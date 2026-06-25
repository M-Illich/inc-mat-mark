/*
Delete/Rederive with Marking
*/

:- use_module(library(chr)).
:- chr_constraint init/1, stream/1,
	read_stream/1, phase/1,
	available_input/1, extract_input/2,
	update/3, stream_end/0,
	fact/4, finish_update/0,
	num_updates/1, current_update/1,
	pending_fact/3,
	marked_facts/2, marked_facts/3, applied_rules/2, 
	applied_rules_list/2, marked_facts_list/2,
	applied_rules_init, marked_facts_init,
	applied_rules_list_init, marked_facts_list_init,
	count_marked_facts,
	check_neg_mark/2, check_pos_mark/2,
	clean/0, print/0.

%:- chr_option(debug, off).
:- chr_option(optimize, off).


% initialization
init(Port) <=> 
	setup_call_cleanup(
		% connect to server 
		tcp_connect(Port, Stream, []),		
		(	stream(Stream),
			num_updates(0),
			current_update(1),
			applied_rules_init,
			applied_rules_list_init,
			marked_facts_init,
			marked_facts_list_init,
			read_stream(infinite),
			% indicate end of procesing
			writeln(Stream,"end"),
			flush_output(Stream),
			print
		),
		close(Stream)
	).		


% -- remove constraints for simpler output --
clean \ fact(_,_,_,_) <=> true.	
clean \ stream(_) <=> true.
clean \ phase(_) <=> true.	


% -- statistical information --
% count number of rule applications for each phase
applied_rules(N,P), applied_rules(M,P) <=>
	K is N + M,
	applied_rules(K,P).

% distinguish between explicit and implicit facts			
	% explicit
marked_facts(N,add,[P|_]) <=> explicit(P) | marked_facts(N,negEx).	
marked_facts(N,del,[P|_]) <=> explicit(P) | marked_facts(N,posEx).	
	% implicit
marked_facts(N,add,_) <=> marked_facts(N,negIm).
marked_facts(N,del,_) <=> marked_facts(N,posIm).

% count number of marked facts
marked_facts(N,O), marked_facts(M,O) <=>
	K is N + M,
	marked_facts(K,O).		

% print out collected statistics
print, applied_rules_list(P,L) ==> writeln(applied_rules(P,L)).
print, marked_facts_list(O,L) ==> writeln(marked_facts(O,L)).


% -- initialize lists to collect number of applied rules and marked facts for each update --
applied_rules_list_init <=>
	applied_rules_list(del,[]),
	applied_rules_list(red,[]),
	applied_rules_list(ins,[]).
marked_facts_list_init <=>
	marked_facts_list(negIm,[]),
	marked_facts_list(negEx,[]),
	marked_facts_list(posIm,[]),
	marked_facts_list(posEx,[]).		
	
% introduce counter for each type of rules
applied_rules_init <=>
	applied_rules(0,del),
	applied_rules(0,red),
	applied_rules(0,ins).	
% introduce counter for each type of marked facts
marked_facts_init <=>
	marked_facts(0,posIm),
	marked_facts(0,posEx),
	marked_facts(0,negIm),		
	marked_facts(0,negEx).		
		

%-------------------------------------------------	
% -- read input from stream --

% stop when stream finished
stream_end \ read_stream(_) <=> true.

% no need to wait when next update already read before
current_update(U), num_updates(U) \ read_stream(infinite) <=>
	read_stream(0.0).

% try to get next input from stream
% note: we use current_update here to ensure that read_stream(infinite) which is added at end of loop does not trigger early
stream(S), current_update(_) \ read_stream(WaitTime) <=> 
	wait_for_input([S],L,WaitTime),
	available_input(L).
	
% no input from stream available
available_input([]) <=> true.

% get input from stream
available_input([S]), num_updates(N) <=>			
	% read added and deleted facts from stream
	read_line_to_string(S,A),
	read_line_to_string(S,D),	
	extract_input(A,D),
	M is N+1,
	num_updates(M).
	

% input indicates end of stream
extract_input("[]","[]") <=>	
	stream_end.

% input is an update
num_updates(N) \ extract_input(X,Y) <=>	
	term_string(A,X),  
	term_string(D,Y),
	update(del,D,N),
	update(add,A,N).	
		
	
% check if next update available after deriving a fact
applied_rules(1,O), num_updates(U), current_update(U) ==> 
	O \== del |
	read_stream(0.0).		


% introduce del-facts of next update once it is current update
% (add-facts are introduced later)
current_update(U) \ pending_fact(F,del,U) <=>
	fact(F,del,_,U).
	

% start processing when every deleted fact has been inserted
current_update(U) \ update(del,[],U) <=> phase(1).
% insert every deleted fact for current update
current_update(U) \ update(del,[F|Fs],U) <=>
	fact(F,del,_,U),
	update(del,Fs,U).

% store del-facts of next update	 for marking
update(del,[F|Fs],U) <=>
	pending_fact(F,del,U),
	update(del,Fs,U).

	
%-----------------
% no duplicates
% save mark if duplicate is marked
fact(F,O,M1,_) \ fact(F,O,M2,_) <=> check_neg_mark([M2],M1).

% mark facts that are deleted by next update
fact(F,_,M,_) \ pending_fact(F,del,_) <=>
	var(M) |
	M = 1.
	

%-------------------------------------------------
% -- deletions --
% remove deleted add-fact
fact(F,del,_,_) \ fact(F,add,_,_) <=> true.


% -- delete every fact that depends on a deleted fact --
phase(1), fact([e, X, Y],O1,M1,_) \ fact([p, X, Y],add,_,U) <=> member(del,[O1]) | check_pos_mark([(e,O1,M1)],M), fact([p, X, Y],del,M,U), applied_rules(1,del).
phase(1), fact([e, X, Y],O1,M1,_), fact([p, Y, Z],O2,M2,_) \ fact([p, X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([(e,O1,M1),(p,O2,M2)],M), fact([p, X, Z],del,M,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact([e, X, Y],add,M1,_) \ fact([p, X, Y],del,_,U) <=> true | check_neg_mark([M1],M), fact([p, X, Y],add,M,U), applied_rules(1,red).
phase(2), fact([e, X, Y],add,M1,_), fact([p, Y, Z],add,M2,_) \ fact([p, X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact([p, X, Z],add,M,U), applied_rules(1,red).
phase(2) <=> phase(3).


% -- remove facts that cannot be rederived --
phase(3) \ fact(_,del,_,_) <=> true.
phase(3) <=> true.


%-------------------------------------------------
% -- insertions --

% finish processing when every new fact has been inserted
current_update(U) \ update(add,[],U) <=> phase(4), finish_update.
% insert every new fact
current_update(U) \ update(add,[F|Fs],U) <=>
	fact(F,add,_,U),
	update(add,Fs,U).
	
% -- compute new derivable facts	--
phase(4), fact([e, X, Y],add,M1,U1) ==> member(U,[U1]) | check_neg_mark([M1],M), fact([p, X, Y],add,M,U), applied_rules(1,ins).
phase(4), fact([e, X, Y],add,M1,U1), fact([p, Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact([p, X, Z],add,M,U), applied_rules(1,ins).

%----------------
% -- write materialization to stream --
finish_update, stream(S), current_update(N) ==> writeln(S, materialization(N)). 	
finish_update, stream(S), fact(F,add,_,_) ==> writeln(S,F).	
finish_update, stream(S) ==> writeln(S,""), flush_output(S).

% -- move on to next update --
% transform marked add-facts into del-facts
finish_update \ fact(F,add,1,U) <=> 
	fact(F,del,_,U),
	marked_facts(1,add,F).
	
% collect numbers of applied rules and marked facts 
finish_update \ applied_rules(N,P), applied_rules_list(P,L) <=>
	append(L,[N],K),
	applied_rules_list(P,K).
count_marked_facts \ marked_facts(N,P), marked_facts_list(P,L) <=>
	append(L,[N],K),
	marked_facts_list(P,K).	
count_marked_facts <=> true.

% start next update's processing
finish_update, phase(4), current_update(U) <=> 
	count_marked_facts,
	applied_rules_init,
	marked_facts_init,
	V is U + 1,
	read_stream(infinite),
	current_update(V).


% -----------------------------
% check if at least one element in list is marked (indicated by 1)
check_neg_mark([],_) <=> true.		
check_neg_mark([1|_],M) <=> M = 1.
check_neg_mark([_|L],M) <=> check_neg_mark(L,M).	

% check if every fact in list is either 
% deleted and marked, or explicit and neither deleted nor marked
check_pos_mark([],M) <=> M = 1.
check_pos_mark([(_,del,1)|L],M) <=> check_pos_mark(L,M).
check_pos_mark([(P,add,M1)|L],M) <=> var(M1), explicit(P) | check_pos_mark(L,M).
check_pos_mark(_,_) <=> true.


% -- predicates for explicit facts --
explicit(e).
