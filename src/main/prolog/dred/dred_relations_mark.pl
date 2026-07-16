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

% store facts of next update for marking
update(O,[F|Fs],U) <=>
	pending_fact(F,O,U),
	update(O,Fs,U).

	
%-----------------
% no duplicates
fact(F,O,_,_) \ fact(F,O,_,_) <=> true.
% save mark if duplicate is marked
%fact(F,add,M1,_) \ fact(F,add,M2,_) <=> check_neg_mark([M2],M1).
%fact([P|L],del,M1,_) \ fact([P|L],del,M2,_) <=> check_pos_mark([(P,del,M2)],M1).

% mark facts that are changed by next update
fact(F,O1,M,_) \ pending_fact(F,O2,_) <=>
	%var(M),
	O1 \== O2 |
	M = 1.
		

%-------------------------------------------------
% -- deletions --
% remove deleted add-fact
fact(F,del,_,_) \ fact(F,add,_,_) <=> true.


% -- delete every fact that depends on a deleted fact --
phase(1), fact(['obo:RO_0003000', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002490', X, Y],O1,M1,_) \ fact(['obo:RO_0002487', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002487', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001020', X, Y],O1,M1,_) \ fact(['obo:RO_0003302', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003302', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002178', X, Y],O1,M1,_) \ fact(['obo:RO_0002170', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002170', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002203', X, Y],O1,M1,_) \ fact(['obo:RO_0002286', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002286', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002372', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X0, X1],O1,M1,_), fact(['obo:RO_0002234', X1, X2],O2,M2,_) \ fact(['obo:RO_0002234', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002230',O1,M1),('obo:RO_0002234',O2,M2)],M), fact(['obo:RO_0002234', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002506', X, _],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002496', X, Y],O1,M1,_) \ fact(['obo:RO_0002487', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002487', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002353', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002256', X, Y],O1,M1,_) \ fact(['obo:RO_0002258', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002258', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002443', X, Y],O1,M1,_) \ fact(['obo:RO_0002440', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002440', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002522', X, Y],O1,M1,_) \ fact(['obo:RO_0002514', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002514', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009501', X0, X1],O1,M1,_), fact(['obo:RO_0002233', X1, X2],O2,M2,_) \ fact(['obo:RO_0004028', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0009501',O1,M1),('obo:RO_0002233',O2,M2)],M), fact(['obo:RO_0004028', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002248', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002295', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011013', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002242', X, Y],O1,M1,_) \ fact(['obo:RO_0002244', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002244', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002595', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002448', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002235', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002212', X, Y],O1,M1,_) \ fact(['obo:RO_0002211', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002211', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002020', X, Y],O1,M1,_) \ fact(['obo:RO_0002313', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002313', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X0, X1],O1,M1,_), fact(['obo:RO_0002212', X1, X2],O2,M2,_) \ fact(['obo:RO_0002212', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002230',O1,M1),('obo:RO_0002212',O2,M2)],M), fact(['obo:RO_0002212', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002110', X, Y],O1,M1,_) \ fact(['obo:RO_0002130', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002130', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002134', X, _],O1,M1,_) \ fact(['obo:CARO_0001001', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001001', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002009', X, _],O1,M1,_) \ fact(['obo:CL_0000000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002017', X, Y],O1,M1,_) \ fact(['obo:RO_0002018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002101', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002104', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002179', X, X1],O1,M1,_), fact(['obo:CARO_0000006', X],O2,M2,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002179',O1,M1),('obo:CARO_0000006',O2,M2)],M), fact(['obo:CARO_0000003', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002233', X, X2],O1,M1,_), fact(['obo:RO_0002025', X, X1],O2,M2,_) \ fact(['obo:RO_0002233', X1, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002233',O1,M1),('obo:RO_0002025',O2,M2)],M), fact(['obo:RO_0002233', X1, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002459', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002004', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002326', X, Y],O1,M1,_) \ fact(['obo:RO_0002329', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002329', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:RO_0002497', X1, X2],O2,M2,_) \ fact(['obo:RO_0002497', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:RO_0002497',O2,M2)],M), fact(['obo:RO_0002497', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002578', X0, X1],O1,M1,_), fact(['obo:RO_0002578', X1, X2],O2,M2,_) \ fact(['obo:RO_0002211', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002578',O1,M1),('obo:RO_0002578',O2,M2)],M), fact(['obo:RO_0002211', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002622', X, Y],O1,M1,_) \ fact(['obo:RO_0002618', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002618', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002224', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002331', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002331', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002331',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002331', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002576', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002400', X, Y],O1,M1,_) \ fact(['obo:RO_0002233', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002233', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004000', X, _],O1,M1,_) \ fact(['obo:BFO_0000017', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000017', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002518', X, Y],O1,M1,_) \ fact(['obo:RO_0002524', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002524', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002206', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002206',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X0, X1],O1,M1,_), fact(['obo:RO_0002224', X1, X2],O2,M2,_) \ fact(['obo:RO_0002090', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002230',O1,M1),('obo:RO_0002224',O2,M2)],M), fact(['obo:RO_0002090', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003301', X, Y],O1,M1,_), fact(['obo:RO_0003301', Y, X],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0003301',O1,M1),('obo:RO_0003301',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002015', X, Y],O1,M1,_) \ fact(['obo:RO_0002336', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002336', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002134', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002134', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002134',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002134', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000052', X, Y],O1,M1,_) \ fact(['obo:RO_0002314', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002314', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009003', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002427', Y, X],O1,M1,_) \ fact(['obo:RO_0002418', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002418', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002418', Y, X],O1,M1,_) \ fact(['obo:RO_0002427', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002427', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002225', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002225',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002461', X0, X1],O1,M1,_), fact(['obo:RO_0002466', X1, X2],O2,M2,_), fact(['obo:RO_0002461', X3, X2],O3,M3,_) \ fact(['obo:RO_0002441', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002461',O1,M1),('obo:RO_0002466',O2,M2),('obo:RO_0002461',O3,M3)],M), fact(['obo:RO_0002441', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002641', Y, X],O1,M1,_) \ fact(['obo:RO_0002640', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002640', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002640', Y, X],O1,M1,_) \ fact(['obo:RO_0002641', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002641', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002211', X, Y],O1,M1,_), fact(['obo:RO_0002211', Y, Z],O2,M2,_) \ fact(['obo:RO_0002211', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002211',O1,M1),('obo:RO_0002211',O2,M2)],M), fact(['obo:RO_0002211', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002163', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009501', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002495', X, Y],O1,M1,_) \ fact(['obo:RO_0002494', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002494', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003304', X, Y],O1,M1,_) \ fact(['obo:RO_0003302', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003302', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002380', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002332', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002506', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002213', X, Y],O1,M1,_), fact(['obo:RO_0002213', Y, Z],O2,M2,_) \ fact(['obo:RO_0002213', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002213',O1,M1),('obo:RO_0002213',O2,M2)],M), fact(['obo:RO_0002213', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002355', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002413', X, Y],O1,M1,_) \ fact(['obo:RO_0002414', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002414', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004003', X, Y],O1,M1,_) \ fact(['obo:RO_0004000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002334', Y, X],O1,M1,_) \ fact(['obo:RO_0002211', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002211', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002211', Y, X],O1,M1,_) \ fact(['obo:RO_0002334', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002334', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002159', Y, X],O1,M1,_) \ fact(['obo:RO_0002159', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002159', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0085030', X],O1,M1,_) \ fact(['obo:RO_0002467', X, X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002467', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002156', X0, X1],O1,M1,_), fact(['obo:RO_0002157', X1, X2],O2,M2,_) \ fact(['obo:RO_0002158', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002156',O1,M1),('obo:RO_0002157',O2,M2)],M), fact(['obo:RO_0002158', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002303', X, Y],O1,M1,_) \ fact(['obo:RO_0002321', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002321', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011015', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003002', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002432', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002569', X, Y],O1,M1,_) \ fact(['obo:RO_0002375', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002375', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002212', X1, X2],O2,M2,_) \ fact(['obo:RO_0002430', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002212',O2,M2)],M), fact(['obo:RO_0002430', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002496', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002496', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002496',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002496', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002496', X, Y],O1,M1,_), fact(['obo:RO_NonExist', X],O2,M2,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002496',O1,M1),('obo:RO_NonExist',O2,M2)],M), fact(['obo:BFO_0000050', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002131', X, Y],O1,M1,_), fact(['obo:RO_NonExist', X],O2,M2,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002131',O1,M1),('obo:RO_NonExist',O2,M2)],M), fact(['obo:BFO_0000050', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002162', X, Y],O1,M1,_), fact(['obo:RO_NonExist', X],O2,M2,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002162',O1,M1),('obo:RO_NonExist',O2,M2)],M), fact(['obo:BFO_0000050', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002315', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002382', X, Y],O1,M1,_) \ fact(['obo:RO_0002377', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002377', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002507', X, Y],O1,M1,_) \ fact(['obo:RO_0002559', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002559', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0001025', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0001025',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0001025', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002314', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002314', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002314',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002314', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002224', X0, X1],O1,M1,_), fact(['obo:RO_0002233', X1, X2],O2,M2,_) \ fact(['obo:RO_0002233', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002224',O1,M1),('obo:RO_0002233',O2,M2)],M), fact(['obo:RO_0002233', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002336', Y, X],O1,M1,_) \ fact(['obo:RO_0002213', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002213', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002213', Y, X],O1,M1,_) \ fact(['obo:RO_0002336', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002336', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002583', X, Y],O1,M1,_) \ fact(['obo:RO_0002496', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002496', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002371', X, Y],O1,M1,_) \ fact(['obo:RO_0002177', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002177', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002449', X, Y],O1,M1,_) \ fact(['obo:RO_0002448', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002448', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002567', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004009', X, Y],O1,M1,_) \ fact(['obo:RO_0002233', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002233', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002092', X0, X1],O1,M1,_), fact(['obo:BFO_0000063', X1, X2],O2,M2,_) \ fact(['obo:BFO_0000063', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002092',O1,M1),('obo:BFO_0000063',O2,M2)],M), fact(['obo:BFO_0000063', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002460', Y, X],O1,M1,_) \ fact(['obo:RO_0002459', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002459', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002459', Y, X],O1,M1,_) \ fact(['obo:RO_0002460', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002460', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002158', Y, X],O1,M1,_) \ fact(['obo:RO_0002158', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002158', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002606', X, Y],O1,M1,_) \ fact(['obo:RO_0002599', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002599', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002335', Y, X],O1,M1,_) \ fact(['obo:RO_0002212', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002212', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002212', Y, X],O1,M1,_) \ fact(['obo:RO_0002335', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002335', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002201', X, Y],O1,M1,_) \ fact(['owl:topObjectProperty', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:topObjectProperty', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002292', X, Y],O1,M1,_) \ fact(['obo:RO_0002330', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002330', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002574', _, X1],O1,M1,_) \ fact(['obo:CARO_0001010', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002593', X0, X1],O1,M1,_), fact(['obo:BFO_0000063', X1, X2],O2,M2,_), fact(['obo:RO_0002593', X3, X2],O3,M3,_) \ fact(['obo:RO_0002497', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002593',O1,M1),('obo:BFO_0000063',O2,M2),('obo:RO_0002593',O3,M3)],M), fact(['obo:RO_0002497', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002413', X, Y],O1,M1,_) \ fact(['obo:RO_0002412', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002412', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002404', X, Y],O1,M1,_) \ fact(['obo:BFO_0000062', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000062', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002590', X, Y],O1,M1,_) \ fact(['obo:RO_0002592', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002592', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002100', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002100', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002100',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002100', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002214', X, X1],O1,M1,_), fact(['obo:BFO_0000015', X],O2,M2,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002214',O1,M1),('obo:BFO_0000015',O2,M2)],M), fact(['obo:BFO_0000015', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002600', X, Y],O1,M1,_) \ fact(['obo:RO_0002598', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002598', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002481', X, Y],O1,M1,_) \ fact(['obo:RO_0002564', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002564', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008501', X, Y],O1,M1,_) \ fact(['obo:RO_0002440', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002440', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001019', Y, X],O1,M1,_) \ fact(['obo:RO_0001018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001018', Y, X],O1,M1,_) \ fact(['obo:RO_0001019', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001019', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002007', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002525', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002309', X, Y],O1,M1,_) \ fact(['obo:RO_0002244', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002244', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002313', X0, X1],O1,M1,_), fact(['obo:BFO_0000051', X1, X2],O2,M2,_) \ fact(['obo:RO_0002313', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002313',O1,M1),('obo:BFO_0000051',O2,M2)],M), fact(['obo:RO_0002313', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002348', _, X1],O1,M1,_) \ fact(['obo:CL_0000000', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000000', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004009', X, Y],O1,M1,_) \ fact(['obo:RO_0004007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002479', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002449', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X0, X1],O1,M1,_), fact(['obo:BFO_0000055', X1, X2],O2,M2,_), fact(['obo:RO_0000052', X2, X3],O3,M3,_) \ fact(['obo:RO_0000057', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:BFO_0000055',O2,M2),('obo:RO_0000052',O3,M3)],M), fact(['obo:RO_0000057', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002373', X, Y],O1,M1,_) \ fact(['obo:RO_0002371', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002371', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002531', X, Y],O1,M1,_) \ fact(['obo:RO_0002515', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002515', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002495', X, Y],O1,M1,_) \ fact(['obo:RO_0002207', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002207', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002387', X, Y],O1,M1,_) \ fact(['obo:RO_0002384', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002384', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002587', X, Y],O1,M1,_) \ fact(['obo:RO_0002297', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002297', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002286', Y, X],O1,M1,_) \ fact(['obo:RO_0002258', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002258', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002258', Y, X],O1,M1,_) \ fact(['obo:RO_0002286', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002286', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002633', X, Y],O1,M1,_) \ fact(['obo:RO_0002445', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002445', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002435', X, Y],O1,M1,_) \ fact(['obo:RO_0002434', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002434', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002100', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002586', X, Y],O1,M1,_) \ fact(['obo:RO_0002233', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002233', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002593', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002492', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002593',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002492', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004023', X, Y],O1,M1,_) \ fact(['obo:RO_0040035', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040035', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011024', X, Y],O1,M1,_) \ fact(['obo:RO_0011022', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011022', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002408', X0, X1],O1,M1,_), fact(['obo:RO_0002408', X1, X2],O2,M2,_) \ fact(['obo:RO_0002409', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002408',O1,M1),('obo:RO_0002408',O2,M2)],M), fact(['obo:RO_0002409', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002371', X, Y],O1,M1,_) \ fact(['obo:RO_0002170', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002170', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004029', X, Y],O1,M1,_) \ fact(['obo:RO_0040035', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040035', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002434', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002206', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002206', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002206',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002206', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002418', X1, X2],O2,M2,_) \ fact(['obo:RO_0002264', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002418',O2,M2)],M), fact(['obo:RO_0002264', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004020', X, Y],O1,M1,_) \ fact(['obo:RO_0004019', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004019', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002501', _, X1],O1,M1,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002334', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002624', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002530', X, Y],O1,M1,_) \ fact(['obo:RO_0002529', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002529', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:BFO_0000066', X1, X2],O2,M2,_) \ fact(['obo:RO_0002432', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:BFO_0000066',O2,M2)],M), fact(['obo:RO_0002432', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002202', X, Y],O1,M1,_), fact(['obo:RO_0002202', Y, Z],O2,M2,_) \ fact(['obo:RO_0002202', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002202',O1,M1),('obo:RO_0002202',O2,M2)],M), fact(['obo:RO_0002202', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008508', Y, X],O1,M1,_) \ fact(['obo:RO_0008507', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0008507', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008507', Y, X],O1,M1,_) \ fact(['obo:RO_0008508', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0008508', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002214', X, X1],O1,M1,_), fact(['obo:BFO_0000002', X],O2,M2,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002214',O1,M1),('obo:BFO_0000002',O2,M2)],M), fact(['obo:BFO_0000002', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002606', Y, X],O1,M1,_) \ fact(['obo:RO_0002302', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002302', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002302', Y, X],O1,M1,_) \ fact(['obo:RO_0002606', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002606', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002437', X, Y],O1,M1,_) \ fact(['obo:RO_0002321', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002321', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002426', X, Y],O1,M1,_) \ fact(['obo:RO_0002424', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002424', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002203', X, Y],O1,M1,_), fact(['obo:RO_0002203', Y, Z],O2,M2,_) \ fact(['obo:RO_0002203', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002203',O1,M1),('obo:RO_0002203',O2,M2)],M), fact(['obo:RO_0002203', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002107', X, Y],O1,M1,_) \ fact(['obo:RO_0002120', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002120', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002412', X, Y],O1,M1,_) \ fact(['obo:RO_0002411', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002411', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002578', X, Y],O1,M1,_) \ fact(['obo:RO_0002211', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002211', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002414', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002132', Y, X],O1,M1,_) \ fact(['obo:RO_0002101', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002101', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002101', Y, X],O1,M1,_) \ fact(['obo:RO_0002132', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002132', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002371', Y, X],O1,M1,_) \ fact(['obo:RO_0002371', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002371', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002551', X, Y],O1,M1,_), fact(['obo:RO_0002551', Y, X],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002551',O1,M1),('obo:RO_0002551',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002530', X, Y],O1,M1,_) \ fact(['obo:RO_0002515', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002515', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002427', X, Y],O1,M1,_), fact(['obo:RO_0002427', Y, Z],O2,M2,_) \ fact(['obo:RO_0002427', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002427',O1,M1),('obo:RO_0002427',O2,M2)],M), fact(['obo:RO_0002427', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002411', X1, X2],O2,M2,_), fact(['obo:RO_0002233', X2, X3],O3,M3,_) \ fact(['obo:RO_0002566', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002411',O2,M2),('obo:RO_0002233',O3,M3)],M), fact(['obo:RO_0002566', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004021', X, Y],O1,M1,_) \ fact(['obo:RO_0004019', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004019', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002576', Y, X],O1,M1,_) \ fact(['obo:RO_0002551', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002551', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002551', Y, X],O1,M1,_) \ fact(['obo:RO_0002576', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002576', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003001', Y, X],O1,M1,_) \ fact(['obo:RO_0003000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003000', Y, X],O1,M1,_) \ fact(['obo:RO_0003001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008506', Y, X],O1,M1,_) \ fact(['obo:RO_0008506', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0008506', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009002', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002527', Y, X],O1,M1,_) \ fact(['obo:RO_0002527', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002527', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002407', X, Y],O1,M1,_) \ fact(['obo:RO_0002213', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002213', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002511', X0, X1],O1,M1,_), fact(['obo:RO_0002513', X1, X2],O2,M2,_) \ fact(['obo:RO_0002205', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002511',O1,M1),('obo:RO_0002513',O2,M2)],M), fact(['obo:RO_0002205', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002632', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002372', X, Y],O1,M1,_) \ fact(['obo:RO_0002371', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002371', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002386', X, Y],O1,M1,_) \ fact(['obo:RO_0002384', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002384', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0085031', X],O1,M1,_) \ fact(['obo:RO_0002466', X, X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002466', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002526', Y, X],O1,M1,_) \ fact(['obo:RO_0002526', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002526', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000000', X, X1],O1,M1,_), fact(['obo:BFO_0000002', X],O2,M2,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000000',O1,M1),('obo:BFO_0000002',O2,M2)],M), fact(['obo:BFO_0000002', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004025', X0, X1],O1,M1,_), fact(['obo:RO_0002215', X1, X2],O2,M2,_) \ fact(['obo:RO_0004024', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0004025',O1,M1),('obo:RO_0002215',O2,M2)],M), fact(['obo:RO_0004024', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002104', X, _],O1,M1,_) \ fact(['obo:CARO_0000006', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000006', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002301', X, Y],O1,M1,_) \ fact(['obo:RO_0002552', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002552', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002494', X, Y],O1,M1,_) \ fact(['obo:RO_0002202', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002202', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002521', X, Y],O1,M1,_) \ fact(['obo:RO_0002514', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002514', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002527', X, Y],O1,M1,_) \ fact(['obo:RO_0002514', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002514', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004030', X, Y],O1,M1,_) \ fact(['obo:RO_0004019', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004019', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002100', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011014', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002405', X, Y],O1,M1,_) \ fact(['obo:RO_0002087', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002087', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002016', X, Y],O1,M1,_) \ fact(['obo:RO_0002017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002010', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002411', X1, X2],O2,M2,_) \ fact(['obo:RO_0002263', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002411',O2,M2)],M), fact(['obo:RO_0002263', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004026', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X0, X1],O1,M1,_), fact(['obo:RO_0000057', X1, X2],O2,M2,_) \ fact(['obo:RO_0000057', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:RO_0000057',O2,M2)],M), fact(['obo:RO_0000057', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002330', _, X1],O1,M1,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002566', X, _],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008506', X, _],O1,M1,_) \ fact(['obo:CARO_0001010', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002200', X, Y],O1,M1,_) \ fact(['owl:topObjectProperty', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:topObjectProperty', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002567', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002478', X, Y],O1,M1,_) \ fact(['obo:RO_0002476', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002476', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002025', X, Y],O1,M1,_) \ fact(['obo:RO_0002017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002576', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002352', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002442', X, Y],O1,M1,_) \ fact(['obo:RO_0002440', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002440', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002009', X, Y],O1,M1,_) \ fact(['obo:RO_0002292', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002292', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002245', X, Y],O1,M1,_) \ fact(['obo:RO_0002206', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002206', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002333', X, Y],O1,M1,_) \ fact(['obo:RO_0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002109', X, Y],O1,M1,_) \ fact(['obo:RO_0002103', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002103', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002524', X0, X1],O1,M1,_), fact(['obo:RO_0002525', X1, X2],O2,M2,_) \ fact(['obo:RO_0002526', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002524',O1,M1),('obo:RO_0002525',O2,M2)],M), fact(['obo:RO_0002526', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002553', X, Y],O1,M1,_) \ fact(['obo:RO_0002454', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002454', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002470', X, Y],O1,M1,_) \ fact(['obo:RO_0002438', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002438', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002252', X, Y],O1,M1,_) \ fact(['obo:RO_0002375', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002375', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0016301', X],O1,M1,_) \ fact(['obo:RO_0002481', X, X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002481', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002232', X, Y],O1,M1,_) \ fact(['obo:RO_0002479', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002479', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004024', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0004024', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0004024',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0004024', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008502', Y, X],O1,M1,_) \ fact(['obo:RO_0008501', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0008501', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008501', Y, X],O1,M1,_) \ fact(['obo:RO_0008502', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0008502', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X0, X1],O1,M1,_), fact(['obo:RO_0002213', X1, X2],O2,M2,_) \ fact(['obo:RO_0002598', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002215',O1,M1),('obo:RO_0002213',O2,M2)],M), fact(['obo:RO_0002598', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002342', X, Y],O1,M1,_) \ fact(['obo:RO_0002344', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002344', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002231', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002211', X0, X1],O1,M1,_), fact(['obo:RO_0002313', X1, X2],O2,M2,_) \ fact(['obo:RO_0002011', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002211',O1,M1),('obo:RO_0002313',O2,M2)],M), fact(['obo:RO_0002011', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002205', X, Y],O1,M1,_) \ fact(['obo:RO_0002330', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002330', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002208', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003309', X, Y],O1,M1,_) \ fact(['obo:RO_0003305', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003305', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002203', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002255', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002203',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002255', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004034', X, Y],O1,M1,_) \ fact(['obo:RO_0002263', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002263', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008504', Y, X],O1,M1,_) \ fact(['obo:RO_0008503', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0008503', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008503', Y, X],O1,M1,_) \ fact(['obo:RO_0008504', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0008504', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002112', X, Y],O1,M1,_) \ fact(['obo:RO_0002103', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002103', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002378', X, Y],O1,M1,_), fact(['obo:RO_0002382', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002378',O1,M1),('obo:RO_0002382',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002590', X, Y],O1,M1,_) \ fact(['obo:RO_0002586', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002586', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002445', X0, X1],O1,M1,_), fact(['obo:RO_0002445', X1, X2],O2,M2,_) \ fact(['obo:RO_0002554', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002445',O1,M1),('obo:RO_0002445',O2,M2)],M), fact(['obo:RO_0002554', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002378', X, Y],O1,M1,_), fact(['obo:RO_0002383', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002378',O1,M1),('obo:RO_0002383',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002456', Y, X],O1,M1,_) \ fact(['obo:RO_0002455', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002455', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002455', Y, X],O1,M1,_) \ fact(['obo:RO_0002456', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002456', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004034', X, Y],O1,M1,_) \ fact(['obo:RO_0004032', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004032', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002551', _, X1],O1,M1,_) \ fact(['obo:CARO_0000006', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000006', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002102', X, Y],O1,M1,_) \ fact(['obo:RO_0002113', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002113', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002431', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002573', X, _],O1,M1,_) \ fact(['obo:BFO_0000020', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002521', Y, X],O1,M1,_) \ fact(['obo:RO_0002521', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002521', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002339', X, Y],O1,M1,_) \ fact(['obo:RO_0002344', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002344', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002584', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003303', X, Y],O1,M1,_) \ fact(['obo:RO_0003302', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003302', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002558', X, Y],O1,M1,_) \ fact(['obo:RO_0002616', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002616', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002505', X, Y],O1,M1,_) \ fact(['obo:RO_0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002458', X, Y],O1,M1,_) \ fact(['obo:RO_0002438', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002438', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004012', X, Y],O1,M1,_) \ fact(['obo:RO_0004010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002494', X, Y],O1,M1,_), fact(['obo:RO_0002494', Y, Z],O2,M2,_) \ fact(['obo:RO_0002494', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002494',O1,M1),('obo:RO_0002494',O2,M2)],M), fact(['obo:RO_0002494', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002205', X, _],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002608', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X0, X1],O1,M1,_), fact(['obo:RO_0002481', X1, X2],O2,M2,_), fact(['obo:RO_0002400', X2, X3],O3,M3,_) \ fact(['obo:RO_0002447', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002215',O1,M1),('obo:RO_0002481',O2,M2),('obo:RO_0002400',O3,M3)],M), fact(['obo:RO_0002447', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002487', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003001', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002378', X, Y],O1,M1,_) \ fact(['obo:RO_0002377', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002377', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002257', X, Y],O1,M1,_) \ fact(['obo:RO_0002386', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002386', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002151', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004007', X, Y],O1,M1,_) \ fact(['obo:RO_0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002381', X, Y],O1,M1,_) \ fact(['obo:RO_0002375', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002375', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004004', X, Y],O1,M1,_) \ fact(['obo:RO_0004000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000003', X, Y],O1,M1,_) \ fact(['obo:RO_0002320', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002320', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002213', X2, X],O1,M1,_), fact(['obo:RO_0002212', X, X1],O2,M2,_) \ fact(['obo:RO_0002212', X2, X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002213',O1,M1),('obo:RO_0002212',O2,M2)],M), fact(['obo:RO_0002212', X2, X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002212', X, X1],O1,M1,_), fact(['obo:RO_0002213', X1, X2],O2,M2,_) \ fact(['obo:RO_0002212', X, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002212',O1,M1),('obo:RO_0002213',O2,M2)],M), fact(['obo:RO_0002212', X, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002085', X, Y],O1,M1,_) \ fact(['obo:RO_0002088', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002088', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002555', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002157', Y, X],O1,M1,_) \ fact(['obo:RO_0002156', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002156', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002156', Y, X],O1,M1,_) \ fact(['obo:RO_0002157', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002157', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011004', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002457', X, Y],O1,M1,_) \ fact(['obo:RO_0002438', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002438', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002120', Y, X],O1,M1,_) \ fact(['obo:RO_0002103', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002103', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002103', Y, X],O1,M1,_) \ fact(['obo:RO_0002120', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002120', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002629', X, Y],O1,M1,_) \ fact(['obo:RO_0002213', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002213', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0010001', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002293', X, Y],O1,M1,_) \ fact(['obo:RO_0002292', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002292', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002524', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002487', _, X1],O1,M1,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002497', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002497', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002497',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002497', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002017', X1, X2],O2,M2,_) \ fact(['obo:RO_0002327', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002017',O2,M2)],M), fact(['obo:RO_0002327', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002635', Y, X],O1,M1,_) \ fact(['obo:RO_0002634', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002634', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002634', Y, X],O1,M1,_) \ fact(['obo:RO_0002635', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002635', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000052', X0, X1],O1,M1,_), fact(['obo:RO_0000058', X1, X2],O2,M2,_) \ fact(['obo:RO_0010001', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0000052',O1,M1),('obo:RO_0000058',O2,M2)],M), fact(['obo:RO_0010001', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002157', X, Y],O1,M1,_), fact(['obo:RO_0002157', Y, Z],O2,M2,_) \ fact(['obo:RO_0002157', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002157',O1,M1),('obo:RO_0002157',O2,M2)],M), fact(['obo:RO_0002157', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002331', X, Y],O1,M1,_) \ fact(['obo:RO_0002431', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002431', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004035', X, Y],O1,M1,_) \ fact(['obo:RO_0004033', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004033', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002202', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002202',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004030', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002156', X, Y],O1,M1,_), fact(['obo:RO_0002156', Y, Z],O2,M2,_) \ fact(['obo:RO_0002156', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002156',O1,M1),('obo:RO_0002156',O2,M2)],M), fact(['obo:RO_0002156', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001023', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002380', X, Y],O1,M1,_) \ fact(['obo:RO_0002375', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002375', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002299', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002523', Y, X],O1,M1,_) \ fact(['obo:RO_0002522', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002522', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002522', Y, X],O1,M1,_) \ fact(['obo:RO_0002523', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002523', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002506', _, X1],O1,M1,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003000', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002551', X, X],O1,M1,_) \ fact(['owl:Nothing', X, X],add,_,U) <=> member(del,[O1]) | fact(['owl:Nothing', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002108', X, Y],O1,M1,_) \ fact(['obo:RO_0002103', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002103', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002231', X, Y],O1,M1,_) \ fact(['obo:RO_0002479', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002479', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004005', X, Y],O1,M1,_) \ fact(['obo:RO_0004000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004027', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002448', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004013', X, Y],O1,M1,_) \ fact(['obo:RO_0004010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002338', X, Y],O1,M1,_) \ fact(['obo:RO_0002344', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002344', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002411', X, Y],O1,M1,_) \ fact(['obo:RO_0002418', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002418', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X2, X],O1,M1,_), fact(['obo:BFO_0000051', X, X1],O2,M2,_), fact(['obo:GO_0003674', X],O3,M3,_) \ fact(['obo:RO_0002327', X2, X1],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:BFO_0000051',O2,M2),('obo:GO_0003674',O3,M3)],M), fact(['obo:RO_0002327', X2, X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002572', X, Y],O1,M1,_) \ fact(['obo:RO_0002571', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002571', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002637', Y, X],O1,M1,_) \ fact(['obo:RO_0002636', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002636', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002636', Y, X],O1,M1,_) \ fact(['obo:RO_0002637', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002637', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002132', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002425', X, Y],O1,M1,_) \ fact(['obo:RO_0002424', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002424', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002473', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009003', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002214', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002214',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002377', X, Y],O1,M1,_) \ fact(['obo:RO_0002375', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002375', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002583', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002488', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002583',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002488', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002450', X, Y],O1,M1,_) \ fact(['obo:RO_0002448', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002448', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011014', X, Y],O1,M1,_) \ fact(['obo:RO_0011010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002295', X, _],O1,M1,_) \ fact(['obo:GO_0008150', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0008150', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002574', X, _],O1,M1,_) \ fact(['obo:CARO_0001010', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004027', X, Y],O1,M1,_) \ fact(['obo:RO_0004026', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004026', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002310', X],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002211', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002439', X, Y],O1,M1,_) \ fact(['obo:RO_0002438', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002438', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002110', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002110', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002110',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002110', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002512', X0, X1],O1,M1,_), fact(['obo:RO_0002510', X1, X2],O2,M2,_) \ fact(['obo:RO_0002204', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002512',O1,M1),('obo:RO_0002510',O2,M2)],M), fact(['obo:RO_0002204', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002448', X, Y],O1,M1,_) \ fact(['obo:RO_0002436', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002436', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004021', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002509', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002385', X, Y],O1,M1,_) \ fact(['obo:RO_0002384', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002384', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002461', X, Y],O1,M1,_) \ fact(['obo:RO_0000056', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000056', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:BFO_0000051', X1, X2],O2,M2,_) \ fact(['obo:RO_0004031', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:BFO_0000051',O2,M2)],M), fact(['obo:RO_0004031', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002585', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002158', X, Y],O1,M1,_), fact(['obo:RO_0002158', Y, Z],O2,M2,_) \ fact(['obo:RO_0002158', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002158',O1,M1),('obo:RO_0002158',O2,M2)],M), fact(['obo:RO_0002158', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002633', Y, X],O1,M1,_) \ fact(['obo:RO_0002632', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002632', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002632', Y, X],O1,M1,_) \ fact(['obo:RO_0002633', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002633', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002402', X0, X1],O1,M1,_), fact(['obo:RO_0002400', X1, X2],O2,M2,_) \ fact(['obo:RO_0002413', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002402',O1,M1),('obo:RO_0002400',O2,M2)],M), fact(['obo:RO_0002413', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004019', X, Y],O1,M1,_) \ fact(['obo:RO_0004017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002592', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002159', X, Y],O1,M1,_), fact(['obo:RO_0002159', Y, Z],O2,M2,_) \ fact(['obo:RO_0002159', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002159',O1,M1),('obo:RO_0002159',O2,M2)],M), fact(['obo:RO_0002159', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002571', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002637', X, Y],O1,M1,_) \ fact(['obo:RO_0002445', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002445', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002384', _, X1],O1,M1,_) \ fact(['obo:CARO_0000000', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000000', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011003', X, Y],O1,M1,_) \ fact(['obo:RO_0002566', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002566', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002524', X, Y],O1,M1,_), fact(['obo:RO_0002524', Y, Z],O2,M2,_) \ fact(['obo:RO_0002524', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002524',O1,M1),('obo:RO_0002524',O2,M2)],M), fact(['obo:RO_0002524', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002629', X, X2],O1,M1,_), fact(['obo:RO_0002025', X, X1],O2,M2,_) \ fact(['obo:RO_0002629', X1, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002629',O1,M1),('obo:RO_0002025',O2,M2)],M), fact(['obo:RO_0002629', X1, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0004046', X1, X2],O2,M2,_) \ fact(['obo:RO_0004033', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0004046',O2,M2)],M), fact(['obo:RO_0004033', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002218', X, Y],O1,M1,_) \ fact(['obo:RO_0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002523', X, Y],O1,M1,_), fact(['obo:RO_0002523', Y, Z],O2,M2,_) \ fact(['obo:RO_0002523', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002523',O1,M1),('obo:RO_0002523',O2,M2)],M), fact(['obo:RO_0002523', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004017', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X0, X1],O1,M1,_), fact(['obo:RO_0002213', X1, X2],O2,M2,_) \ fact(['obo:RO_0002213', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002230',O1,M1),('obo:RO_0002213',O2,M2)],M), fact(['obo:RO_0002213', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002018', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002492', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002492', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002492',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002492', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002517', X, Y],O1,M1,_) \ fact(['obo:RO_0002525', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002525', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002001', X, Y],O1,M1,_), fact(['obo:RO_0002001', Y, Z],O2,M2,_) \ fact(['obo:RO_0002001', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002001',O1,M1),('obo:RO_0002001',O2,M2)],M), fact(['obo:RO_0002001', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002212', X0, X1],O1,M1,_), fact(['obo:RO_0002212', X1, X2],O2,M2,_) \ fact(['obo:RO_0002213', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002212',O1,M1),('obo:RO_0002212',O2,M2)],M), fact(['obo:RO_0002213', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002520', X, Y],O1,M1,_) \ fact(['obo:RO_0002524', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002524', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002314', X, Y],O1,M1,_) \ fact(['obo:RO_0002502', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002502', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002525', X, Y],O1,M1,_), fact(['obo:RO_0002525', Y, Z],O2,M2,_) \ fact(['obo:RO_0002525', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002525',O1,M1),('obo:RO_0002525',O2,M2)],M), fact(['obo:RO_0002525', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002583', X0, X1],O1,M1,_), fact(['obo:BFO_0000062', X1, X2],O2,M2,_), fact(['obo:RO_0002583', X3, X2],O3,M3,_) \ fact(['obo:RO_0002496', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002583',O1,M1),('obo:BFO_0000062',O2,M2),('obo:RO_0002583',O3,M3)],M), fact(['obo:RO_0002496', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002379', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002177', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002226', X, _],O1,M1,_) \ fact(['obo:CARO_0000000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002305', X, Y],O1,M1,_) \ fact(['obo:RO_0004046', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004046', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X2, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X],O2,M2,_), fact(['obo:GO_0008150', X],O3,M3,_) \ fact(['obo:RO_0002331', X2, X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:BFO_0000050',O2,M2),('obo:GO_0008150',O3,M3)],M), fact(['obo:RO_0002331', X2, X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002331', X0, X1],O1,M1,_), fact(['obo:RO_0002211', X1, X2],O2,M2,_) \ fact(['obo:RO_0002428', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002331',O1,M1),('obo:RO_0002211',O2,M2)],M), fact(['obo:RO_0002428', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002522', X, Y],O1,M1,_), fact(['obo:RO_0002522', Y, Z],O2,M2,_) \ fact(['obo:RO_0002522', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002522',O1,M1),('obo:RO_0002522',O2,M2)],M), fact(['obo:RO_0002522', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011015', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004027', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002529', Y, X],O1,M1,_) \ fact(['obo:RO_0002529', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002529', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002529', Y, X],O1,M1,_) \ fact(['obo:RO_0002529', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002529', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002204', X, Y],O1,M1,_) \ fact(['obo:RO_0002330', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002330', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002525', Y, X],O1,M1,_) \ fact(['obo:RO_0002524', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002524', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002524', Y, X],O1,M1,_) \ fact(['obo:RO_0002525', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002525', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002639', Y, X],O1,M1,_) \ fact(['obo:RO_0002638', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002638', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002638', Y, X],O1,M1,_) \ fact(['obo:RO_0002639', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002639', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002343', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002159', X, Y],O1,M1,_) \ fact(['obo:RO_0002320', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002320', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002315', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002004', X, Y],O1,M1,_) \ fact(['obo:RO_0001018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002578', Y, X],O1,M1,_) \ fact(['obo:RO_0002022', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002022', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002022', Y, X],O1,M1,_) \ fact(['obo:RO_0002578', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002578', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002295', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002295',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002437', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002115', Y, X],O1,M1,_) \ fact(['obo:RO_0002114', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002114', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002114', Y, X],O1,M1,_) \ fact(['obo:RO_0002115', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002115', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002596', X, Y],O1,M1,_) \ fact(['obo:RO_0002500', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002500', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0044403', X],O1,M1,_) \ fact(['obo:RO_0002465', X, X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002465', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011015', X, Y],O1,M1,_) \ fact(['obo:RO_0011009', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011009', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002461', X0, X1],O1,M1,_), fact(['obo:RO_0002467', X1, X2],O2,M2,_), fact(['obo:RO_0002461', X3, X2],O3,M3,_) \ fact(['obo:RO_0002442', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002461',O1,M1),('obo:RO_0002467',O2,M2),('obo:RO_0002461',O3,M3)],M), fact(['obo:RO_0002442', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002337', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002162', X, Y],O1,M1,_) \ fact(['obo:RO_0002320', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002320', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002000', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002263', X, Y],O1,M1,_) \ fact(['obo:RO_0002264', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002264', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002528', X, Y],O1,M1,_), fact(['obo:RO_0002528', Y, Z],O2,M2,_) \ fact(['obo:RO_0002528', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002528',O1,M1),('obo:RO_0002528',O2,M2)],M), fact(['obo:RO_0002528', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002444', X0, X1],O1,M1,_), fact(['obo:RO_0002444', X1, X2],O2,M2,_) \ fact(['obo:RO_0002553', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002444',O1,M1),('obo:RO_0002444',O2,M2)],M), fact(['obo:RO_0002553', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:RO_0002496', X1, X2],O2,M2,_) \ fact(['obo:RO_0002496', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:RO_0002496',O2,M2)],M), fact(['obo:RO_0002496', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002200', _, X1],O1,M1,_) \ fact(['obo:UPHENO_0001001', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:UPHENO_0001001', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002564', X, Y],O1,M1,_) \ fact(['obo:RO_0002563', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002563', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002024', X, Y],O1,M1,_) \ fact(['obo:RO_0002022', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002022', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002566', Y, X],O1,M1,_) \ fact(['obo:RO_0002559', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002559', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002559', Y, X],O1,M1,_) \ fact(['obo:RO_0002566', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002566', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002529', X, Y],O1,M1,_), fact(['obo:RO_0002529', Y, Z],O2,M2,_) \ fact(['obo:RO_0002529', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002529',O1,M1),('obo:RO_0002529',O2,M2)],M), fact(['obo:RO_0002529', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002486', Y, X],O1,M1,_) \ fact(['obo:RO_0002485', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002485', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002485', Y, X],O1,M1,_) \ fact(['obo:RO_0002486', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002486', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004035', X, Y],O1,M1,_) \ fact(['obo:RO_0002263', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002263', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002325', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002452', X, Y],O1,M1,_) \ fact(['obo:RO_0002200', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002200', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002231', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002014', X, Y],O1,M1,_) \ fact(['obo:RO_0002335', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002335', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002213', X1, X2],O2,M2,_) \ fact(['obo:RO_0002429', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002213',O2,M2)],M), fact(['obo:RO_0002429', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002341', X, Y],O1,M1,_) \ fact(['obo:RO_0002337', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002337', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002025', X, Y1],O1,M1,_), fact(['obo:RO_0002025', X, Y2],O2,M2,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002025',O1,M1),('obo:RO_0002025',O2,M2)],M), fact(['owl:sameAs', Y1, Y2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002241', X, Y],O1,M1,_) \ fact(['obo:RO_0002309', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002309', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002486', X, Y],O1,M1,_) \ fact(['obo:RO_0002170', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002170', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002578', X, X1],O1,M1,_), fact(['obo:RO_0002327', X2, X1],O2,M2,_), fact(['obo:GO_0003674', X1],O3,M3,_), fact(['obo:GO_0003674', X],O4,M4,_) \ fact(['obo:RO_0002233', X, X2],add,_,U) <=> member(del,[O1,O2,O3,O4]) | check_pos_mark([('obo:RO_0002578',O1,M1),('obo:RO_0002327',O2,M2),('obo:GO_0003674',O3,M3),('obo:GO_0003674',O4,M4)],M), fact(['obo:RO_0002233', X, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002629', X, Y],O1,M1,_) \ fact(['obo:RO_0002578', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002578', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011002', X, Y],O1,M1,_) \ fact(['obo:RO_0002566', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002566', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002473', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004031', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002352', Y, X],O1,M1,_) \ fact(['obo:RO_0002233', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002233', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002233', Y, X],O1,M1,_) \ fact(['obo:RO_0002352', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002352', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002507', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002304', X, Y],O1,M1,_) \ fact(['obo:RO_0004047', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004047', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002352', X3, X1],O1,M1,_), fact(['obo:RO_0002333', X2, X3],O2,M2,_), fact(['obo:RO_0002014', X, X1],O3,M3,_) \ fact(['obo:RO_0002630', X2, X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002352',O1,M1),('obo:RO_0002333',O2,M2),('obo:RO_0002014',O3,M3)],M), fact(['obo:RO_0002630', X2, X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002158', X, Y],O1,M1,_) \ fact(['obo:RO_0002320', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002320', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002352', X3, X1],O1,M1,_), fact(['obo:RO_0002333', X2, X3],O2,M2,_), fact(['obo:RO_0002015', X, X1],O3,M3,_) \ fact(['obo:RO_0002629', X2, X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002352',O1,M1),('obo:RO_0002333',O2,M2),('obo:RO_0002015',O3,M3)],M), fact(['obo:RO_0002629', X2, X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002412', X, Y],O1,M1,_) \ fact(['obo:RO_0002090', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002090', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002013', X, Y],O1,M1,_) \ fact(['obo:RO_0002334', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002334', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X, Y],O1,M1,_) \ fact(['obo:RO_0002215', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002215', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002286', X0, X1],O1,M1,_), fact(['obo:RO_0002497', X1, X2],O2,M2,_) \ fact(['obo:RO_0002497', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002286',O1,M1),('obo:RO_0002497',O2,M2)],M), fact(['obo:RO_0002497', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002204', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000301', X, Y],O1,M1,_), fact(['obo:RO_0000301', Y, Z],O2,M2,_) \ fact(['obo:RO_0000301', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0000301',O1,M1),('obo:RO_0000301',O2,M2)],M), fact(['obo:RO_0000301', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001018', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002557', Y, X],O1,M1,_) \ fact(['obo:RO_0002556', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002556', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002556', Y, X],O1,M1,_) \ fact(['obo:RO_0002557', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002557', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000302', X, Y],O1,M1,_), fact(['obo:RO_0000302', Y, Z],O2,M2,_) \ fact(['obo:RO_0000302', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0000302',O1,M1),('obo:RO_0000302',O2,M2)],M), fact(['obo:RO_0000302', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002371', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002177', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002371',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002177', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002176', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002493', X, Y],O1,M1,_) \ fact(['obo:RO_0002492', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002492', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002345', X0, X1],O1,M1,_), fact(['obo:BFO_0000051', X1, X2],O2,M2,_) \ fact(['obo:RO_0002345', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002345',O1,M1),('obo:BFO_0000051',O2,M2)],M), fact(['obo:RO_0002345', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002112', Y, X],O1,M1,_) \ fact(['obo:RO_0002106', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002106', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002106', Y, X],O1,M1,_) \ fact(['obo:RO_0002112', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002112', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002023', X, Y],O1,M1,_) \ fact(['obo:RO_0002022', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002022', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002353', Y, X],O1,M1,_) \ fact(['obo:RO_0002234', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002234', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002234', Y, X],O1,M1,_) \ fact(['obo:RO_0002353', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002353', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002022', X, Y],O1,M1,_) \ fact(['obo:RO_0002334', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002334', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002215',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002296', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002257', Y, X],O1,M1,_) \ fact(['obo:RO_0002256', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002256', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002256', Y, X],O1,M1,_) \ fact(['obo:RO_0002257', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002257', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002026', _, X1],O1,M1,_) \ fact(['foaf:image', X1],add,_,U) <=> member(del,[O1]) | fact(['foaf:image', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002559', X, Y],O1,M1,_) \ fact(['obo:RO_0002506', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002506', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002332', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002297', X, Y],O1,M1,_) \ fact(['obo:RO_0002234', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002234', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002373', X, Y],O1,M1,_) \ fact(['obo:RO_0002567', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002567', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002557', X, Y],O1,M1,_) \ fact(['obo:RO_0002453', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002453', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002342', X, Y],O1,M1,_) \ fact(['obo:RO_0002021', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002021', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002121', X, _],O1,M1,_) \ fact(['obo:CL_0000540', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000540', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002305', X, Y],O1,M1,_) \ fact(['obo:RO_0002411', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002411', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002254', _, X1],O1,M1,_) \ fact(['obo:CARO_0000000', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000000', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002450', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002513', X, Y],O1,M1,_) \ fact(['obo:RO_0002330', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002330', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002599', X, Y],O1,M1,_) \ fact(['obo:RO_0002597', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002597', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002639', X, Y],O1,M1,_) \ fact(['obo:RO_0002635', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002635', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011014', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002461', X0, X1],O1,M1,_), fact(['obo:RO_0002468', X1, X2],O2,M2,_), fact(['obo:RO_0002461', X3, X2],O3,M3,_) \ fact(['obo:RO_0002443', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002461',O1,M1),('obo:RO_0002468',O2,M2),('obo:RO_0002461',O3,M3)],M), fact(['obo:RO_0002443', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004014', X, Y],O1,M1,_) \ fact(['obo:RO_0004010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002554', Y, X],O1,M1,_) \ fact(['obo:RO_0002553', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002553', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002553', Y, X],O1,M1,_) \ fact(['obo:RO_0002554', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002554', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002176', X1, X0],O1,M1,_), fact(['obo:RO_0002176', X1, X2],O2,M2,_) \ fact(['obo:RO_0002170', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002176',O1,M1),('obo:RO_0002176',O2,M2)],M), fact(['obo:RO_0002170', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002630', X, X2],O1,M1,_), fact(['obo:RO_0002025', X, X1],O2,M2,_) \ fact(['obo:RO_0002630', X1, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002630',O1,M1),('obo:RO_0002025',O2,M2)],M), fact(['obo:RO_0002630', X1, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004019', X, Y],O1,M1,_) \ fact(['obo:RO_0004023', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004023', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002331', X, Y],O1,M1,_) \ fact(['obo:RO_0000056', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000056', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002110', Y, X],O1,M1,_) \ fact(['obo:RO_0002102', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002102', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002102', Y, X],O1,M1,_) \ fact(['obo:RO_0002110', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002110', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002224', X0, X1],O1,M1,_), fact(['obo:RO_0002400', X1, X2],O2,M2,_) \ fact(['obo:RO_0002400', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002224',O1,M1),('obo:RO_0002400',O2,M2)],M), fact(['obo:RO_0002400', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002221', Y, X],O1,M1,_) \ fact(['obo:RO_0002219', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002219', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002219', Y, X],O1,M1,_) \ fact(['obo:RO_0002221', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002221', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002298', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002526', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004022', X, Y],O1,M1,_) \ fact(['obo:RO_0004019', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004019', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002509', X, Y],O1,M1,_) \ fact(['obo:RO_0002506', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002506', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002566', _, X1],O1,M1,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002517', X, Y],O1,M1,_), fact(['obo:RO_0002517', Y, Z],O2,M2,_) \ fact(['obo:RO_0002517', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002517',O1,M1),('obo:RO_0002517',O2,M2)],M), fact(['obo:RO_0002517', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002570', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0001018', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0001025',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0001018', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002519', X, Y],O1,M1,_), fact(['obo:RO_0002519', Y, Z],O2,M2,_) \ fact(['obo:RO_0002519', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002519',O1,M1),('obo:RO_0002519',O2,M2)],M), fact(['obo:RO_0002519', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002340', X0, X1],O1,M1,_), fact(['obo:BFO_0000051', X1, X2],O2,M2,_) \ fact(['obo:RO_0002340', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002340',O1,M1),('obo:BFO_0000051',O2,M2)],M), fact(['obo:RO_0002340', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002162', _, X1],O1,M1,_) \ fact(['obo:CARO_0001010', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002384', X, Y],O1,M1,_) \ fact(['obo:RO_0002324', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002324', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011023', X, Y],O1,M1,_) \ fact(['obo:RO_0011022', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011022', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002518', X, Y],O1,M1,_), fact(['obo:RO_0002518', Y, Z],O2,M2,_) \ fact(['obo:RO_0002518', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002518',O1,M1),('obo:RO_0002518',O2,M2)],M), fact(['obo:RO_0002518', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002456', X, Y],O1,M1,_) \ fact(['obo:RO_0002442', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002442', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002441', X, Y],O1,M1,_) \ fact(['obo:RO_0002440', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002440', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002106', X, Y],O1,M1,_) \ fact(['obo:RO_0002120', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002120', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002232', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002565', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002503', X, Y],O1,M1,_) \ fact(['obo:RO_0002502', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002502', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002300', X, Y],O1,M1,_) \ fact(['obo:RO_0002552', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002552', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002008', X, _],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002375', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X2, X],O1,M1,_), fact(['obo:BFO_0000066', X, X1],O2,M2,_) \ fact(['obo:BFO_0000050', X2, X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:BFO_0000066',O2,M2)],M), fact(['obo:BFO_0000050', X2, X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002526', X, Y],O1,M1,_) \ fact(['obo:RO_0002514', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002514', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002248', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003311', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002516', X, Y],O1,M1,_), fact(['obo:RO_0002516', Y, Z],O2,M2,_) \ fact(['obo:RO_0002516', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002516',O1,M1),('obo:RO_0002516',O2,M2)],M), fact(['obo:RO_0002516', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002377', X0, X1],O1,M1,_), fact(['obo:RO_0002381', X1, X2],O2,M2,_) \ fact(['obo:RO_0002380', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002377',O1,M1),('obo:RO_0002381',O2,M2)],M), fact(['obo:RO_0002380', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002356', _, X1],O1,M1,_) \ fact(['obo:CL_0000000', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000000', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002458', Y, X],O1,M1,_) \ fact(['obo:RO_0002439', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002439', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002439', Y, X],O1,M1,_) \ fact(['obo:RO_0002458', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002458', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002552', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002170', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002180', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002211', X1, X2],O2,M2,_), fact(['obo:RO_0002333', X2, X3],O3,M3,_) \ fact(['obo:RO_0002448', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002211',O2,M2),('obo:RO_0002333',O3,M3)],M), fact(['obo:RO_0002448', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002509', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002408', X, Y],O1,M1,_) \ fact(['obo:RO_0002630', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002630', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003302', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004022', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002445', Y, X],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002444', Y, X],O1,M1,_) \ fact(['obo:RO_0002445', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002445', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002176', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002240', X, Y],O1,M1,_) \ fact(['obo:RO_0002244', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002244', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004018', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002477', X, Y],O1,M1,_) \ fact(['obo:RO_0002476', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002476', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0004047', X1, X2],O2,M2,_) \ fact(['obo:RO_0004032', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0004047',O2,M2)],M), fact(['obo:RO_0004032', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002015', X, Y],O1,M1,_) \ fact(['obo:RO_0002013', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002013', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002525', X, Y],O1,M1,_) \ fact(['obo:RO_0002526', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002526', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009001', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011007', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000300', X, Y],O1,M1,_), fact(['obo:RO_0000300', Y, Z],O2,M2,_) \ fact(['obo:RO_0000300', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0000300',O1,M1),('obo:RO_0000300',O2,M2)],M), fact(['obo:RO_0000300', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002472', X, Y],O1,M1,_) \ fact(['obo:RO_0002616', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002616', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002433', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000000', X, X1],O1,M1,_), fact(['obo:BFO_0000003', X],O2,M2,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000000',O1,M1),('obo:BFO_0000003',O2,M2)],M), fact(['obo:BFO_0000003', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002551', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011010', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002412', Y, X],O1,M1,_) \ fact(['obo:RO_0002405', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002405', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002405', Y, X],O1,M1,_) \ fact(['obo:RO_0002412', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002412', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002293', Y, X],O1,M1,_) \ fact(['obo:RO_0002291', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002291', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002291', Y, X],O1,M1,_) \ fact(['obo:RO_0002293', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002293', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002460', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002229', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002333', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002573', _, X1],O1,M1,_) \ fact(['obo:BFO_0000020', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002426', _, X1],O1,M1,_) \ fact(['obo:BFO_0000020', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002516', X, Y],O1,M1,_) \ fact(['obo:RO_0002524', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002524', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002223', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002205', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002509', X, _],O1,M1,_) \ fact(['obo:RO_0002577', X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002577', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002462', X0, X1],O1,M1,_), fact(['obo:RO_0002468', X1, X2],O2,M2,_), fact(['obo:RO_0002463', X3, X2],O3,M3,_) \ fact(['obo:RO_0002444', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002462',O1,M1),('obo:RO_0002468',O2,M2),('obo:RO_0002463',O3,M3)],M), fact(['obo:RO_0002444', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011016', X, Y],O1,M1,_) \ fact(['obo:RO_0011004', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011004', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002411', Y, X],O1,M1,_) \ fact(['obo:RO_0002404', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002404', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002404', Y, X],O1,M1,_) \ fact(['obo:RO_0002411', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002411', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002254', X, Y],O1,M1,_) \ fact(['obo:RO_0002258', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002258', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002463', X, Y],O1,M1,_) \ fact(['obo:RO_0002461', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002461', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002525', X, Y],O1,M1,_) \ fact(['obo:RO_0002523', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002523', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004019', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002569', Y, X],O1,M1,_) \ fact(['obo:RO_0002380', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002380', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002380', Y, X],O1,M1,_) \ fact(['obo:RO_0002569', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002569', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000301', X, Y],O1,M1,_) \ fact(['obo:RO_0000300', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000300', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002432', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002103', X, Y],O1,M1,_) \ fact(['obo:RO_0000301', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000301', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011022', X, Y],O1,M1,_) \ fact(['obo:RO_0011003', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011003', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011010', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001023', X, Y],O1,M1,_) \ fact(['obo:RO_0003302', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003302', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003003', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002468', X, Y],O1,M1,_) \ fact(['obo:RO_0002465', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002465', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002025', X, Y],O1,M1,_) \ fact(['obo:RO_0002211', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002211', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002134', X, Y],O1,M1,_) \ fact(['owl:topObjectProperty', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:topObjectProperty', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:BFO_0000051', X1, X2],O2,M2,_) \ fact(['obo:RO_0002327', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:BFO_0000051',O2,M2)],M), fact(['obo:RO_0002327', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002411', X1, X2],O2,M2,_), fact(['obo:RO_0002333', X2, X3],O3,M3,_) \ fact(['obo:RO_0002566', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002411',O2,M2),('obo:RO_0002333',O3,M3)],M), fact(['obo:RO_0002566', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X0, X1],O1,M1,_), fact(['obo:RO_0002482', X1, X2],O2,M2,_), fact(['obo:RO_0002400', X2, X3],O3,M3,_) \ fact(['obo:RO_0002480', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002215',O1,M1),('obo:RO_0002482',O2,M2),('obo:RO_0002400',O3,M3)],M), fact(['obo:RO_0002480', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002201', X, Y1],O1,M1,_), fact(['obo:RO_0002201', X, Y2],O2,M2,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002201',O1,M1),('obo:RO_0002201',O2,M2)],M), fact(['owl:sameAs', Y1, Y2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002384', X, _],O1,M1,_) \ fact(['obo:CARO_0000000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:BFO_0000062', X1, X2],O2,M2,_) \ fact(['obo:BFO_0000062', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000062',O2,M2)],M), fact(['obo:BFO_0000062', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002515', X, Y],O1,M1,_) \ fact(['obo:RO_0002527', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002527', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002570', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002462', X, Y],O1,M1,_) \ fact(['obo:RO_0002461', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002461', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002552', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002007', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002517', Y, X],O1,M1,_) \ fact(['obo:RO_0002516', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002516', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002516', Y, X],O1,M1,_) \ fact(['obo:RO_0002517', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002517', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000054', X0, X1],O1,M1,_), fact(['obo:RO_0002404', X1, X2],O2,M2,_) \ fact(['obo:RO_0009501', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000054',O1,M1),('obo:RO_0002404',O2,M2)],M), fact(['obo:RO_0009501', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002109', Y, X],O1,M1,_) \ fact(['obo:RO_0002105', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002105', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002105', Y, X],O1,M1,_) \ fact(['obo:RO_0002109', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002109', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002113', X, Y],O1,M1,_) \ fact(['obo:RO_0002130', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002130', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002448', X, Y],O1,M1,_) \ fact(['obo:RO_0011002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002234', X, Y],O1,M1,_) \ fact(['obo:RO_0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0040036', X, Y],O1,M1,_) \ fact(['obo:RO_0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002524', X, Y],O1,M1,_) \ fact(['obo:RO_0002526', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002526', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002572', X, _],O1,M1,_) \ fact(['obo:BFO_0000141', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000141', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002445', X, Y],O1,M1,_) \ fact(['obo:RO_0002453', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002453', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002329', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004028', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002492', X, Y],O1,M1,_) \ fact(['obo:RO_0002497', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002497', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002018', X, Y],O1,M1,_) \ fact(['obo:RO_0002180', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002180', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002326', X, Y],O1,M1,_) \ fact(['obo:RO_0002216', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002216', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002524', X, Y],O1,M1,_) \ fact(['obo:RO_0002522', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002522', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002332', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003307', X, Y],O1,M1,_) \ fact(['obo:RO_0003305', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003305', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002511', Y, X],O1,M1,_) \ fact(['obo:RO_0002510', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002510', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002510', Y, X],O1,M1,_) \ fact(['obo:RO_0002511', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002511', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003003', X, Y],O1,M1,_) \ fact(['obo:RO_0002450', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002450', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002625', Y, X],O1,M1,_) \ fact(['obo:RO_0002624', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002624', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002624', Y, X],O1,M1,_) \ fact(['obo:RO_0002625', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002625', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002452', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002625', X, Y],O1,M1,_) \ fact(['obo:RO_0002619', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002619', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002343', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002014', X, Y],O1,M1,_) \ fact(['obo:RO_0002013', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002013', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002349', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002513', Y, X],O1,M1,_) \ fact(['obo:RO_0002512', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002512', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002512', Y, X],O1,M1,_) \ fact(['obo:RO_0002513', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002513', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002375', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002354', Y, X],O1,M1,_) \ fact(['obo:RO_0002297', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002297', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002297', Y, X],O1,M1,_) \ fact(['obo:RO_0002354', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002354', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002507', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002568', X, Y],O1,M1,_) \ fact(['obo:RO_0002567', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002567', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002224', X0, X1],O1,M1,_), fact(['obo:RO_0002230', X1, X2],O2,M2,_) \ fact(['obo:RO_0002087', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002224',O1,M1),('obo:RO_0002230',O2,M2)],M), fact(['obo:RO_0002087', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002025', X, X1],O1,M1,_), fact(['obo:RO_0002233', X1, X2],O2,M2,_) \ fact(['obo:RO_0002233', X, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002025',O1,M1),('obo:RO_0002233',O2,M2)],M), fact(['obo:RO_0002233', X, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002007', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011003', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002485', X, Y],O1,M1,_) \ fact(['obo:RO_0002170', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002170', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000001', X, Y],O1,M1,_) \ fact(['obo:RO_0002158', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002158', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002627', Y, X],O1,M1,_) \ fact(['obo:RO_0002626', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002626', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002626', Y, X],O1,M1,_) \ fact(['obo:RO_0002627', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002627', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002331', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002331', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002476', X, _],O1,M1,_) \ fact(['obo:GO_0005634', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0005634', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002339', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002339', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002339',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002339', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001020', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008506', _, X1],O1,M1,_) \ fact(['obo:CARO_0001010', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004006', X, Y],O1,M1,_) \ fact(['obo:RO_0004000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002244', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002253', Y, X],O1,M1,_) \ fact(['obo:RO_0002252', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002252', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002252', Y, X],O1,M1,_) \ fact(['obo:RO_0002253', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002253', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002447', X, Y],O1,M1,_) \ fact(['obo:RO_0002436', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002436', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002558', Y, X],O1,M1,_) \ fact(['obo:RO_0002472', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002472', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002472', Y, X],O1,M1,_) \ fact(['obo:RO_0002558', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002558', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002225', X, Y],O1,M1,_) \ fact(['obo:RO_0002202', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002202', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003301', Y, X],O1,M1,_) \ fact(['obo:RO_0002615', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002615', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002615', Y, X],O1,M1,_) \ fact(['obo:RO_0003301', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003301', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002216', X, Y],O1,M1,_) \ fact(['obo:RO_0002500', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002500', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002130', Y, X],O1,M1,_) \ fact(['obo:RO_0002006', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002006', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002006', Y, X],O1,M1,_) \ fact(['obo:RO_0002130', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002130', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002333', Y, X],O1,M1,_) \ fact(['obo:RO_0002327', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002327', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', Y, X],O1,M1,_) \ fact(['obo:RO_0002333', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002333', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002578', X, X2],O1,M1,_), fact(['obo:RO_0002025', X, X1],O2,M2,_) \ fact(['obo:RO_0002578', X1, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002578',O1,M1),('obo:RO_0002025',O2,M2)],M), fact(['obo:RO_0002578', X1, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011009', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002354', X, Y],O1,M1,_) \ fact(['obo:RO_0002353', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002353', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002406', X0, X1],O1,M1,_), fact(['obo:RO_0002407', X1, X2],O2,M2,_) \ fact(['obo:RO_0002407', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002406',O1,M1),('obo:RO_0002407',O2,M2)],M), fact(['obo:RO_0002407', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002578', X, Y],O1,M1,_) \ fact(['obo:RO_0002412', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002412', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002473', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008508', X, Y],O1,M1,_) \ fact(['obo:RO_0002619', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002619', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000300', _, X1],O1,M1,_) \ fact(['obo:CL_0000540', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000540', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002608', Y, X],O1,M1,_) \ fact(['obo:RO_0002500', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002500', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002500', Y, X],O1,M1,_) \ fact(['obo:RO_0002608', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002608', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002134', Y, X],O1,M1,_) \ fact(['obo:RO_0002005', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002005', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002005', Y, X],O1,M1,_) \ fact(['obo:RO_0002134', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002134', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004025', _, X1],O1,M1,_) \ fact(['obo:CARO_0000006', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000006', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002255', Y, X],O1,M1,_) \ fact(['obo:RO_0002254', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002254', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002254', Y, X],O1,M1,_) \ fact(['obo:RO_0002255', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002255', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002256', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011009', X, Y],O1,M1,_) \ fact(['obo:RO_0011021', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011021', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002255', X, Y],O1,M1,_) \ fact(['obo:RO_0002385', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002385', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002258', X, _],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002257', X, Y],O1,M1,_) \ fact(['obo:RO_0002286', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002286', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002376', X, Y],O1,M1,_) \ fact(['obo:RO_0002375', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002375', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002211', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002407', X0, X1],O1,M1,_), fact(['obo:RO_0002406', X1, X2],O2,M2,_) \ fact(['obo:RO_0002407', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002407',O1,M1),('obo:RO_0002406',O2,M2)],M), fact(['obo:RO_0002407', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000063', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002584', X, Y],O1,M1,_) \ fact(['obo:RO_0002595', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002595', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002207', X, Y],O1,M1,_) \ fact(['obo:RO_0002202', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002202', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002233', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002497', X0, X1],O1,M1,_), fact(['obo:RO_0002082', X1, X2],O2,M2,_) \ fact(['obo:RO_0002497', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002497',O1,M1),('obo:RO_0002082',O2,M2)],M), fact(['obo:RO_0002497', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002455', X, Y],O1,M1,_) \ fact(['obo:RO_0002442', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002442', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002012', X, Y],O1,M1,_) \ fact(['obo:RO_0002418', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002418', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002630', Y, X],O1,M1,_) \ fact(['obo:RO_0002023', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002023', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002023', Y, X],O1,M1,_) \ fact(['obo:RO_0002630', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002630', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002585', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002105', X, Y],O1,M1,_) \ fact(['obo:RO_0002120', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002120', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002211', X, Y],O1,M1,_) \ fact(['obo:RO_0002411', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002411', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002005', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002476', X, Y],O1,M1,_) \ fact(['obo:RO_0002258', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002258', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002636', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002108', Y, X],O1,M1,_) \ fact(['obo:RO_0002107', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002107', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002107', Y, X],O1,M1,_) \ fact(['obo:RO_0002108', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002108', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001022', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002210', X, Y],O1,M1,_) \ fact(['obo:RO_0002203', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002203', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002114', X, Y],O1,M1,_) \ fact(['obo:RO_0002120', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002120', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004026', X, Y],O1,M1,_) \ fact(['obo:RO_0040035', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040035', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002437', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002018', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009002', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008504', X, Y],O1,M1,_) \ fact(['obo:RO_0002445', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002445', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002496', X0, X1],O1,M1,_), fact(['obo:BFO_0000062', X1, X2],O2,M2,_) \ fact(['obo:RO_0002496', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002496',O1,M1),('obo:BFO_0000062',O2,M2)],M), fact(['obo:RO_0002496', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002519', Y, X],O1,M1,_) \ fact(['obo:RO_0002518', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002518', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002518', Y, X],O1,M1,_) \ fact(['obo:RO_0002519', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002519', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002414', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002352', X3, X1],O1,M1,_), fact(['obo:RO_0002333', X2, X3],O2,M2,_), fact(['obo:RO_0002013', X, X1],O3,M3,_) \ fact(['obo:RO_0002578', X2, X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002352',O1,M1),('obo:RO_0002333',O2,M2),('obo:RO_0002013',O3,M3)],M), fact(['obo:RO_0002578', X2, X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002180', X1, X],O1,M1,_), fact(['obo:BFO_0000015', X1],O2,M2,_), fact(['obo:BFO_0000015', X],O3,M3,_) \ fact(['obo:RO_0002018', X1, X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002180',O1,M1),('obo:BFO_0000015',O2,M2),('obo:BFO_0000015',O3,M3)],M), fact(['obo:RO_0002018', X1, X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X, Y],O1,M1,_) \ fact(['obo:RO_0002216', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002216', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003310', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002635', X, Y],O1,M1,_) \ fact(['obo:RO_0002445', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002445', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002216', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002215',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002216', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002373', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002285', X, Y],O1,M1,_) \ fact(['obo:RO_0002258', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002258', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X0, X1],O1,M1,_), fact(['obo:RO_0002215', X1, X2],O2,M2,_) \ fact(['obo:RO_0002584', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:RO_0002215',O2,M2)],M), fact(['obo:RO_0002584', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002204', _, X1],O1,M1,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011008', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X0, X1],O1,M1,_), fact(['obo:RO_0002131', X1, X2],O2,M2,_) \ fact(['obo:RO_0002131', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:RO_0002131',O2,M2)],M), fact(['obo:RO_0002131', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002591', X, Y],O1,M1,_) \ fact(['obo:RO_0002233', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002233', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002411', X, X1],O1,M1,_), fact(['obo:RO_0002131', X, X1],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002411',O1,M1),('obo:RO_0002131',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002411', X, X1],O1,M1,_), fact(['obo:RO_0002131', X, X1],O2,M2,_) \ fact(['owl:Nothing', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002411',O1,M1),('obo:RO_0002131',O2,M2)],M), fact(['owl:Nothing', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002021', X, Y],O1,M1,_) \ fact(['obo:RO_0002479', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002479', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002508', X, Y],O1,M1,_) \ fact(['obo:RO_0002566', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002566', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011002', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0072519', X],O1,M1,_) \ fact(['obo:RO_0002468', X, X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002468', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002507', X, Y],O1,M1,_) \ fact(['obo:RO_0002509', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002509', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000066', X1, X0],O1,M1,_), fact(['obo:RO_0002234', X1, X2],O2,M2,_) \ fact(['obo:RO_0003000', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000066',O1,M1),('obo:RO_0002234',O2,M2)],M), fact(['obo:RO_0003000', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002437', X, Y],O1,M1,_) \ fact(['obo:RO_0002434', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002434', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008507', X, Y],O1,M1,_) \ fact(['obo:RO_0002618', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002618', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002130', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002375', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002411', X, Y],O1,M1,_) \ fact(['obo:BFO_0000063', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000063', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:RO_0002210', X1, X2],O2,M2,_) \ fact(['obo:RO_0002287', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:RO_0002210',O2,M2)],M), fact(['obo:RO_0002287', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002428', X, Y],O1,M1,_) \ fact(['obo:RO_0002431', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002431', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003301', X, X],O1,M1,_) \ fact(['owl:Nothing', X, X],add,_,U) <=> member(del,[O1]) | fact(['owl:Nothing', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002254', X0, X1],O1,M1,_), fact(['obo:RO_0002162', X1, X2],O2,M2,_) \ fact(['obo:RO_0002162', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002254',O1,M1),('obo:RO_0002162',O2,M2)],M), fact(['obo:RO_0002162', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002131', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002131', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002013', X, Y],O1,M1,_) \ fact(['obo:RO_0002017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002249', Y, X],O1,M1,_) \ fact(['obo:RO_0002248', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002248', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002248', Y, X],O1,M1,_) \ fact(['obo:RO_0002249', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002249', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000302', X, Y],O1,M1,_) \ fact(['obo:RO_0000300', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000300', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002220', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002445', X, Y],O1,M1,_) \ fact(['obo:RO_0002443', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002443', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002233', X, Y],O1,M1,_) \ fact(['obo:RO_0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002454', X, Y],O1,M1,_) \ fact(['obo:RO_0002440', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002440', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002534', X],O1,M1,_) \ fact(['obo:RO_0002532', X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002532', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002177', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004023', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002489', X, Y],O1,M1,_) \ fact(['obo:RO_0002488', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002488', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004018', Y, X],O1,M1,_) \ fact(['obo:RO_0004017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004017', Y, X],O1,M1,_) \ fact(['obo:RO_0004018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004029', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002444', X, Y],O1,M1,_) \ fact(['obo:RO_0002454', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002454', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004020', _, X1],O1,M1,_) \ fact(['obo:CARO_0000006', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000006', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002450', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002203', X, Y],O1,M1,_) \ fact(['obo:RO_0002388', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002388', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002120', X, Y],O1,M1,_) \ fact(['obo:RO_0000302', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000302', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002465', X, Y],O1,M1,_) \ fact(['obo:RO_0002563', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002563', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002160', X, Y],O1,M1,_) \ fact(['obo:RO_0002162', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002162', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002131', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002131', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002203', X, Y],O1,M1,_) \ fact(['obo:RO_0002387', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002387', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003002', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002467', X, Y],O1,M1,_) \ fact(['obo:RO_0002465', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002465', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002529', X, Y],O1,M1,_) \ fact(['obo:RO_0002527', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002527', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002254', X, _],O1,M1,_) \ fact(['obo:CARO_0000000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002372', X, Y],O1,M1,_) \ fact(['obo:RO_0002567', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002567', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002629', Y, X],O1,M1,_) \ fact(['obo:RO_0002024', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002024', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002024', Y, X],O1,M1,_) \ fact(['obo:RO_0002629', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002629', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002500', X, Y],O1,M1,_) \ fact(['obo:RO_0002595', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002595', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002556', X, Y],O1,M1,_) \ fact(['obo:RO_0002454', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002454', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002304', X, Y],O1,M1,_) \ fact(['obo:RO_0002411', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002411', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002619', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002577', X],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002492', X, Y],O1,M1,_) \ fact(['obo:RO_0002490', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002490', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002438', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008503', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002248', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002202', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002325', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001021', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002297', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002488', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002488', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002488',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002488', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002298', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002292', Y, X],O1,M1,_) \ fact(['obo:RO_0002206', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002206', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002206', Y, X],O1,M1,_) \ fact(['obo:RO_0002292', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002292', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0010002', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002226', X, Y],O1,M1,_) \ fact(['obo:RO_0002258', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002258', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002004', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002641', X, Y],O1,M1,_) \ fact(['obo:RO_0002635', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002635', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002630', X, Y],O1,M1,_) \ fact(['obo:RO_0002212', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002212', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002157', X, Y],O1,M1,_) \ fact(['obo:RO_0002320', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002320', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002295', X, Y],O1,M1,_) \ fact(['obo:RO_0002324', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002324', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002570', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002595', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002026', X, _],O1,M1,_) \ fact(['foaf:image', X],add,_,U) <=> member(del,[O1]) | fact(['foaf:image', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002102', X, _],O1,M1,_) \ fact(['obo:CL_0000540', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000540', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002623', Y, X],O1,M1,_) \ fact(['obo:RO_0002622', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002622', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002622', Y, X],O1,M1,_) \ fact(['obo:RO_0002623', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002623', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003306', X, Y],O1,M1,_) \ fact(['obo:RO_0003304', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003304', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009001', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001018', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002115', X, Y],O1,M1,_) \ fact(['obo:RO_0002103', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002103', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002598', X, Y],O1,M1,_) \ fact(['obo:RO_0002596', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002596', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002638', X, Y],O1,M1,_) \ fact(['obo:RO_0002634', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002634', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004046', X, Y],O1,M1,_) \ fact(['obo:RO_0002418', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002418', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002150', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002607', X, Y],O1,M1,_) \ fact(['obo:RO_0002610', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002610', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002207', X0, X1],O1,M1,_), fact(['obo:RO_0001025', X1, X2],O2,M2,_) \ fact(['obo:RO_0002226', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002207',O1,M1),('obo:RO_0001025',O2,M2)],M), fact(['obo:RO_0002226', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002008', _, X1],O1,M1,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002514', X, _],O1,M1,_) \ fact(['obo:RO_0002532', X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002532', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002512', X, Y],O1,M1,_) \ fact(['obo:RO_0002330', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002330', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002213', X, Y],O1,M1,_) \ fact(['obo:RO_0002304', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002304', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008505', _, X1],O1,M1,_) \ fact(['obo:CARO_0001010', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002313', X, Y],O1,M1,_) \ fact(['obo:RO_0002337', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002337', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004015', X, Y],O1,M1,_) \ fact(['obo:RO_0004010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004028', X, _],O1,M1,_) \ fact(['obo:BFO_0000017', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000017', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002085', X, Y],O1,M1,_), fact(['obo:RO_0002085', Y, Z],O2,M2,_) \ fact(['obo:RO_0002085', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002085',O1,M1),('obo:RO_0002085',O2,M2)],M), fact(['obo:RO_0002085', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002202', X, Y],O1,M1,_) \ fact(['obo:RO_0002258', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002258', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002303', _, X1],O1,M1,_) \ fact(['obo:ENVO_01000254', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:ENVO_01000254', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002446', X, Y],O1,M1,_) \ fact(['obo:RO_0002437', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002437', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002121', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002121', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002121',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002121', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002233', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011007', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004001', X, Y],O1,M1,_) \ fact(['obo:RO_0004000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002012', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002429', X, Y],O1,M1,_) \ fact(['obo:RO_0002428', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002428', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002337', _, X1],O1,M1,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002111', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002006', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002640', X, Y],O1,M1,_) \ fact(['obo:RO_0002634', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002634', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002589', X, Y],O1,M1,_) \ fact(['obo:RO_0002586', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002586', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001023', Y, X],O1,M1,_) \ fact(['obo:RO_0001021', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001021', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001021', Y, X],O1,M1,_) \ fact(['obo:RO_0001023', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001023', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002508', Y, X],O1,M1,_) \ fact(['obo:RO_0002507', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002507', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002507', Y, X],O1,M1,_) \ fact(['obo:RO_0002508', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002508', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004032', X, Y],O1,M1,_) \ fact(['obo:RO_0002264', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002264', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002012', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002630', X1, X2],O2,M2,_), fact(['obo:RO_0002333', X2, X3],O3,M3,_) \ fact(['obo:RO_0002449', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002630',O2,M2),('obo:RO_0002333',O3,M3)],M), fact(['obo:RO_0002449', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002232', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002305', X1, X2],O2,M2,_) \ fact(['obo:RO_0004035', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002305',O2,M2)],M), fact(['obo:RO_0004035', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X0, X1],O1,M1,_), fact(['obo:RO_0002202', X1, X2],O2,M2,_) \ fact(['obo:RO_0002254', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:RO_0002202',O2,M2)],M), fact(['obo:RO_0002254', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002563', X, Y],O1,M1,_) \ fact(['obo:RO_0002464', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002464', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011007', X, Y],O1,M1,_) \ fact(['obo:RO_0011023', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011023', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002255', X, Y],O1,M1,_) \ fact(['obo:RO_0002286', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002286', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002476', _, X1],O1,M1,_) \ fact(['obo:GO_0005634', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0005634', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002005', _, X1],O1,M1,_) \ fact(['obo:CARO_0001001', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001001', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011010', X, Y],O1,M1,_) \ fact(['obo:RO_0011021', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011021', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002593', X, Y],O1,M1,_) \ fact(['obo:RO_0002497', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002497', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003003', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002349', _, X1],O1,M1,_) \ fact(['obo:CL_0000000', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000000', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002296', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004047', X, Y],O1,M1,_) \ fact(['obo:RO_0002418', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002418', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008502', X, Y],O1,M1,_) \ fact(['obo:RO_0002440', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002440', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004002', X, Y],O1,M1,_) \ fact(['obo:RO_0004000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002383', X, Y],O1,M1,_) \ fact(['obo:RO_0002376', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002376', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002451', X, Y],O1,M1,_) \ fact(['obo:RO_0002321', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002321', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002313', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002408', X0, X1],O1,M1,_), fact(['obo:RO_0002409', X1, X2],O2,M2,_) \ fact(['obo:RO_0002409', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002408',O1,M1),('obo:RO_0002409',O2,M2)],M), fact(['obo:RO_0002409', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004016', X, Y],O1,M1,_) \ fact(['obo:RO_0004010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004024', X, Y],O1,M1,_) \ fact(['obo:RO_0004023', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004023', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002256', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002315', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002511', X, Y],O1,M1,_) \ fact(['obo:RO_0002330', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002330', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002150', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002597', X, Y],O1,M1,_) \ fact(['obo:RO_0002596', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002596', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002404', X, X1],O1,M1,_), fact(['obo:RO_0002131', X, X1],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002404',O1,M1),('obo:RO_0002131',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002404', X, X1],O1,M1,_), fact(['obo:RO_0002131', X, X1],O2,M2,_) \ fact(['owl:Nothing', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002404',O1,M1),('obo:RO_0002131',O2,M2)],M), fact(['owl:Nothing', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002619', Y, X],O1,M1,_) \ fact(['obo:RO_0002618', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002618', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002618', Y, X],O1,M1,_) \ fact(['obo:RO_0002619', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002619', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002591', X, Y],O1,M1,_) \ fact(['obo:RO_0002592', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002592', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002388', X, Y],O1,M1,_) \ fact(['obo:RO_0002387', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002387', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002206', X, _],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002406', X, Y],O1,M1,_) \ fact(['obo:RO_0002629', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002629', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002409', X0, X1],O1,M1,_), fact(['obo:RO_0002408', X1, X2],O2,M2,_) \ fact(['obo:RO_0002409', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002409',O1,M1),('obo:RO_0002408',O2,M2)],M), fact(['obo:RO_0002409', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003308', X, Y],O1,M1,_) \ fact(['obo:RO_0002610', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002610', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002209', Y, X],O1,M1,_) \ fact(['obo:RO_0002208', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002208', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002208', Y, X],O1,M1,_) \ fact(['obo:RO_0002209', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002209', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X0, X1],O1,M1,_), fact(['obo:RO_0002211', X1, X2],O2,M2,_) \ fact(['obo:RO_0002596', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002215',O1,M1),('obo:RO_0002211',O2,M2)],M), fact(['obo:RO_0002596', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004024', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004008', X, Y],O1,M1,_) \ fact(['obo:RO_0002234', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002234', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003002', X, Y],O1,M1,_) \ fact(['obo:RO_0002449', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002449', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002404', X, Y],O1,M1,_) \ fact(['obo:RO_0002427', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002427', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002258', X, Y],O1,M1,_) \ fact(['obo:RO_0002324', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002324', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002212', X, Y],O1,M1,_) \ fact(['obo:RO_0002305', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002305', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002634', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002436', X, Y],O1,M1,_) \ fact(['obo:RO_0002434', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002434', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002574', X, Y],O1,M1,_) \ fact(['obo:RO_0002437', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002437', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001022', Y, X],O1,M1,_) \ fact(['obo:RO_0001020', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001020', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001020', Y, X],O1,M1,_) \ fact(['obo:RO_0001022', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001022', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002220', X, Y],O1,M1,_) \ fact(['obo:RO_0002163', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002163', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002130', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002130', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002130',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002130', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002440', Y, X],O1,M1,_) \ fact(['obo:RO_0002440', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002440', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000300', X, _],O1,M1,_) \ fact(['obo:CL_0000540', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000540', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002588', X, Y],O1,M1,_) \ fact(['obo:RO_0002592', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002592', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004010', X, Y],O1,M1,_) \ fact(['obo:RO_0004018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002414', X, Y],O1,M1,_) \ fact(['obo:RO_0002411', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002411', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002588', X, Y],O1,M1,_) \ fact(['obo:RO_0002297', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002297', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002375', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002630', X, Y],O1,M1,_) \ fact(['obo:RO_0002578', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002578', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009004', _, X1],O1,M1,_) \ fact(['obo:CARO_0001010', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002507', X, _],O1,M1,_) \ fact(['obo:RO_0002577', X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002577', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002228', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002258', _, X1],O1,M1,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009001', X, X],O1,M1,_) \ fact(['owl:Nothing', X, X],add,_,U) <=> member(del,[O1]) | fact(['owl:Nothing', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004023', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', X0, X1],O1,M1,_), fact(['obo:RO_0001025', X2, X1],O2,M2,_) \ fact(['obo:RO_0002379', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0001025',O1,M1),('obo:RO_0001025',O2,M2)],M), fact(['obo:RO_0002379', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002210', Y, X],O1,M1,_) \ fact(['obo:RO_0002207', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002207', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002207', Y, X],O1,M1,_) \ fact(['obo:RO_0002210', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002210', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002411', X, Y],O1,M1,_), fact(['obo:RO_0002411', Y, Z],O2,M2,_) \ fact(['obo:RO_0002411', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002411',O1,M1),('obo:RO_0002411',O2,M2)],M), fact(['obo:RO_0002411', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008506', X, Y],O1,M1,_) \ fact(['obo:RO_0002321', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002321', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002479', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002355', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009501', X, _],O1,M1,_) \ fact(['obo:BFO_0000017', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000017', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X0, X1],O1,M1,_), fact(['obo:BFO_0000066', X1, X2],O2,M2,_) \ fact(['obo:RO_0002232', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002230',O1,M1),('obo:BFO_0000066',O2,M2)],M), fact(['obo:RO_0002232', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009002', X, X],O1,M1,_) \ fact(['owl:Nothing', X, X],add,_,U) <=> member(del,[O1]) | fact(['owl:Nothing', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001021', X, Y],O1,M1,_) \ fact(['obo:RO_0003302', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003302', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002237', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011003', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002357', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002101', _, X1],O1,M1,_) \ fact(['obo:CARO_0001001', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001001', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011009', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009003', X, X],O1,M1,_) \ fact(['owl:Nothing', X, X],add,_,U) <=> member(del,[O1]) | fact(['owl:Nothing', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002449', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011021', X, Y],O1,M1,_) \ fact(['obo:RO_0011003', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011003', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009005', X, X],O1,M1,_) \ fact(['owl:Nothing', X, X],add,_,U) <=> member(del,[O1]) | fact(['owl:Nothing', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004024', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004022', X, Y],O1,M1,_) \ fact(['obo:RO_0002200', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002200', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002624', X, Y],O1,M1,_) \ fact(['obo:RO_0002618', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002618', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002219', X, Y],O1,M1,_) \ fact(['obo:RO_0002220', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002220', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002627', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002019', X, Y],O1,M1,_) \ fact(['obo:RO_0002233', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002233', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002249', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002286', X, Y],O1,M1,_) \ fact(['obo:RO_0002384', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002384', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002156', X, Y],O1,M1,_) \ fact(['obo:RO_0002320', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002320', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002440', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002348', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002491', X, Y],O1,M1,_) \ fact(['obo:RO_0002492', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002492', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002211', X1, X2],O2,M2,_) \ fact(['obo:RO_0002428', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002211',O2,M2)],M), fact(['obo:RO_0002428', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002434', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X0, X1],O1,M1,_), fact(['obo:BFO_0000066', X1, X2],O2,M2,_) \ fact(['obo:RO_0002479', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:BFO_0000066',O2,M2)],M), fact(['obo:RO_0002479', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004028', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002501', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002418', X, Y],O1,M1,_), fact(['obo:RO_0002418', Y, Z],O2,M2,_) \ fact(['obo:RO_0002418', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002418',O1,M1),('obo:RO_0002418',O2,M2)],M), fact(['obo:RO_0002418', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002488', X, Y],O1,M1,_) \ fact(['obo:RO_0002496', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002496', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002374', X, Y],O1,M1,_) \ fact(['obo:RO_0002156', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002156', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002469', X, Y],O1,M1,_) \ fact(['obo:RO_0002438', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002438', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002571', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002322', X, Y],O1,M1,_) \ fact(['obo:RO_0002321', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002321', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002334', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002150', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002551', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002340', X, Y],O1,M1,_) \ fact(['obo:RO_0002020', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002020', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002488', X, Y],O1,M1,_) \ fact(['obo:RO_0002490', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002490', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002353', X, Y],O1,M1,_) \ fact(['obo:RO_0000056', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000056', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002336', X, Y],O1,M1,_) \ fact(['obo:RO_0002334', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002334', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002113', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002113', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002113',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002113', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002431', X, Y],O1,M1,_) \ fact(['obo:RO_0002500', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002500', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0010002', Y, X],O1,M1,_) \ fact(['obo:RO_0010001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0010001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0010001', Y, X],O1,M1,_) \ fact(['obo:RO_0010002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0010002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002566', X, Y],O1,M1,_) \ fact(['obo:RO_0002506', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002506', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002414', X, Y],O1,M1,_), fact(['obo:RO_0002414', Y, Z],O2,M2,_) \ fact(['obo:RO_0002414', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002414',O1,M1),('obo:RO_0002414',O2,M2)],M), fact(['obo:RO_0002414', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002618', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002338', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002338', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002338',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002338', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:BFO_0000063', X1, X2],O2,M2,_) \ fact(['obo:BFO_0000063', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000063',O2,M2)],M), fact(['obo:BFO_0000063', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004010', Y, X],O1,M1,_) \ fact(['obo:RO_0004000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004000', Y, X],O1,M1,_) \ fact(['obo:RO_0004010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002264', X, Y],O1,M1,_) \ fact(['obo:RO_0002500', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002500', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002352', X, Y],O1,M1,_) \ fact(['obo:RO_0000056', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000056', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002100', X, _],O1,M1,_) \ fact(['obo:CL_0000540', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000540', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002207', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002225', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002207',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002225', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002344', X, Y],O1,M1,_) \ fact(['obo:RO_0002337', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002337', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002209', X, Y],O1,M1,_) \ fact(['obo:RO_0002445', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002445', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002501', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003305', X, Y],O1,M1,_) \ fact(['obo:RO_0003304', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003304', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002002', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004011', Y, X],O1,M1,_) \ fact(['obo:RO_0004001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004001', Y, X],O1,M1,_) \ fact(['obo:RO_0004011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002206', X, Y],O1,M1,_) \ fact(['obo:RO_0002330', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002330', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002356', X, Y],O1,M1,_) \ fact(['obo:RO_0002295', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002295', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002461', X0, X1],O1,M1,_), fact(['obo:RO_0002465', X1, X2],O2,M2,_), fact(['obo:RO_0002461', X3, X2],O3,M3,_) \ fact(['obo:RO_0002440', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002461',O1,M1),('obo:RO_0002465',O2,M2),('obo:RO_0002461',O3,M3)],M), fact(['obo:RO_0002440', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002287', X, Y],O1,M1,_) \ fact(['obo:RO_0002286', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002286', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002578', X, X2],O1,M1,_), fact(['obo:RO_0002333', X2, X3],O2,M2,_), fact(['obo:RO_0002333', X, X1],O3,M3,_), fact(['obo:GO_0016301', X],O4,M4,_) \ fact(['obo:RO_0002447', X1, X3],add,_,U) <=> member(del,[O1,O2,O3,O4]) | check_pos_mark([('obo:RO_0002578',O1,M1),('obo:RO_0002333',O2,M2),('obo:RO_0002333',O3,M3),('obo:GO_0016301',O4,M4)],M), fact(['obo:RO_0002447', X1, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002629', X1, X2],O2,M2,_), fact(['obo:RO_0002333', X2, X3],O3,M3,_) \ fact(['obo:RO_0002450', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002629',O2,M2),('obo:RO_0002333',O3,M3)],M), fact(['obo:RO_0002450', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004025', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0004025', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0004025',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0004025', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002471', X, Y],O1,M1,_) \ fact(['obo:RO_0002438', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002438', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002614', X, Y],O1,M1,_) \ fact(['obo:RO_0002616', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002616', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002227', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002431', X, Y],O1,M1,_) \ fact(['obo:RO_0002264', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002264', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002480', X, Y],O1,M1,_) \ fact(['obo:RO_0002436', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002436', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002360', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002201', Y, X],O1,M1,_) \ fact(['obo:RO_0002200', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002200', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002200', Y, X],O1,M1,_) \ fact(['obo:RO_0002201', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002201', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002016', X, Y],O1,M1,_) \ fact(['obo:RO_0002336', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002336', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002008', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008505', X, Y],O1,M1,_) \ fact(['obo:RO_0002321', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002321', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002626', X, Y],O1,M1,_) \ fact(['obo:RO_0002574', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002574', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000052', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002314', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0000052',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002314', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002215', X0, X1],O1,M1,_), fact(['obo:RO_0002212', X1, X2],O2,M2,_) \ fact(['obo:RO_0002597', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002215',O1,M1),('obo:RO_0002212',O2,M2)],M), fact(['obo:RO_0002597', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002177', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011002', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002299', X, Y],O1,M1,_) \ fact(['obo:RO_0040036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0040036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002496', X0, X1],O1,M1,_), fact(['obo:RO_0002082', X1, X2],O2,M2,_) \ fact(['obo:RO_0002496', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002496',O1,M1),('obo:RO_0002082',O2,M2)],M), fact(['obo:RO_0002496', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011008', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002411', X0, X1],O1,M1,_), fact(['obo:RO_0002402', X1, X2],O2,M2,_) \ fact(['obo:RO_0002403', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002411',O1,M1),('obo:RO_0002402',O2,M2)],M), fact(['obo:RO_0002403', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002435', Y, X],O1,M1,_) \ fact(['obo:RO_0002435', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002435', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002428', X, Y],O1,M1,_) \ fact(['obo:RO_0002263', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002263', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002434', Y, X],O1,M1,_) \ fact(['obo:RO_0002434', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002434', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002427', X, Y],O1,M1,_) \ fact(['obo:RO_0002501', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002501', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002102', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002102', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002102',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002102', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002303', X, _],O1,M1,_) \ fact(['obo:CARO_0001010', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X0, X1],O1,M1,_), fact(['obo:RO_0002211', X1, X2],O2,M2,_) \ fact(['obo:RO_0002211', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002230',O1,M1),('obo:RO_0002211',O2,M2)],M), fact(['obo:RO_0002211', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002595', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002406', X0, X1],O1,M1,_), fact(['obo:RO_0002406', X1, X2],O2,M2,_) \ fact(['obo:RO_0002407', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002406',O1,M1),('obo:RO_0002406',O2,M2)],M), fact(['obo:RO_0002407', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0004842', X],O1,M1,_) \ fact(['obo:RO_0002482', X, X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002482', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002567', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002121', X, Y],O1,M1,_) \ fact(['obo:RO_0002110', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002110', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002302', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004033', X, Y],O1,M1,_) \ fact(['obo:RO_0002264', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002264', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002335', X, Y],O1,M1,_) \ fact(['obo:RO_0002334', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002334', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002554', X, Y],O1,M1,_) \ fact(['obo:RO_0002453', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002453', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002177', X, Y],O1,M1,_) \ fact(['obo:RO_0002567', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002567', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002576', _, X1],O1,M1,_) \ fact(['obo:CARO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002437', Y, X],O1,M1,_) \ fact(['obo:RO_0002437', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002437', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002345', X, Y],O1,M1,_) \ fact(['obo:RO_0002020', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002020', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009005', X, Y],O1,M1,_) \ fact(['obo:RO_0009001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0009001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002436', Y, X],O1,M1,_) \ fact(['obo:RO_0002436', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002436', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002132', X, _],O1,M1,_) \ fact(['obo:CARO_0001001', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001001', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002405', X, Y],O1,M1,_) \ fact(['obo:RO_0002404', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002404', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004011', X, Y],O1,M1,_) \ fact(['obo:RO_0004010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002111', X, Y],O1,M1,_) \ fact(['owl:topObjectProperty', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:topObjectProperty', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002312', X, Y],O1,M1,_) \ fact(['obo:RO_0002320', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002320', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002246', X, Y],O1,M1,_) \ fact(['obo:RO_0002206', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002206', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004025', X, Y],O1,M1,_) \ fact(['obo:RO_0004023', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004023', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002430', X, Y],O1,M1,_) \ fact(['obo:RO_0002428', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002428', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002510', X, Y],O1,M1,_) \ fact(['obo:RO_0002330', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002330', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002469', Y, X],O1,M1,_) \ fact(['obo:RO_0002457', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002457', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002457', Y, X],O1,M1,_) \ fact(['obo:RO_0002469', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002469', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002104', _, X1],O1,M1,_) \ fact(['obo:CARO_0000006', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000006', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002331', X0, X1],O1,M1,_), fact(['obo:RO_0002212', X1, X2],O2,M2,_) \ fact(['obo:RO_0002430', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002331',O1,M1),('obo:RO_0002212',O2,M2)],M), fact(['obo:RO_0002430', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002131', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002327', X0, X1],O1,M1,_), fact(['obo:RO_0002304', X1, X2],O2,M2,_) \ fact(['obo:RO_0004034', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002327',O1,M1),('obo:RO_0002304',O2,M2)],M), fact(['obo:RO_0004034', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002418', X, Y],O1,M1,_) \ fact(['obo:RO_0002501', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002501', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002330', X, _],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011008', X, Y],O1,M1,_) \ fact(['obo:RO_0011024', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011024', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002334', X, Y],O1,M1,_), fact(['obo:RO_0002334', Y, Z],O2,M2,_) \ fact(['obo:RO_0002334', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002334',O1,M1),('obo:RO_0002334',O2,M2)],M), fact(['obo:RO_0002334', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002253', X, Y],O1,M1,_) \ fact(['obo:RO_0002375', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002375', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002010', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0010002', _, X1],O1,M1,_) \ fact(['obo:BFO_0000031', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000031', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002092', Y, X],O1,M1,_) \ fact(['obo:RO_0002085', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002085', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002085', Y, X],O1,M1,_) \ fact(['obo:RO_0002092', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002092', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002220', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002453', X, Y],O1,M1,_) \ fact(['obo:RO_0002440', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002440', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002444', X, Y],O1,M1,_) \ fact(['obo:RO_0002443', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002443', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002507', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002509', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002507',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002509', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002533', X],O1,M1,_) \ fact(['obo:RO_0002532', X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002532', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004008', X, Y],O1,M1,_) \ fact(['obo:RO_0004007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002409', X0, X1],O1,M1,_), fact(['obo:RO_0002409', X1, X2],O2,M2,_) \ fact(['obo:RO_0002407', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002409',O1,M1),('obo:RO_0002409',O2,M2)],M), fact(['obo:RO_0002407', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002213', X, Y],O1,M1,_) \ fact(['obo:RO_0002211', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002211', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, Y],O1,M1,_) \ fact(['obo:RO_0002131', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002131', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002205', Y, X],O1,M1,_) \ fact(['obo:RO_0002204', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002204', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002204', Y, X],O1,M1,_) \ fact(['obo:RO_0002205', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002205', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002409', X, Y],O1,M1,_) \ fact(['obo:RO_0002212', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002212', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004010', _, X1],O1,M1,_) \ fact(['obo:BFO_0000017', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000017', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002322', _, X1],O1,M1,_) \ fact(['obo:ENVO_01000254', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:ENVO_01000254', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002378', X, Y],O1,M1,_) \ fact(['obo:RO_0002376', Y, X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002376', Y, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002482', X, Y],O1,M1,_) \ fact(['obo:RO_0002564', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002564', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002625', X, Y],O1,M1,_) \ fact(['obo:RO_0002445', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002445', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000059', X0, X1],O1,M1,_), fact(['obo:RO_0000053', X1, X2],O2,M2,_) \ fact(['obo:RO_0010002', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0000059',O1,M1),('obo:RO_0000053',O2,M2)],M), fact(['obo:RO_0010002', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002497', X0, X1],O1,M1,_), fact(['obo:BFO_0000063', X1, X2],O2,M2,_) \ fact(['obo:RO_0002497', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002497',O1,M1),('obo:BFO_0000063',O2,M2)],M), fact(['obo:RO_0002497', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004015', Y, X],O1,M1,_) \ fact(['obo:RO_0004005', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004005', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004005', Y, X],O1,M1,_) \ fact(['obo:RO_0004015', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004015', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002491', X, Y],O1,M1,_) \ fact(['obo:RO_0002488', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002488', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002466', X, Y],O1,M1,_) \ fact(['obo:RO_0002465', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002465', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002244', X, _],O1,M1,_) \ fact(['obo:RO_0002310', X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002310', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0003001', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002224', X0, X1],O1,M1,_), fact(['obo:BFO_0000066', X1, X2],O2,M2,_) \ fact(['obo:RO_0002231', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002224',O1,M1),('obo:BFO_0000066',O2,M2)],M), fact(['obo:RO_0002231', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004016', Y, X],O1,M1,_) \ fact(['obo:RO_0004006', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004006', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004006', Y, X],O1,M1,_) \ fact(['obo:RO_0004016', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004016', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0010001', X, _],O1,M1,_) \ fact(['obo:BFO_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002531', X, Y],O1,M1,_) \ fact(['obo:RO_0002528', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002528', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:RO_0002215', X1, X2],O2,M2,_) \ fact(['obo:RO_0002329', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:RO_0002215',O2,M2)],M), fact(['obo:RO_0002329', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002010', X, Y],O1,M1,_) \ fact(['obo:RO_0002418', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002418', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004000', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002216', X, Y],O1,M1,_) \ fact(['obo:RO_0002328', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002328', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002523', X, Y],O1,M1,_) \ fact(['obo:RO_0002514', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002514', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0008505', X, _],O1,M1,_) \ fact(['obo:CARO_0001010', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001010', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002236', X, Y],O1,M1,_) \ fact(['obo:RO_0002444', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002444', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011004', X, Y],O1,M1,_) \ fact(['obo:RO_0011002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002409', X, Y],O1,M1,_), fact(['obo:RO_0002409', Y, Z],O2,M2,_) \ fact(['obo:RO_0002409', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002409',O1,M1),('obo:RO_0002409',O2,M2)],M), fact(['obo:RO_0002409', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004014', Y, X],O1,M1,_) \ fact(['obo:RO_0004004', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004004', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004004', Y, X],O1,M1,_) \ fact(['obo:RO_0004014', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004014', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002203', Y, X],O1,M1,_) \ fact(['obo:RO_0002202', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002202', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002202', Y, X],O1,M1,_) \ fact(['obo:RO_0002203', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002203', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002325', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002243', X, Y],O1,M1,_) \ fact(['obo:RO_0002244', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002244', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002026', X, Y],O1,M1,_) \ fact(['obo:RO_0002323', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002323', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001022', X, Y],O1,M1,_) \ fact(['obo:RO_0003302', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0003302', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004026', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002528', X, Y],O1,M1,_) \ fact(['obo:RO_0002527', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002527', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002012', _, X1],O1,M1,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004025', X, _],O1,M1,_) \ fact(['obo:OGMS_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:OGMS_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002019', X, _],O1,M1,_) \ fact(['obo:GO_0004872', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0004872', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002497', X, Y],O1,M1,_) \ fact(['obo:RO_0002487', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002487', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009501', X, Y],O1,M1,_) \ fact(['obo:RO_0002410', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002410', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011004', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0009004', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011013', _, X1],O1,M1,_) \ fact(['obo:BFO_0000040', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002331', X0, X1],O1,M1,_), fact(['obo:RO_0002213', X1, X2],O2,M2,_) \ fact(['obo:RO_0002429', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002331',O1,M1),('obo:RO_0002213',O2,M2)],M), fact(['obo:RO_0002429', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002407', X, Y],O1,M1,_), fact(['obo:RO_0002407', Y, Z],O2,M2,_) \ fact(['obo:RO_0002407', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002407',O1,M1),('obo:RO_0002407',O2,M2)],M), fact(['obo:RO_0002407', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002291', X, Y],O1,M1,_) \ fact(['obo:RO_0002206', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002206', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002514', _, X1],O1,M1,_) \ fact(['obo:RO_0002532', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002532', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002623', X, Y],O1,M1,_) \ fact(['obo:RO_0002619', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002619', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004012', Y, X],O1,M1,_) \ fact(['obo:RO_0004002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004002', Y, X],O1,M1,_) \ fact(['obo:RO_0004012', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004012', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002111', X, _],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002334', X, Y],O1,M1,_) \ fact(['obo:RO_0002427', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002427', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002131', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:RO_0002131', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002131',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:RO_0002131', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002202', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002206', _, X1],O1,M1,_) \ fact(['obo:CARO_0000006', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000006', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004013', Y, X],O1,M1,_) \ fact(['obo:RO_0004003', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004003', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0004003', Y, X],O1,M1,_) \ fact(['obo:RO_0004013', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0004013', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002519', X, Y],O1,M1,_) \ fact(['obo:RO_0002525', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002525', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0011013', X, Y],O1,M1,_) \ fact(['obo:RO_0011004', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0011004', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002258', X0, X1],O1,M1,_), fact(['obo:RO_0002496', X1, X2],O2,M2,_) \ fact(['obo:RO_0002496', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002258',O1,M1),('obo:RO_0002496',O2,M2)],M), fact(['obo:RO_0002496', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002179', X, Y],O1,M1,_) \ fact(['obo:RO_0002170', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002170', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002221', X, Y],O1,M1,_) \ fact(['obo:RO_0002220', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002220', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0003824', X],O1,M1,_) \ fact(['obo:GO_0003674', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0003674', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0016874', X],O1,M1,_) \ fact(['obo:GO_0003824', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0003824', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0016740', X],O1,M1,_) \ fact(['obo:GO_0003824', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0003824', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0019787', X],O1,M1,_) \ fact(['obo:GO_0016881', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0016881', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0004842', X],O1,M1,_) \ fact(['obo:GO_0019787', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0019787', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0016301', X],O1,M1,_) \ fact(['obo:GO_0016772', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0016772', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0016879', X],O1,M1,_) \ fact(['obo:GO_0016874', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0016874', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0016772', X],O1,M1,_) \ fact(['obo:GO_0016740', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0016740', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0016881', X],O1,M1,_) \ fact(['obo:GO_0016879', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0016879', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000053', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000053', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000053', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000073', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000022', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000022', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000004', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000046', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000046', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000046', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000026', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000034', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000034', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000060', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000060', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000060', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000007', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000024', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000018', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000047', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000052', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000052', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000052', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000061', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000074', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000066', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000066', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000033', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000004', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000004', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000051', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000029', X, Y],O1,M1,_), fact(['obo:RO_HOM0000030', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000029',O1,M1),('obo:RO_HOM0000030',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000045', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000045', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000045', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000037', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000037', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000037', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000029', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000028', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000028', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000057', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000058', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000058', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000044', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000044', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000044', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000036', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000074', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000003', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000003', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000050', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000043', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000043', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000043', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000042', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000042', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000042', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000029', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000029', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000029', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000046', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000047', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000047', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000036', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000028', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000028', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000028', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000027', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000027', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000027', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000062', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000013', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000032', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000029', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000029', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000034', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000034', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000034', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000073', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000073', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000073', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000023', X, Y],O1,M1,_), fact(['obo:RO_HOM0000024', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000023',O1,M1),('obo:RO_HOM0000024',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000027', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000066', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000066', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000071', X, Y],O1,M1,_), fact(['obo:RO_HOM0000072', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000071',O1,M1),('obo:RO_HOM0000072',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000066', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000066', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000066', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000012', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000062', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000065', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000065', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000031', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000029', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000029', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000044', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000003', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000003', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000058', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000058', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000058', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000072', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000072', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000072', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000052', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000030', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000030', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000065', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000065', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000065', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000057', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000071', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000071', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000071', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000034', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000037', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000037', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000063', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000063', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000063', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000044', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000005', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000005', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000049', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000049', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000049', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000020', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000062', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000062', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000062', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000060', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000012', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000054', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000062', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000062', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000048', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000048', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000048', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000065', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000050', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000055', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000055', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000055', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000020', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000019', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000019', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000047', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000047', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000047', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000061', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000061', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000061', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000015', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000006', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000054', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000054', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000054', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000001', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000063', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000054', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000006', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000006', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000005', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000005', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000005', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000011', X, Y],O1,M1,_), fact(['obo:RO_HOM0000017', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000011',O1,M1),('obo:RO_HOM0000017',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000012', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000012', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000012', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000004', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000004', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000004', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000066', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000008', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000008', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000011', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000003', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000003', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000003', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000037', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000049', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000010', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000010', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000010', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000048', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000036', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000036', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000002', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000043', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000055', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000006', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000075', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000034', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000023', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000017', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000049', X, Y],O1,M1,_), fact(['obo:RO_HOM0000050', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000049',O1,M1),('obo:RO_HOM0000050',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000069', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000069', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000069', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000003', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000014', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000006', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000011', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000058', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000003', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000003', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000075', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000075', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000075', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000009', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000068', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000068', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000068', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000001', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000051', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000029', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000029', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000060', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000019', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000019', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000025', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000034', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000034', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000074', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000074', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000074', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000072', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000008', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000008', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000000', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000026', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000026', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000026', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000002', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000071', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000006', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000016', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000006', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000033', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000033', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000033', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000053', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000025', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000025', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000025', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000010', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000006', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000019', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000019', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000019', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000032', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000032', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000032', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000031', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000031', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000031', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000019', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000008', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000024', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000024', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000024', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000018', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000042', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000030', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000030', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000030', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000022', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000017', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000045', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000016', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000016', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000016', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000016', X, Y],O1,M1,_), fact(['obo:RO_HOM0000062', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000016',O1,M1),('obo:RO_HOM0000062',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000009', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000009', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000009', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000023', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000023', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000023', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000001', X, Y],O1,M1,_), fact(['obo:RO_HOM0000002', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000001',O1,M1),('obo:RO_HOM0000002',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000015', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000015', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000015', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000057', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000005', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000005', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000005', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000042', X, Y],O1,M1,_), fact(['obo:RO_HOM0000043', X, Y],O2,M2,_) \ fact(['owl:Nothing', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000042',O1,M1),('obo:RO_HOM0000043',O2,M2)],M), fact(['owl:Nothing', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000022', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000022', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000022', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000068', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000018', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000018', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000030', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000028', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000028', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000014', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000014', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000014', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000008', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000008', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000008', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000069', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000011', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000028', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000008', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000008', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000020', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000020', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000020', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000013', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000013', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000013', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000007', Y, X],O1,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000007', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000048', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000017', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000073', X, Y],O1,M1,_) \ fact(['obo:RO_HOM0000053', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_HOM0000053', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002090', Y, X],O1,M1,_) \ fact(['obo:RO_0002087', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002087', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002087', Y, X],O1,M1,_) \ fact(['obo:RO_0002090', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002090', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002093', Y, X],O1,M1,_) \ fact(['obo:RO_0002084', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002084', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002084', Y, X],O1,M1,_) \ fact(['obo:RO_0002093', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002093', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002087', X, Y],O1,M1,_) \ fact(['obo:BFO_0000062', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000062', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002084', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002081', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000062', X, Y],O1,M1,_), fact(['obo:BFO_0000062', Y, Z],O2,M2,_) \ fact(['obo:BFO_0000062', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000062',O1,M1),('obo:BFO_0000062',O2,M2)],M), fact(['obo:BFO_0000062', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000063', _, X1],O1,M1,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000063', Y, X],O1,M1,_) \ fact(['obo:BFO_0000062', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000062', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000062', Y, X],O1,M1,_) \ fact(['obo:BFO_0000063', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000063', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', Y, X],O1,M1,_) \ fact(['obo:RO_0002229', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002229', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002229', Y, X],O1,M1,_) \ fact(['obo:RO_0002230', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002230', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002092', X0, X1],O1,M1,_), fact(['obo:BFO_0000062', X1, X2],O2,M2,_) \ fact(['obo:BFO_0000062', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002092',O1,M1),('obo:BFO_0000062',O2,M2)],M), fact(['obo:BFO_0000062', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002091', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002083', X, Y],O1,M1,_), fact(['obo:RO_0002083', Y, Z],O2,M2,_) \ fact(['obo:RO_0002083', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002083',O1,M1),('obo:RO_0002083',O2,M2)],M), fact(['obo:RO_0002083', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002230', X, Y],O1,M1,_), fact(['obo:RO_0002230', Y, Z],O2,M2,_) \ fact(['obo:RO_0002230', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002230',O1,M1),('obo:RO_0002230',O2,M2)],M), fact(['obo:RO_0002230', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002091', X0, X1],O1,M1,_), fact(['obo:BFO_0000062', X1, X2],O2,M2,_) \ fact(['obo:BFO_0000062', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002091',O1,M1),('obo:BFO_0000062',O2,M2)],M), fact(['obo:BFO_0000062', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002091', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002089', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002224', X, Y],O1,M1,_), fact(['obo:RO_0002224', Y, Z],O2,M2,_) \ fact(['obo:RO_0002224', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002224',O1,M1),('obo:RO_0002224',O2,M2)],M), fact(['obo:RO_0002224', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002086', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002082', X, Y],O1,M1,_), fact(['obo:RO_0002082', Y, Z],O2,M2,_) \ fact(['obo:RO_0002082', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002082',O1,M1),('obo:RO_0002082',O2,M2)],M), fact(['obo:RO_0002082', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002222', _, X1],O1,M1,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002092', X, Y],O1,M1,_) \ fact(['obo:RO_0002093', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002093', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002089', X, Y],O1,M1,_), fact(['obo:RO_0002089', Y, Z],O2,M2,_) \ fact(['obo:RO_0002089', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002089',O1,M1),('obo:RO_0002089',O2,M2)],M), fact(['obo:RO_0002089', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000063', X, Y],O1,M1,_), fact(['obo:BFO_0000063', Y, Z],O2,M2,_) \ fact(['obo:BFO_0000063', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000063',O1,M1),('obo:BFO_0000063',O2,M2)],M), fact(['obo:BFO_0000063', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000062', _, X1],O1,M1,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002093', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002093', X0, X1],O1,M1,_), fact(['obo:BFO_0000062', X1, X2],O2,M2,_) \ fact(['obo:RO_0002086', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002093',O1,M1),('obo:BFO_0000062',O2,M2)],M), fact(['obo:RO_0002086', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002224', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002088', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002090', X, Y],O1,M1,_) \ fact(['obo:BFO_0000063', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000063', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000063', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000062', X, Y],O1,M1,_) \ fact(['obo:RO_0002086', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002086', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002091', _, X1],O1,M1,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002083', X, Y],O1,M1,_) \ fact(['obo:RO_0002081', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002081', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002229', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002091', X0, X1],O1,M1,_), fact(['obo:BFO_0000060', X1, X2],O2,M2,_) \ fact(['obo:RO_0002089', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002091',O1,M1),('obo:BFO_0000060',O2,M2)],M), fact(['obo:RO_0002089', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000060', X, Y],O1,M1,_), fact(['obo:BFO_0000060', Y, Z],O2,M2,_) \ fact(['obo:BFO_0000060', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000060',O1,M1),('obo:BFO_0000060',O2,M2)],M), fact(['obo:BFO_0000060', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002223', X, Y],O1,M1,_) \ fact(['obo:RO_0002222', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002222', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002224', Y, X],O1,M1,_) \ fact(['obo:RO_0002223', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002223', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002223', Y, X],O1,M1,_) \ fact(['obo:RO_0002224', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002224', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002082', X, Y],O1,M1,_) \ fact(['obo:RO_0002081', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002081', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000062', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002092', X, Y],O1,M1,_), fact(['obo:RO_0002092', Y, Z],O2,M2,_) \ fact(['obo:RO_0002092', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002092',O1,M1),('obo:RO_0002092',O2,M2)],M), fact(['obo:RO_0002092', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002222', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002091', Y, X],O1,M1,_) \ fact(['obo:RO_0002088', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002088', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002088', Y, X],O1,M1,_) \ fact(['obo:RO_0002091', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002091', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002086', X, Y],O1,M1,_), fact(['obo:RO_0002086', Y, Z],O2,M2,_) \ fact(['obo:RO_0002086', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002086',O1,M1),('obo:RO_0002086',O2,M2)],M), fact(['obo:RO_0002086', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', X, Y],O1,M1,_), fact(['obo:RO_0001025', Y, Z],O2,M2,_) \ fact(['obo:RO_0001025', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0001025',O1,M1),('obo:RO_0001025',O2,M2)],M), fact(['obo:RO_0001025', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000057', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000086', X, Y],O1,M1,_) \ fact(['obo:RO_0000053', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000053', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000067', Y, X],O1,M1,_) \ fact(['obo:BFO_0000066', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000066', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000066', Y, X],O1,M1,_) \ fact(['obo:BFO_0000067', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000067', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000055', _, X1],O1,M1,_) \ fact(['obo:BFO_0000017', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000017', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000079', X, _],O1,M1,_) \ fact(['obo:BFO_0000034', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000034', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000079', X, Y],O1,M1,_) \ fact(['obo:RO_0000052', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000052', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000087', _, X1],O1,M1,_) \ fact(['obo:BFO_0000023', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000023', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000080', X, Y],O1,M1,_) \ fact(['obo:RO_0000052', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000052', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, Y],O1,M1,_), fact(['obo:BFO_0000050', Y, Z],O2,M2,_) \ fact(['obo:BFO_0000050', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:BFO_0000050', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X0, X1],O1,M1,_), fact(['obo:BFO_0000066', X1, X2],O2,M2,_) \ fact(['obo:BFO_0000066', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000066',O2,M2)],M), fact(['obo:BFO_0000066', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000085', _, X1],O1,M1,_) \ fact(['obo:BFO_0000034', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000034', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000002', X],O1,M1,_), fact(['obo:BFO_0000050', X, X1],O2,M2,_), fact(['obo:BFO_0000003', X1],O3,M3,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:BFO_0000002',O1,M1),('obo:BFO_0000050',O2,M2),('obo:BFO_0000003',O3,M3)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000003', X],O1,M1,_), fact(['obo:BFO_0000050', X, X1],O2,M2,_), fact(['obo:BFO_0000002', X1],O3,M3,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:BFO_0000003',O1,M1),('obo:BFO_0000050',O2,M2),('obo:BFO_0000002',O3,M3)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000055', Y, X],O1,M1,_) \ fact(['obo:BFO_0000054', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000054', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000054', Y, X],O1,M1,_) \ fact(['obo:BFO_0000055', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000055', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000056', X, _],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000066', X, _],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000058', X, _],O1,M1,_) \ fact(['obo:BFO_0000031', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000031', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002350', X, Y],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', Y, X],O1,M1,_) \ fact(['obo:RO_0001015', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001015', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001015', Y, X],O1,M1,_) \ fact(['obo:RO_0001025', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001025', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001015', X, Y],O1,M1,_), fact(['obo:RO_0001015', Y, Z],O2,M2,_) \ fact(['obo:RO_0001015', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0001015',O1,M1),('obo:RO_0001015',O2,M2)],M), fact(['obo:RO_0001015', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000086', Y, X],O1,M1,_) \ fact(['obo:RO_0000080', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000080', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000080', Y, X],O1,M1,_) \ fact(['obo:RO_0000086', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000086', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000054', _, X1],O1,M1,_) \ fact(['obo:BFO_0000015', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000092', X, Y],O1,M1,_) \ fact(['obo:RO_0000052', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000052', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000055', X, _],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000056', _, X1],O1,M1,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000066', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000057', Y, X],O1,M1,_) \ fact(['obo:RO_0000056', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000056', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000056', Y, X],O1,M1,_) \ fact(['obo:RO_0000057', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000057', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002351', X, X],O1,M1,_) \ fact(['owl:Nothing', X, X],add,_,U) <=> member(del,[O1]) | fact(['owl:Nothing', X, X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002351', X, Y],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000087', Y, X],O1,M1,_) \ fact(['obo:RO_0000081', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000081', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000081', Y, X],O1,M1,_) \ fact(['obo:RO_0000087', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000087', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002002', X, _],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002002', Y, X],O1,M1,_) \ fact(['obo:RO_0002000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002000', Y, X],O1,M1,_) \ fact(['obo:RO_0002002', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002002', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002351', Y, X],O1,M1,_) \ fact(['obo:RO_0002350', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002350', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002350', Y, X],O1,M1,_) \ fact(['obo:RO_0002351', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002351', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000091', X, Y],O1,M1,_) \ fact(['obo:RO_0000053', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000053', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000081', X, Y],O1,M1,_) \ fact(['obo:RO_0000052', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000052', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000085', X, Y],O1,M1,_) \ fact(['obo:RO_0000053', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000053', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000092', Y, X],O1,M1,_) \ fact(['obo:RO_0000091', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000091', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000091', Y, X],O1,M1,_) \ fact(['obo:RO_0000092', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000092', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000085', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000086', _, X1],O1,M1,_) \ fact(['obo:BFO_0000019', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000019', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000006', X],O1,M1,_), fact(['obo:RO_0001025', X, X1],O2,M2,_) \ fact(['owl:Nothing', X, X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000006',O1,M1),('obo:RO_0001025',O2,M2)],M), fact(['owl:Nothing', X, X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000053', _, X1],O1,M1,_) \ fact(['obo:BFO_0000020', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000085', Y, X],O1,M1,_) \ fact(['obo:RO_0000079', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000079', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000079', Y, X],O1,M1,_) \ fact(['obo:RO_0000085', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000085', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000066', X0, X1],O1,M1,_), fact(['obo:BFO_0000050', X1, X2],O2,M2,_) \ fact(['obo:BFO_0000066', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000066',O1,M1),('obo:BFO_0000050',O2,M2)],M), fact(['obo:BFO_0000066', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000059', Y, X],O1,M1,_) \ fact(['obo:RO_0000058', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000058', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000058', Y, X],O1,M1,_) \ fact(['obo:RO_0000059', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000059', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000087', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002002', _, X1],O1,M1,_) \ fact(['obo:BFO_0000141', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000141', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000091', _, X1],O1,M1,_) \ fact(['obo:BFO_0000016', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000016', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', Y, X],O1,M1,_) \ fact(['obo:BFO_0000050', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000050', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', Y, X],O1,M1,_) \ fact(['obo:BFO_0000051', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000051', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000051', X, Y],O1,M1,_), fact(['obo:BFO_0000051', Y, Z],O2,M2,_) \ fact(['obo:BFO_0000051', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000051',O1,M1),('obo:BFO_0000051',O2,M2)],M), fact(['obo:BFO_0000051', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000059', X, _],O1,M1,_) \ fact(['obo:BFO_0000020', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000053', Y, X],O1,M1,_) \ fact(['obo:RO_0000052', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000052', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000052', Y, X],O1,M1,_) \ fact(['obo:RO_0000053', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000053', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000057', _, X1],O1,M1,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000058', _, X1],O1,M1,_) \ fact(['obo:BFO_0000020', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000059', _, X1],O1,M1,_) \ fact(['obo:BFO_0000031', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000031', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001001', Y, X],O1,M1,_) \ fact(['obo:RO_0001000', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001000', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001000', Y, X],O1,M1,_) \ fact(['obo:RO_0001001', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0001001', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000054', X, _],O1,M1,_) \ fact(['obo:BFO_0000017', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000017', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0001025', _, X1],O1,M1,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000006', X1],O1,M1,_), fact(['obo:RO_0001025', X, X1],O2,M2,_) \ fact(['owl:Nothing', X, X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000006',O1,M1),('obo:RO_0001025',O2,M2)],M), fact(['owl:Nothing', X, X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000087', X, Y],O1,M1,_) \ fact(['obo:RO_0000053', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000053', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0000091', X, _],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0001199', X],O1,M1,_) \ fact(['obo:PATO_0000052', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0000052', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0000052', X],O1,M1,_) \ fact(['obo:PATO_0000051', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0000051', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0000051', X],O1,M1,_) \ fact(['obo:PATO_0001241', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0001241', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0002124', X],O1,M1,_) \ fact(['obo:PATO_0000141', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0000141', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0001241', X],O1,M1,_) \ fact(['obo:PATO_0000001', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0000001', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0000141', X],O1,M1,_) \ fact(['obo:PATO_0000051', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0000051', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0016020', X],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0042734', X],O1,M1,_) \ fact(['obo:GO_0044456', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044456', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0005634', X],O1,M1,_) \ fact(['obo:GO_0044464', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044464', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0043005', X],O1,M1,_) \ fact(['obo:GO_0042995', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0042995', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0045211', X],O1,M1,_) \ fact(['obo:GO_0044456', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044456', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0044456', X],O1,M1,_) \ fact(['obo:GO_0044464', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044464', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0044464', X],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0042995', X],O1,M1,_) \ fact(['obo:GO_0044464', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044464', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0045211', X],O1,M1,_) \ fact(['obo:GO_0016020', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0016020', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0030424', X],O1,M1,_) \ fact(['obo:GO_0043005', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0043005', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0042734', X],O1,M1,_) \ fact(['obo:GO_0016020', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0016020', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0008150', X],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0030425', X],O1,M1,_) \ fact(['obo:GO_0043005', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0043005', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0045202', X],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000040', X],O1,M1,_), fact(['obo:BFO_0000141', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000040',O1,M1),('obo:BFO_0000141',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000017', X],O1,M1,_), fact(['obo:BFO_0000019', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000017',O1,M1),('obo:BFO_0000019',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000002', X],O1,M1,_), fact(['obo:BFO_0000003', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000002',O1,M1),('obo:BFO_0000003',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000016', X],O1,M1,_), fact(['obo:BFO_0000023', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000016',O1,M1),('obo:BFO_0000023',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000004', X],O1,M1,_), fact(['obo:BFO_0000020', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000004',O1,M1),('obo:BFO_0000020',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000004', X],O1,M1,_), fact(['obo:BFO_0000031', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000004',O1,M1),('obo:BFO_0000031',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000020', X],O1,M1,_), fact(['obo:BFO_0000031', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000020',O1,M1),('obo:BFO_0000031',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0000006', X],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CL_0000000', X],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0030000', X],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0000000', X],O1,M1,_) \ fact(['obo:CARO_0030000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0030000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0000011', X],O1,M1,_) \ fact(['obo:CARO_0010000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0010000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0010000', X],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0001001', X],O1,M1,_) \ fact(['obo:CARO_0001000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0001000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0000011', X],O1,M1,_) \ fact(['obo:RO_0002577', X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002577', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0000001', X],O1,M1,_) \ fact(['obo:BFO_0000020', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CL_0000540', X],O1,M1,_) \ fact(['obo:CL_0000000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CL_0000000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:ENVO_00000428', X],O1,M1,_) \ fact(['obo:ENVO_01000254', X],add,_,U) <=> member(del,[O1]) | fact(['obo:ENVO_01000254', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0002009', X],O1,M1,_) \ fact(['obo:PATO_0000052', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0000052', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002207', X, X1],O1,M1,_), fact(['obo:CL_0000000', X],O2,M2,_) \ fact(['obo:CL_0000000', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002207',O1,M1),('obo:CL_0000000',O2,M2)],M), fact(['obo:CL_0000000', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:ENVO_01000254', X],O1,M1,_) \ fact(['obo:RO_0002577', X],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0002577', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002207', X, X1],O1,M1,_), fact(['obo:CARO_0010000', X],O2,M2,_) \ fact(['obo:CARO_0010000', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_0002207',O1,M1),('obo:CARO_0010000',O2,M2)],M), fact(['obo:CARO_0010000', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:OGMS_0000031', X],O1,M1,_) \ fact(['obo:BFO_0000016', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000016', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:UPHENO_0001001', X],O1,M1,_) \ fact(['obo:PATO_0000001', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0000001', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0001010', X],O1,M1,_) \ fact(['obo:BFO_0000040', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000040', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0001000', X],O1,M1,_) \ fact(['obo:CARO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0000006', X],O1,M1,_) \ fact(['obo:CARO_0000000', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000000', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0000007', X],O1,M1,_) \ fact(['obo:BFO_0000141', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000141', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:CARO_0000003', X],O1,M1,_) \ fact(['obo:CARO_0000006', X],add,_,U) <=> member(del,[O1]) | fact(['obo:CARO_0000006', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0000402', X],O1,M1,_) \ fact(['obo:PATO_0002009', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0002009', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0000052', X],O1,M1,_) \ fact(['obo:PATO_0000051', X],add,_,U) <=> member(del,[O1]) | fact(['obo:PATO_0000051', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:PATO_0000051', X],O1,M1,_) \ fact(['obo:BFO_0000019', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000019', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0003674', X],O1,M1,_) \ fact(['obo:BFO_0000015', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000015', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002262', X, Y],O1,M1,_) \ fact(['obo:RO_0000087', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000087', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002260', X, Y],O1,M1,_) \ fact(['obo:RO_0000087', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000087', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:RO_0002261', X, Y],O1,M1,_) \ fact(['obo:RO_0000087', X, Y],add,_,U) <=> member(del,[O1]) | fact(['obo:RO_0000087', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000019', X],O1,M1,_) \ fact(['obo:BFO_0000020', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000016', X],O1,M1,_) \ fact(['obo:BFO_0000017', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000017', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000031', X],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000015', X],O1,M1,_) \ fact(['obo:BFO_0000003', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000003', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000020', X],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000004', X],O1,M1,_) \ fact(['obo:BFO_0000002', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000002', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000017', X],O1,M1,_) \ fact(['obo:BFO_0000020', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000020', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000141', X],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000040', X],O1,M1,_) \ fact(['obo:BFO_0000004', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000004', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000005', X],O1,M1,_) \ fact(['go:ObsoleteClass', X],add,_,U) <=> member(del,[O1]) | fact(['go:ObsoleteClass', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000034', X],O1,M1,_) \ fact(['obo:BFO_0000016', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000016', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000006', X],O1,M1,_) \ fact(['obo:BFO_0000141', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000141', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000023', X],O1,M1,_) \ fact(['obo:BFO_0000017', X],add,_,U) <=> member(del,[O1]) | fact(['obo:BFO_0000017', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0085031', X],O1,M1,_) \ fact(['obo:GO_0044403', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044403', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0051705', X],O1,M1,_) \ fact(['obo:GO_0007610', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0007610', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0051704', X],O1,M1,_) \ fact(['obo:GO_0008150', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0008150', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0007610', X],O1,M1,_) \ fact(['obo:GO_0050896', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0050896', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0051816', X],O1,M1,_) \ fact(['obo:GO_0007631', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0007631', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0044403', X],O1,M1,_) \ fact(['obo:GO_0044419', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044419', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0044419', X],O1,M1,_) \ fact(['obo:GO_0051704', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0051704', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0072519', X],O1,M1,_) \ fact(['obo:GO_0044403', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044403', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0007631', X],O1,M1,_) \ fact(['obo:GO_0007610', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0007610', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0050896', X],O1,M1,_) \ fact(['obo:GO_0008150', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0008150', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0051702', X],O1,M1,_) \ fact(['obo:GO_0044419', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044419', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0085030', X],O1,M1,_) \ fact(['obo:GO_0044403', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0044403', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0051850', X],O1,M1,_) \ fact(['obo:GO_0051702', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0051702', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0051705', X],O1,M1,_) \ fact(['obo:GO_0051704', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0051704', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0051850', X],O1,M1,_) \ fact(['obo:GO_0051816', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0051816', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:GO_0051850', X],O1,M1,_) \ fact(['obo:GO_0051705', X],add,_,U) <=> member(del,[O1]) | fact(['obo:GO_0051705', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, X1],O1,M1,_), fact(['obo:BFO_0000020', X],O2,M2,_) \ fact(['obo:BFO_0000020', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000020',O2,M2)],M), fact(['obo:BFO_0000020', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, X1],O1,M1,_), fact(['obo:BFO_0000031', X],O2,M2,_) \ fact(['obo:BFO_0000031', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000031',O2,M2)],M), fact(['obo:BFO_0000031', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000000', X, X1],O1,M1,_), fact(['obo:BFO_0000002', X],O2,M2,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000000',O1,M1),('obo:BFO_0000002',O2,M2)],M), fact(['obo:BFO_0000002', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, X1],O1,M1,_), fact(['obo:BFO_0000003', X],O2,M2,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000003',O2,M2)],M), fact(['obo:BFO_0000003', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, X1],O1,M1,_), fact(['obo:BFO_0000002', X],O2,M2,_) \ fact(['obo:BFO_0000002', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000002',O2,M2)],M), fact(['obo:BFO_0000002', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:RO_HOM0000000', X, X1],O1,M1,_), fact(['obo:BFO_0000003', X],O2,M2,_) \ fact(['obo:BFO_0000003', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:RO_HOM0000000',O1,M1),('obo:BFO_0000003',O2,M2)],M), fact(['obo:BFO_0000003', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, X1],O1,M1,_), fact(['obo:BFO_0000004', X],O2,M2,_) \ fact(['obo:BFO_0000004', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000004',O2,M2)],M), fact(['obo:BFO_0000004', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, X1],O1,M1,_), fact(['obo:BFO_0000017', X],O2,M2,_) \ fact(['obo:BFO_0000017', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000017',O2,M2)],M), fact(['obo:BFO_0000017', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000050', X, X1],O1,M1,_), fact(['obo:BFO_0000019', X],O2,M2,_) \ fact(['obo:BFO_0000019', X1],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('obo:BFO_0000050',O1,M1),('obo:BFO_0000019',O2,M2)],M), fact(['obo:BFO_0000019', X1],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000141', X],O1,M1,_), fact(['obo:BFO_0000051', X, X1],O2,M2,_), fact(['obo:BFO_0000040', X1],O3,M3,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:BFO_0000141',O1,M1),('obo:BFO_0000051',O2,M2),('obo:BFO_0000040',O3,M3)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['obo:BFO_0000040', X],O1,M1,_), fact(['obo:BFO_0000050', X, X1],O2,M2,_), fact(['obo:BFO_0000141', X1],O3,M3,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('obo:BFO_0000040',O1,M1),('obo:BFO_0000050',O2,M2),('obo:BFO_0000141',O3,M3)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact(['obo:RO_0003000', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002490', X, Y],add,M1,_) \ fact(['obo:RO_0002487', X, Y],del,_,U) <=> true | fact(['obo:RO_0002487', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001020', X, Y],add,M1,_) \ fact(['obo:RO_0003302', X, Y],del,_,U) <=> true | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002178', X, Y],add,M1,_) \ fact(['obo:RO_0002170', X, Y],del,_,U) <=> true | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002203', X, Y],add,M1,_) \ fact(['obo:RO_0002286', X, Y],del,_,U) <=> true | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002372', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X0, X1],add,M1,_), fact(['obo:RO_0002234', X1, X2],add,M2,_) \ fact(['obo:RO_0002234', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002234', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002506', X, _],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002496', X, Y],add,M1,_) \ fact(['obo:RO_0002487', X, Y],del,_,U) <=> true | fact(['obo:RO_0002487', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002353', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002256', X, Y],add,M1,_) \ fact(['obo:RO_0002258', X, Y],del,_,U) <=> true | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002443', X, Y],add,M1,_) \ fact(['obo:RO_0002440', X, Y],del,_,U) <=> true | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002522', X, Y],add,M1,_) \ fact(['obo:RO_0002514', X, Y],del,_,U) <=> true | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009501', X0, X1],add,M1,_), fact(['obo:RO_0002233', X1, X2],add,M2,_) \ fact(['obo:RO_0004028', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004028', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002248', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002295', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011013', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002242', X, Y],add,M1,_) \ fact(['obo:RO_0002244', X, Y],del,_,U) <=> true | fact(['obo:RO_0002244', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002595', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002448', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002235', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002212', X, Y],add,M1,_) \ fact(['obo:RO_0002211', X, Y],del,_,U) <=> true | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002020', X, Y],add,M1,_) \ fact(['obo:RO_0002313', X, Y],del,_,U) <=> true | fact(['obo:RO_0002313', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X0, X1],add,M1,_), fact(['obo:RO_0002212', X1, X2],add,M2,_) \ fact(['obo:RO_0002212', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002212', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002110', X, Y],add,M1,_) \ fact(['obo:RO_0002130', X, Y],del,_,U) <=> true | fact(['obo:RO_0002130', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002134', X, _],add,M1,_) \ fact(['obo:CARO_0001001', X],del,_,U) <=> true | fact(['obo:CARO_0001001', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002009', X, _],add,M1,_) \ fact(['obo:CL_0000000', X],del,_,U) <=> true | fact(['obo:CL_0000000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002017', X, Y],add,M1,_) \ fact(['obo:RO_0002018', X, Y],del,_,U) <=> true | fact(['obo:RO_0002018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002101', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002104', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002179', X, X1],add,M1,_), fact(['obo:CARO_0000006', X],add,M2,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:CARO_0000003', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002233', X, X2],add,M1,_), fact(['obo:RO_0002025', X, X1],add,M2,_) \ fact(['obo:RO_0002233', X1, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002233', X1, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002459', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002004', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002326', X, Y],add,M1,_) \ fact(['obo:RO_0002329', X, Y],del,_,U) <=> true | fact(['obo:RO_0002329', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:RO_0002497', X1, X2],add,M2,_) \ fact(['obo:RO_0002497', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002578', X0, X1],add,M1,_), fact(['obo:RO_0002578', X1, X2],add,M2,_) \ fact(['obo:RO_0002211', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002211', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002622', X, Y],add,M1,_) \ fact(['obo:RO_0002618', X, Y],del,_,U) <=> true | fact(['obo:RO_0002618', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002224', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002331', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002331', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002331', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002576', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002400', X, Y],add,M1,_) \ fact(['obo:RO_0002233', X, Y],del,_,U) <=> true | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004000', X, _],add,M1,_) \ fact(['obo:BFO_0000017', X],del,_,U) <=> true | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002518', X, Y],add,M1,_) \ fact(['obo:RO_0002524', X, Y],del,_,U) <=> true | fact(['obo:RO_0002524', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002206', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X0, X1],add,M1,_), fact(['obo:RO_0002224', X1, X2],add,M2,_) \ fact(['obo:RO_0002090', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002090', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003301', X, Y],add,M1,_), fact(['obo:RO_0003301', Y, X],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002015', X, Y],add,M1,_) \ fact(['obo:RO_0002336', X, Y],del,_,U) <=> true | fact(['obo:RO_0002336', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002134', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002134', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002134', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000052', X, Y],add,M1,_) \ fact(['obo:RO_0002314', X, Y],del,_,U) <=> true | fact(['obo:RO_0002314', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009003', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002427', Y, X],add,M1,_) \ fact(['obo:RO_0002418', X, Y],del,_,U) <=> true | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002418', Y, X],add,M1,_) \ fact(['obo:RO_0002427', X, Y],del,_,U) <=> true | fact(['obo:RO_0002427', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002225', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002461', X0, X1],add,M1,_), fact(['obo:RO_0002466', X1, X2],add,M2,_), fact(['obo:RO_0002461', X3, X2],add,M3,_) \ fact(['obo:RO_0002441', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002441', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002641', Y, X],add,M1,_) \ fact(['obo:RO_0002640', X, Y],del,_,U) <=> true | fact(['obo:RO_0002640', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002640', Y, X],add,M1,_) \ fact(['obo:RO_0002641', X, Y],del,_,U) <=> true | fact(['obo:RO_0002641', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002211', X, Y],add,M1,_), fact(['obo:RO_0002211', Y, Z],add,M2,_) \ fact(['obo:RO_0002211', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002211', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002163', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009501', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002495', X, Y],add,M1,_) \ fact(['obo:RO_0002494', X, Y],del,_,U) <=> true | fact(['obo:RO_0002494', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003304', X, Y],add,M1,_) \ fact(['obo:RO_0003302', X, Y],del,_,U) <=> true | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002380', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002332', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002506', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002213', X, Y],add,M1,_), fact(['obo:RO_0002213', Y, Z],add,M2,_) \ fact(['obo:RO_0002213', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002213', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002355', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002413', X, Y],add,M1,_) \ fact(['obo:RO_0002414', X, Y],del,_,U) <=> true | fact(['obo:RO_0002414', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004003', X, Y],add,M1,_) \ fact(['obo:RO_0004000', X, Y],del,_,U) <=> true | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002334', Y, X],add,M1,_) \ fact(['obo:RO_0002211', X, Y],del,_,U) <=> true | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002211', Y, X],add,M1,_) \ fact(['obo:RO_0002334', X, Y],del,_,U) <=> true | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002159', Y, X],add,M1,_) \ fact(['obo:RO_0002159', X, Y],del,_,U) <=> true | fact(['obo:RO_0002159', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0085030', X],add,M1,_) \ fact(['obo:RO_0002467', X, X],del,_,U) <=> true | fact(['obo:RO_0002467', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002156', X0, X1],add,M1,_), fact(['obo:RO_0002157', X1, X2],add,M2,_) \ fact(['obo:RO_0002158', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002158', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002303', X, Y],add,M1,_) \ fact(['obo:RO_0002321', X, Y],del,_,U) <=> true | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011015', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003002', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002432', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002569', X, Y],add,M1,_) \ fact(['obo:RO_0002375', X, Y],del,_,U) <=> true | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002212', X1, X2],add,M2,_) \ fact(['obo:RO_0002430', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002430', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002496', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002496', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002496', X, Y],add,M1,_), fact(['obo:RO_NonExist', X],add,M2,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002131', X, Y],add,M1,_), fact(['obo:RO_NonExist', X],add,M2,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002162', X, Y],add,M1,_), fact(['obo:RO_NonExist', X],add,M2,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002315', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002382', X, Y],add,M1,_) \ fact(['obo:RO_0002377', X, Y],del,_,U) <=> true | fact(['obo:RO_0002377', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002507', X, Y],add,M1,_) \ fact(['obo:RO_0002559', X, Y],del,_,U) <=> true | fact(['obo:RO_0002559', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0001025', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0001025', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002314', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002314', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002314', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002224', X0, X1],add,M1,_), fact(['obo:RO_0002233', X1, X2],add,M2,_) \ fact(['obo:RO_0002233', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002233', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002336', Y, X],add,M1,_) \ fact(['obo:RO_0002213', X, Y],del,_,U) <=> true | fact(['obo:RO_0002213', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002213', Y, X],add,M1,_) \ fact(['obo:RO_0002336', X, Y],del,_,U) <=> true | fact(['obo:RO_0002336', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002583', X, Y],add,M1,_) \ fact(['obo:RO_0002496', X, Y],del,_,U) <=> true | fact(['obo:RO_0002496', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002371', X, Y],add,M1,_) \ fact(['obo:RO_0002177', X, Y],del,_,U) <=> true | fact(['obo:RO_0002177', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002449', X, Y],add,M1,_) \ fact(['obo:RO_0002448', X, Y],del,_,U) <=> true | fact(['obo:RO_0002448', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002567', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004009', X, Y],add,M1,_) \ fact(['obo:RO_0002233', X, Y],del,_,U) <=> true | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002092', X0, X1],add,M1,_), fact(['obo:BFO_0000063', X1, X2],add,M2,_) \ fact(['obo:BFO_0000063', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000063', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002460', Y, X],add,M1,_) \ fact(['obo:RO_0002459', X, Y],del,_,U) <=> true | fact(['obo:RO_0002459', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002459', Y, X],add,M1,_) \ fact(['obo:RO_0002460', X, Y],del,_,U) <=> true | fact(['obo:RO_0002460', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002158', Y, X],add,M1,_) \ fact(['obo:RO_0002158', X, Y],del,_,U) <=> true | fact(['obo:RO_0002158', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002606', X, Y],add,M1,_) \ fact(['obo:RO_0002599', X, Y],del,_,U) <=> true | fact(['obo:RO_0002599', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002335', Y, X],add,M1,_) \ fact(['obo:RO_0002212', X, Y],del,_,U) <=> true | fact(['obo:RO_0002212', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002212', Y, X],add,M1,_) \ fact(['obo:RO_0002335', X, Y],del,_,U) <=> true | fact(['obo:RO_0002335', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002201', X, Y],add,M1,_) \ fact(['owl:topObjectProperty', X, Y],del,_,U) <=> true | fact(['owl:topObjectProperty', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002292', X, Y],add,M1,_) \ fact(['obo:RO_0002330', X, Y],del,_,U) <=> true | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002574', _, X1],add,M1,_) \ fact(['obo:CARO_0001010', X1],del,_,U) <=> true | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002593', X0, X1],add,M1,_), fact(['obo:BFO_0000063', X1, X2],add,M2,_), fact(['obo:RO_0002593', X3, X2],add,M3,_) \ fact(['obo:RO_0002497', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002497', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002413', X, Y],add,M1,_) \ fact(['obo:RO_0002412', X, Y],del,_,U) <=> true | fact(['obo:RO_0002412', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002404', X, Y],add,M1,_) \ fact(['obo:BFO_0000062', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000062', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002590', X, Y],add,M1,_) \ fact(['obo:RO_0002592', X, Y],del,_,U) <=> true | fact(['obo:RO_0002592', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002100', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002100', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002100', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002214', X, X1],add,M1,_), fact(['obo:BFO_0000015', X],add,M2,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000015', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002600', X, Y],add,M1,_) \ fact(['obo:RO_0002598', X, Y],del,_,U) <=> true | fact(['obo:RO_0002598', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002481', X, Y],add,M1,_) \ fact(['obo:RO_0002564', X, Y],del,_,U) <=> true | fact(['obo:RO_0002564', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008501', X, Y],add,M1,_) \ fact(['obo:RO_0002440', X, Y],del,_,U) <=> true | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001019', Y, X],add,M1,_) \ fact(['obo:RO_0001018', X, Y],del,_,U) <=> true | fact(['obo:RO_0001018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001018', Y, X],add,M1,_) \ fact(['obo:RO_0001019', X, Y],del,_,U) <=> true | fact(['obo:RO_0001019', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002007', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002525', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002309', X, Y],add,M1,_) \ fact(['obo:RO_0002244', X, Y],del,_,U) <=> true | fact(['obo:RO_0002244', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002313', X0, X1],add,M1,_), fact(['obo:BFO_0000051', X1, X2],add,M2,_) \ fact(['obo:RO_0002313', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002313', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002348', _, X1],add,M1,_) \ fact(['obo:CL_0000000', X1],del,_,U) <=> true | fact(['obo:CL_0000000', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004009', X, Y],add,M1,_) \ fact(['obo:RO_0004007', X, Y],del,_,U) <=> true | fact(['obo:RO_0004007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002479', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002449', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X0, X1],add,M1,_), fact(['obo:BFO_0000055', X1, X2],add,M2,_), fact(['obo:RO_0000052', X2, X3],add,M3,_) \ fact(['obo:RO_0000057', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0000057', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002373', X, Y],add,M1,_) \ fact(['obo:RO_0002371', X, Y],del,_,U) <=> true | fact(['obo:RO_0002371', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002531', X, Y],add,M1,_) \ fact(['obo:RO_0002515', X, Y],del,_,U) <=> true | fact(['obo:RO_0002515', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002495', X, Y],add,M1,_) \ fact(['obo:RO_0002207', X, Y],del,_,U) <=> true | fact(['obo:RO_0002207', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002387', X, Y],add,M1,_) \ fact(['obo:RO_0002384', X, Y],del,_,U) <=> true | fact(['obo:RO_0002384', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002587', X, Y],add,M1,_) \ fact(['obo:RO_0002297', X, Y],del,_,U) <=> true | fact(['obo:RO_0002297', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002286', Y, X],add,M1,_) \ fact(['obo:RO_0002258', X, Y],del,_,U) <=> true | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002258', Y, X],add,M1,_) \ fact(['obo:RO_0002286', X, Y],del,_,U) <=> true | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002633', X, Y],add,M1,_) \ fact(['obo:RO_0002445', X, Y],del,_,U) <=> true | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002435', X, Y],add,M1,_) \ fact(['obo:RO_0002434', X, Y],del,_,U) <=> true | fact(['obo:RO_0002434', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002100', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002586', X, Y],add,M1,_) \ fact(['obo:RO_0002233', X, Y],del,_,U) <=> true | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002593', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002492', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002492', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004023', X, Y],add,M1,_) \ fact(['obo:RO_0040035', X, Y],del,_,U) <=> true | fact(['obo:RO_0040035', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011024', X, Y],add,M1,_) \ fact(['obo:RO_0011022', X, Y],del,_,U) <=> true | fact(['obo:RO_0011022', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002408', X0, X1],add,M1,_), fact(['obo:RO_0002408', X1, X2],add,M2,_) \ fact(['obo:RO_0002409', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002409', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002371', X, Y],add,M1,_) \ fact(['obo:RO_0002170', X, Y],del,_,U) <=> true | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004029', X, Y],add,M1,_) \ fact(['obo:RO_0040035', X, Y],del,_,U) <=> true | fact(['obo:RO_0040035', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002434', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002206', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002206', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002206', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002418', X1, X2],add,M2,_) \ fact(['obo:RO_0002264', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002264', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004020', X, Y],add,M1,_) \ fact(['obo:RO_0004019', X, Y],del,_,U) <=> true | fact(['obo:RO_0004019', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002501', _, X1],add,M1,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002334', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002624', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002530', X, Y],add,M1,_) \ fact(['obo:RO_0002529', X, Y],del,_,U) <=> true | fact(['obo:RO_0002529', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:BFO_0000066', X1, X2],add,M2,_) \ fact(['obo:RO_0002432', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002432', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002202', X, Y],add,M1,_), fact(['obo:RO_0002202', Y, Z],add,M2,_) \ fact(['obo:RO_0002202', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002202', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008508', Y, X],add,M1,_) \ fact(['obo:RO_0008507', X, Y],del,_,U) <=> true | fact(['obo:RO_0008507', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008507', Y, X],add,M1,_) \ fact(['obo:RO_0008508', X, Y],del,_,U) <=> true | fact(['obo:RO_0008508', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002214', X, X1],add,M1,_), fact(['obo:BFO_0000002', X],add,M2,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000002', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002606', Y, X],add,M1,_) \ fact(['obo:RO_0002302', X, Y],del,_,U) <=> true | fact(['obo:RO_0002302', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002302', Y, X],add,M1,_) \ fact(['obo:RO_0002606', X, Y],del,_,U) <=> true | fact(['obo:RO_0002606', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002437', X, Y],add,M1,_) \ fact(['obo:RO_0002321', X, Y],del,_,U) <=> true | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002426', X, Y],add,M1,_) \ fact(['obo:RO_0002424', X, Y],del,_,U) <=> true | fact(['obo:RO_0002424', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002203', X, Y],add,M1,_), fact(['obo:RO_0002203', Y, Z],add,M2,_) \ fact(['obo:RO_0002203', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002203', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002107', X, Y],add,M1,_) \ fact(['obo:RO_0002120', X, Y],del,_,U) <=> true | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002412', X, Y],add,M1,_) \ fact(['obo:RO_0002411', X, Y],del,_,U) <=> true | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002578', X, Y],add,M1,_) \ fact(['obo:RO_0002211', X, Y],del,_,U) <=> true | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002414', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002132', Y, X],add,M1,_) \ fact(['obo:RO_0002101', X, Y],del,_,U) <=> true | fact(['obo:RO_0002101', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002101', Y, X],add,M1,_) \ fact(['obo:RO_0002132', X, Y],del,_,U) <=> true | fact(['obo:RO_0002132', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002371', Y, X],add,M1,_) \ fact(['obo:RO_0002371', X, Y],del,_,U) <=> true | fact(['obo:RO_0002371', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002551', X, Y],add,M1,_), fact(['obo:RO_0002551', Y, X],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002530', X, Y],add,M1,_) \ fact(['obo:RO_0002515', X, Y],del,_,U) <=> true | fact(['obo:RO_0002515', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002427', X, Y],add,M1,_), fact(['obo:RO_0002427', Y, Z],add,M2,_) \ fact(['obo:RO_0002427', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002427', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002411', X1, X2],add,M2,_), fact(['obo:RO_0002233', X2, X3],add,M3,_) \ fact(['obo:RO_0002566', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002566', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004021', X, Y],add,M1,_) \ fact(['obo:RO_0004019', X, Y],del,_,U) <=> true | fact(['obo:RO_0004019', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002576', Y, X],add,M1,_) \ fact(['obo:RO_0002551', X, Y],del,_,U) <=> true | fact(['obo:RO_0002551', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002551', Y, X],add,M1,_) \ fact(['obo:RO_0002576', X, Y],del,_,U) <=> true | fact(['obo:RO_0002576', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003001', Y, X],add,M1,_) \ fact(['obo:RO_0003000', X, Y],del,_,U) <=> true | fact(['obo:RO_0003000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003000', Y, X],add,M1,_) \ fact(['obo:RO_0003001', X, Y],del,_,U) <=> true | fact(['obo:RO_0003001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008506', Y, X],add,M1,_) \ fact(['obo:RO_0008506', X, Y],del,_,U) <=> true | fact(['obo:RO_0008506', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009002', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002527', Y, X],add,M1,_) \ fact(['obo:RO_0002527', X, Y],del,_,U) <=> true | fact(['obo:RO_0002527', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002407', X, Y],add,M1,_) \ fact(['obo:RO_0002213', X, Y],del,_,U) <=> true | fact(['obo:RO_0002213', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002511', X0, X1],add,M1,_), fact(['obo:RO_0002513', X1, X2],add,M2,_) \ fact(['obo:RO_0002205', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002205', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002632', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002372', X, Y],add,M1,_) \ fact(['obo:RO_0002371', X, Y],del,_,U) <=> true | fact(['obo:RO_0002371', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002386', X, Y],add,M1,_) \ fact(['obo:RO_0002384', X, Y],del,_,U) <=> true | fact(['obo:RO_0002384', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0085031', X],add,M1,_) \ fact(['obo:RO_0002466', X, X],del,_,U) <=> true | fact(['obo:RO_0002466', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002526', Y, X],add,M1,_) \ fact(['obo:RO_0002526', X, Y],del,_,U) <=> true | fact(['obo:RO_0002526', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000000', X, X1],add,M1,_), fact(['obo:BFO_0000002', X],add,M2,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000002', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004025', X0, X1],add,M1,_), fact(['obo:RO_0002215', X1, X2],add,M2,_) \ fact(['obo:RO_0004024', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004024', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002104', X, _],add,M1,_) \ fact(['obo:CARO_0000006', X],del,_,U) <=> true | fact(['obo:CARO_0000006', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002301', X, Y],add,M1,_) \ fact(['obo:RO_0002552', X, Y],del,_,U) <=> true | fact(['obo:RO_0002552', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002494', X, Y],add,M1,_) \ fact(['obo:RO_0002202', X, Y],del,_,U) <=> true | fact(['obo:RO_0002202', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002521', X, Y],add,M1,_) \ fact(['obo:RO_0002514', X, Y],del,_,U) <=> true | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002527', X, Y],add,M1,_) \ fact(['obo:RO_0002514', X, Y],del,_,U) <=> true | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004030', X, Y],add,M1,_) \ fact(['obo:RO_0004019', X, Y],del,_,U) <=> true | fact(['obo:RO_0004019', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002100', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011014', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002405', X, Y],add,M1,_) \ fact(['obo:RO_0002087', X, Y],del,_,U) <=> true | fact(['obo:RO_0002087', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002016', X, Y],add,M1,_) \ fact(['obo:RO_0002017', X, Y],del,_,U) <=> true | fact(['obo:RO_0002017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002010', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002411', X1, X2],add,M2,_) \ fact(['obo:RO_0002263', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002263', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004026', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X0, X1],add,M1,_), fact(['obo:RO_0000057', X1, X2],add,M2,_) \ fact(['obo:RO_0000057', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0000057', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002330', _, X1],add,M1,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002566', X, _],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008506', X, _],add,M1,_) \ fact(['obo:CARO_0001010', X],del,_,U) <=> true | fact(['obo:CARO_0001010', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002200', X, Y],add,M1,_) \ fact(['owl:topObjectProperty', X, Y],del,_,U) <=> true | fact(['owl:topObjectProperty', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002567', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002478', X, Y],add,M1,_) \ fact(['obo:RO_0002476', X, Y],del,_,U) <=> true | fact(['obo:RO_0002476', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002025', X, Y],add,M1,_) \ fact(['obo:RO_0002017', X, Y],del,_,U) <=> true | fact(['obo:RO_0002017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002576', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002352', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002442', X, Y],add,M1,_) \ fact(['obo:RO_0002440', X, Y],del,_,U) <=> true | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002009', X, Y],add,M1,_) \ fact(['obo:RO_0002292', X, Y],del,_,U) <=> true | fact(['obo:RO_0002292', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002245', X, Y],add,M1,_) \ fact(['obo:RO_0002206', X, Y],del,_,U) <=> true | fact(['obo:RO_0002206', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002333', X, Y],add,M1,_) \ fact(['obo:RO_0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002109', X, Y],add,M1,_) \ fact(['obo:RO_0002103', X, Y],del,_,U) <=> true | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002524', X0, X1],add,M1,_), fact(['obo:RO_0002525', X1, X2],add,M2,_) \ fact(['obo:RO_0002526', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002526', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002553', X, Y],add,M1,_) \ fact(['obo:RO_0002454', X, Y],del,_,U) <=> true | fact(['obo:RO_0002454', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002470', X, Y],add,M1,_) \ fact(['obo:RO_0002438', X, Y],del,_,U) <=> true | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002252', X, Y],add,M1,_) \ fact(['obo:RO_0002375', X, Y],del,_,U) <=> true | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0016301', X],add,M1,_) \ fact(['obo:RO_0002481', X, X],del,_,U) <=> true | fact(['obo:RO_0002481', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002232', X, Y],add,M1,_) \ fact(['obo:RO_0002479', X, Y],del,_,U) <=> true | fact(['obo:RO_0002479', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004024', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0004024', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004024', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008502', Y, X],add,M1,_) \ fact(['obo:RO_0008501', X, Y],del,_,U) <=> true | fact(['obo:RO_0008501', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008501', Y, X],add,M1,_) \ fact(['obo:RO_0008502', X, Y],del,_,U) <=> true | fact(['obo:RO_0008502', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X0, X1],add,M1,_), fact(['obo:RO_0002213', X1, X2],add,M2,_) \ fact(['obo:RO_0002598', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002598', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002342', X, Y],add,M1,_) \ fact(['obo:RO_0002344', X, Y],del,_,U) <=> true | fact(['obo:RO_0002344', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002231', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002211', X0, X1],add,M1,_), fact(['obo:RO_0002313', X1, X2],add,M2,_) \ fact(['obo:RO_0002011', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002011', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002205', X, Y],add,M1,_) \ fact(['obo:RO_0002330', X, Y],del,_,U) <=> true | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002208', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003309', X, Y],add,M1,_) \ fact(['obo:RO_0003305', X, Y],del,_,U) <=> true | fact(['obo:RO_0003305', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002203', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002255', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002255', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004034', X, Y],add,M1,_) \ fact(['obo:RO_0002263', X, Y],del,_,U) <=> true | fact(['obo:RO_0002263', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008504', Y, X],add,M1,_) \ fact(['obo:RO_0008503', X, Y],del,_,U) <=> true | fact(['obo:RO_0008503', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008503', Y, X],add,M1,_) \ fact(['obo:RO_0008504', X, Y],del,_,U) <=> true | fact(['obo:RO_0008504', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002112', X, Y],add,M1,_) \ fact(['obo:RO_0002103', X, Y],del,_,U) <=> true | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002378', X, Y],add,M1,_), fact(['obo:RO_0002382', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002590', X, Y],add,M1,_) \ fact(['obo:RO_0002586', X, Y],del,_,U) <=> true | fact(['obo:RO_0002586', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002445', X0, X1],add,M1,_), fact(['obo:RO_0002445', X1, X2],add,M2,_) \ fact(['obo:RO_0002554', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002554', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002378', X, Y],add,M1,_), fact(['obo:RO_0002383', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002456', Y, X],add,M1,_) \ fact(['obo:RO_0002455', X, Y],del,_,U) <=> true | fact(['obo:RO_0002455', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002455', Y, X],add,M1,_) \ fact(['obo:RO_0002456', X, Y],del,_,U) <=> true | fact(['obo:RO_0002456', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004034', X, Y],add,M1,_) \ fact(['obo:RO_0004032', X, Y],del,_,U) <=> true | fact(['obo:RO_0004032', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002551', _, X1],add,M1,_) \ fact(['obo:CARO_0000006', X1],del,_,U) <=> true | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002102', X, Y],add,M1,_) \ fact(['obo:RO_0002113', X, Y],del,_,U) <=> true | fact(['obo:RO_0002113', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002431', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002573', X, _],add,M1,_) \ fact(['obo:BFO_0000020', X],del,_,U) <=> true | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002521', Y, X],add,M1,_) \ fact(['obo:RO_0002521', X, Y],del,_,U) <=> true | fact(['obo:RO_0002521', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002339', X, Y],add,M1,_) \ fact(['obo:RO_0002344', X, Y],del,_,U) <=> true | fact(['obo:RO_0002344', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002584', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003303', X, Y],add,M1,_) \ fact(['obo:RO_0003302', X, Y],del,_,U) <=> true | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002558', X, Y],add,M1,_) \ fact(['obo:RO_0002616', X, Y],del,_,U) <=> true | fact(['obo:RO_0002616', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002505', X, Y],add,M1,_) \ fact(['obo:RO_0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002458', X, Y],add,M1,_) \ fact(['obo:RO_0002438', X, Y],del,_,U) <=> true | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004012', X, Y],add,M1,_) \ fact(['obo:RO_0004010', X, Y],del,_,U) <=> true | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002494', X, Y],add,M1,_), fact(['obo:RO_0002494', Y, Z],add,M2,_) \ fact(['obo:RO_0002494', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002494', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002205', X, _],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002608', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X0, X1],add,M1,_), fact(['obo:RO_0002481', X1, X2],add,M2,_), fact(['obo:RO_0002400', X2, X3],add,M3,_) \ fact(['obo:RO_0002447', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002447', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002487', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003001', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002378', X, Y],add,M1,_) \ fact(['obo:RO_0002377', X, Y],del,_,U) <=> true | fact(['obo:RO_0002377', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002257', X, Y],add,M1,_) \ fact(['obo:RO_0002386', X, Y],del,_,U) <=> true | fact(['obo:RO_0002386', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002151', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004007', X, Y],add,M1,_) \ fact(['obo:RO_0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002381', X, Y],add,M1,_) \ fact(['obo:RO_0002375', X, Y],del,_,U) <=> true | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004004', X, Y],add,M1,_) \ fact(['obo:RO_0004000', X, Y],del,_,U) <=> true | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000003', X, Y],add,M1,_) \ fact(['obo:RO_0002320', X, Y],del,_,U) <=> true | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002213', X2, X],add,M1,_), fact(['obo:RO_0002212', X, X1],add,M2,_) \ fact(['obo:RO_0002212', X2, X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002212', X2, X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002212', X, X1],add,M1,_), fact(['obo:RO_0002213', X1, X2],add,M2,_) \ fact(['obo:RO_0002212', X, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002212', X, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002085', X, Y],add,M1,_) \ fact(['obo:RO_0002088', X, Y],del,_,U) <=> true | fact(['obo:RO_0002088', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002555', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002157', Y, X],add,M1,_) \ fact(['obo:RO_0002156', X, Y],del,_,U) <=> true | fact(['obo:RO_0002156', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002156', Y, X],add,M1,_) \ fact(['obo:RO_0002157', X, Y],del,_,U) <=> true | fact(['obo:RO_0002157', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011004', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002457', X, Y],add,M1,_) \ fact(['obo:RO_0002438', X, Y],del,_,U) <=> true | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002120', Y, X],add,M1,_) \ fact(['obo:RO_0002103', X, Y],del,_,U) <=> true | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002103', Y, X],add,M1,_) \ fact(['obo:RO_0002120', X, Y],del,_,U) <=> true | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002629', X, Y],add,M1,_) \ fact(['obo:RO_0002213', X, Y],del,_,U) <=> true | fact(['obo:RO_0002213', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0010001', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002293', X, Y],add,M1,_) \ fact(['obo:RO_0002292', X, Y],del,_,U) <=> true | fact(['obo:RO_0002292', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002524', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002487', _, X1],add,M1,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002497', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002497', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002017', X1, X2],add,M2,_) \ fact(['obo:RO_0002327', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002327', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002635', Y, X],add,M1,_) \ fact(['obo:RO_0002634', X, Y],del,_,U) <=> true | fact(['obo:RO_0002634', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002634', Y, X],add,M1,_) \ fact(['obo:RO_0002635', X, Y],del,_,U) <=> true | fact(['obo:RO_0002635', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000052', X0, X1],add,M1,_), fact(['obo:RO_0000058', X1, X2],add,M2,_) \ fact(['obo:RO_0010001', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0010001', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002157', X, Y],add,M1,_), fact(['obo:RO_0002157', Y, Z],add,M2,_) \ fact(['obo:RO_0002157', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002157', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002331', X, Y],add,M1,_) \ fact(['obo:RO_0002431', X, Y],del,_,U) <=> true | fact(['obo:RO_0002431', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004035', X, Y],add,M1,_) \ fact(['obo:RO_0004033', X, Y],del,_,U) <=> true | fact(['obo:RO_0004033', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002202', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004030', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002156', X, Y],add,M1,_), fact(['obo:RO_0002156', Y, Z],add,M2,_) \ fact(['obo:RO_0002156', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002156', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001023', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002380', X, Y],add,M1,_) \ fact(['obo:RO_0002375', X, Y],del,_,U) <=> true | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002299', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002523', Y, X],add,M1,_) \ fact(['obo:RO_0002522', X, Y],del,_,U) <=> true | fact(['obo:RO_0002522', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002522', Y, X],add,M1,_) \ fact(['obo:RO_0002523', X, Y],del,_,U) <=> true | fact(['obo:RO_0002523', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002506', _, X1],add,M1,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003000', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002551', X, X],add,M1,_) \ fact(['owl:Nothing', X, X],del,_,U) <=> true | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002108', X, Y],add,M1,_) \ fact(['obo:RO_0002103', X, Y],del,_,U) <=> true | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002231', X, Y],add,M1,_) \ fact(['obo:RO_0002479', X, Y],del,_,U) <=> true | fact(['obo:RO_0002479', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004005', X, Y],add,M1,_) \ fact(['obo:RO_0004000', X, Y],del,_,U) <=> true | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004027', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002448', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004013', X, Y],add,M1,_) \ fact(['obo:RO_0004010', X, Y],del,_,U) <=> true | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002338', X, Y],add,M1,_) \ fact(['obo:RO_0002344', X, Y],del,_,U) <=> true | fact(['obo:RO_0002344', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002411', X, Y],add,M1,_) \ fact(['obo:RO_0002418', X, Y],del,_,U) <=> true | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X2, X],add,M1,_), fact(['obo:BFO_0000051', X, X1],add,M2,_), fact(['obo:GO_0003674', X],add,M3,_) \ fact(['obo:RO_0002327', X2, X1],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002327', X2, X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002572', X, Y],add,M1,_) \ fact(['obo:RO_0002571', X, Y],del,_,U) <=> true | fact(['obo:RO_0002571', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002637', Y, X],add,M1,_) \ fact(['obo:RO_0002636', X, Y],del,_,U) <=> true | fact(['obo:RO_0002636', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002636', Y, X],add,M1,_) \ fact(['obo:RO_0002637', X, Y],del,_,U) <=> true | fact(['obo:RO_0002637', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002132', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002425', X, Y],add,M1,_) \ fact(['obo:RO_0002424', X, Y],del,_,U) <=> true | fact(['obo:RO_0002424', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002473', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009003', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002214', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002377', X, Y],add,M1,_) \ fact(['obo:RO_0002375', X, Y],del,_,U) <=> true | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002583', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002488', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002488', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002450', X, Y],add,M1,_) \ fact(['obo:RO_0002448', X, Y],del,_,U) <=> true | fact(['obo:RO_0002448', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011014', X, Y],add,M1,_) \ fact(['obo:RO_0011010', X, Y],del,_,U) <=> true | fact(['obo:RO_0011010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002295', X, _],add,M1,_) \ fact(['obo:GO_0008150', X],del,_,U) <=> true | fact(['obo:GO_0008150', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002574', X, _],add,M1,_) \ fact(['obo:CARO_0001010', X],del,_,U) <=> true | fact(['obo:CARO_0001010', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004027', X, Y],add,M1,_) \ fact(['obo:RO_0004026', X, Y],del,_,U) <=> true | fact(['obo:RO_0004026', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002310', X],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002211', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002439', X, Y],add,M1,_) \ fact(['obo:RO_0002438', X, Y],del,_,U) <=> true | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002110', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002110', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002110', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002512', X0, X1],add,M1,_), fact(['obo:RO_0002510', X1, X2],add,M2,_) \ fact(['obo:RO_0002204', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002204', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002448', X, Y],add,M1,_) \ fact(['obo:RO_0002436', X, Y],del,_,U) <=> true | fact(['obo:RO_0002436', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004021', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002509', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002385', X, Y],add,M1,_) \ fact(['obo:RO_0002384', X, Y],del,_,U) <=> true | fact(['obo:RO_0002384', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002461', X, Y],add,M1,_) \ fact(['obo:RO_0000056', X, Y],del,_,U) <=> true | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:BFO_0000051', X1, X2],add,M2,_) \ fact(['obo:RO_0004031', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004031', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002585', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002158', X, Y],add,M1,_), fact(['obo:RO_0002158', Y, Z],add,M2,_) \ fact(['obo:RO_0002158', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002158', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002633', Y, X],add,M1,_) \ fact(['obo:RO_0002632', X, Y],del,_,U) <=> true | fact(['obo:RO_0002632', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002632', Y, X],add,M1,_) \ fact(['obo:RO_0002633', X, Y],del,_,U) <=> true | fact(['obo:RO_0002633', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002402', X0, X1],add,M1,_), fact(['obo:RO_0002400', X1, X2],add,M2,_) \ fact(['obo:RO_0002413', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002413', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004019', X, Y],add,M1,_) \ fact(['obo:RO_0004017', X, Y],del,_,U) <=> true | fact(['obo:RO_0004017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002592', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002159', X, Y],add,M1,_), fact(['obo:RO_0002159', Y, Z],add,M2,_) \ fact(['obo:RO_0002159', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002159', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002571', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002637', X, Y],add,M1,_) \ fact(['obo:RO_0002445', X, Y],del,_,U) <=> true | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002384', _, X1],add,M1,_) \ fact(['obo:CARO_0000000', X1],del,_,U) <=> true | fact(['obo:CARO_0000000', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011003', X, Y],add,M1,_) \ fact(['obo:RO_0002566', X, Y],del,_,U) <=> true | fact(['obo:RO_0002566', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002524', X, Y],add,M1,_), fact(['obo:RO_0002524', Y, Z],add,M2,_) \ fact(['obo:RO_0002524', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002524', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002629', X, X2],add,M1,_), fact(['obo:RO_0002025', X, X1],add,M2,_) \ fact(['obo:RO_0002629', X1, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002629', X1, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0004046', X1, X2],add,M2,_) \ fact(['obo:RO_0004033', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004033', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002218', X, Y],add,M1,_) \ fact(['obo:RO_0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002523', X, Y],add,M1,_), fact(['obo:RO_0002523', Y, Z],add,M2,_) \ fact(['obo:RO_0002523', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002523', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004017', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X0, X1],add,M1,_), fact(['obo:RO_0002213', X1, X2],add,M2,_) \ fact(['obo:RO_0002213', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002213', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002018', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002492', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002492', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002492', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002517', X, Y],add,M1,_) \ fact(['obo:RO_0002525', X, Y],del,_,U) <=> true | fact(['obo:RO_0002525', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002001', X, Y],add,M1,_), fact(['obo:RO_0002001', Y, Z],add,M2,_) \ fact(['obo:RO_0002001', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002001', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002212', X0, X1],add,M1,_), fact(['obo:RO_0002212', X1, X2],add,M2,_) \ fact(['obo:RO_0002213', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002213', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002520', X, Y],add,M1,_) \ fact(['obo:RO_0002524', X, Y],del,_,U) <=> true | fact(['obo:RO_0002524', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002314', X, Y],add,M1,_) \ fact(['obo:RO_0002502', X, Y],del,_,U) <=> true | fact(['obo:RO_0002502', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002525', X, Y],add,M1,_), fact(['obo:RO_0002525', Y, Z],add,M2,_) \ fact(['obo:RO_0002525', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002525', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002583', X0, X1],add,M1,_), fact(['obo:BFO_0000062', X1, X2],add,M2,_), fact(['obo:RO_0002583', X3, X2],add,M3,_) \ fact(['obo:RO_0002496', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002496', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002379', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002177', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002226', X, _],add,M1,_) \ fact(['obo:CARO_0000000', X],del,_,U) <=> true | fact(['obo:CARO_0000000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002305', X, Y],add,M1,_) \ fact(['obo:RO_0004046', X, Y],del,_,U) <=> true | fact(['obo:RO_0004046', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X2, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X],add,M2,_), fact(['obo:GO_0008150', X],add,M3,_) \ fact(['obo:RO_0002331', X2, X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002331', X2, X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002331', X0, X1],add,M1,_), fact(['obo:RO_0002211', X1, X2],add,M2,_) \ fact(['obo:RO_0002428', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002428', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002522', X, Y],add,M1,_), fact(['obo:RO_0002522', Y, Z],add,M2,_) \ fact(['obo:RO_0002522', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002522', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011015', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004027', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002529', Y, X],add,M1,_) \ fact(['obo:RO_0002529', X, Y],del,_,U) <=> true | fact(['obo:RO_0002529', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002529', Y, X],add,M1,_) \ fact(['obo:RO_0002529', X, Y],del,_,U) <=> true | fact(['obo:RO_0002529', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002204', X, Y],add,M1,_) \ fact(['obo:RO_0002330', X, Y],del,_,U) <=> true | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002525', Y, X],add,M1,_) \ fact(['obo:RO_0002524', X, Y],del,_,U) <=> true | fact(['obo:RO_0002524', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002524', Y, X],add,M1,_) \ fact(['obo:RO_0002525', X, Y],del,_,U) <=> true | fact(['obo:RO_0002525', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002639', Y, X],add,M1,_) \ fact(['obo:RO_0002638', X, Y],del,_,U) <=> true | fact(['obo:RO_0002638', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002638', Y, X],add,M1,_) \ fact(['obo:RO_0002639', X, Y],del,_,U) <=> true | fact(['obo:RO_0002639', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002343', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002159', X, Y],add,M1,_) \ fact(['obo:RO_0002320', X, Y],del,_,U) <=> true | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002315', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002004', X, Y],add,M1,_) \ fact(['obo:RO_0001018', X, Y],del,_,U) <=> true | fact(['obo:RO_0001018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002578', Y, X],add,M1,_) \ fact(['obo:RO_0002022', X, Y],del,_,U) <=> true | fact(['obo:RO_0002022', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002022', Y, X],add,M1,_) \ fact(['obo:RO_0002578', X, Y],del,_,U) <=> true | fact(['obo:RO_0002578', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002295', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002437', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002115', Y, X],add,M1,_) \ fact(['obo:RO_0002114', X, Y],del,_,U) <=> true | fact(['obo:RO_0002114', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002114', Y, X],add,M1,_) \ fact(['obo:RO_0002115', X, Y],del,_,U) <=> true | fact(['obo:RO_0002115', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002596', X, Y],add,M1,_) \ fact(['obo:RO_0002500', X, Y],del,_,U) <=> true | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0044403', X],add,M1,_) \ fact(['obo:RO_0002465', X, X],del,_,U) <=> true | fact(['obo:RO_0002465', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011015', X, Y],add,M1,_) \ fact(['obo:RO_0011009', X, Y],del,_,U) <=> true | fact(['obo:RO_0011009', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002461', X0, X1],add,M1,_), fact(['obo:RO_0002467', X1, X2],add,M2,_), fact(['obo:RO_0002461', X3, X2],add,M3,_) \ fact(['obo:RO_0002442', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002442', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002337', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002162', X, Y],add,M1,_) \ fact(['obo:RO_0002320', X, Y],del,_,U) <=> true | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002000', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002263', X, Y],add,M1,_) \ fact(['obo:RO_0002264', X, Y],del,_,U) <=> true | fact(['obo:RO_0002264', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002528', X, Y],add,M1,_), fact(['obo:RO_0002528', Y, Z],add,M2,_) \ fact(['obo:RO_0002528', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002528', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002444', X0, X1],add,M1,_), fact(['obo:RO_0002444', X1, X2],add,M2,_) \ fact(['obo:RO_0002553', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002553', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:RO_0002496', X1, X2],add,M2,_) \ fact(['obo:RO_0002496', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002200', _, X1],add,M1,_) \ fact(['obo:UPHENO_0001001', X1],del,_,U) <=> true | fact(['obo:UPHENO_0001001', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002564', X, Y],add,M1,_) \ fact(['obo:RO_0002563', X, Y],del,_,U) <=> true | fact(['obo:RO_0002563', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002024', X, Y],add,M1,_) \ fact(['obo:RO_0002022', X, Y],del,_,U) <=> true | fact(['obo:RO_0002022', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002566', Y, X],add,M1,_) \ fact(['obo:RO_0002559', X, Y],del,_,U) <=> true | fact(['obo:RO_0002559', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002559', Y, X],add,M1,_) \ fact(['obo:RO_0002566', X, Y],del,_,U) <=> true | fact(['obo:RO_0002566', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002529', X, Y],add,M1,_), fact(['obo:RO_0002529', Y, Z],add,M2,_) \ fact(['obo:RO_0002529', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002529', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002486', Y, X],add,M1,_) \ fact(['obo:RO_0002485', X, Y],del,_,U) <=> true | fact(['obo:RO_0002485', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002485', Y, X],add,M1,_) \ fact(['obo:RO_0002486', X, Y],del,_,U) <=> true | fact(['obo:RO_0002486', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004035', X, Y],add,M1,_) \ fact(['obo:RO_0002263', X, Y],del,_,U) <=> true | fact(['obo:RO_0002263', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002325', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002452', X, Y],add,M1,_) \ fact(['obo:RO_0002200', X, Y],del,_,U) <=> true | fact(['obo:RO_0002200', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002231', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002014', X, Y],add,M1,_) \ fact(['obo:RO_0002335', X, Y],del,_,U) <=> true | fact(['obo:RO_0002335', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002213', X1, X2],add,M2,_) \ fact(['obo:RO_0002429', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002429', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002341', X, Y],add,M1,_) \ fact(['obo:RO_0002337', X, Y],del,_,U) <=> true | fact(['obo:RO_0002337', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002025', X, Y1],add,M1,_), fact(['obo:RO_0002025', X, Y2],add,M2,_) \ fact(['owl:sameAs', Y1, Y2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002241', X, Y],add,M1,_) \ fact(['obo:RO_0002309', X, Y],del,_,U) <=> true | fact(['obo:RO_0002309', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002486', X, Y],add,M1,_) \ fact(['obo:RO_0002170', X, Y],del,_,U) <=> true | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002578', X, X1],add,M1,_), fact(['obo:RO_0002327', X2, X1],add,M2,_), fact(['obo:GO_0003674', X1],add,M3,_), fact(['obo:GO_0003674', X],add,M4,_) \ fact(['obo:RO_0002233', X, X2],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4],M), fact(['obo:RO_0002233', X, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002629', X, Y],add,M1,_) \ fact(['obo:RO_0002578', X, Y],del,_,U) <=> true | fact(['obo:RO_0002578', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011002', X, Y],add,M1,_) \ fact(['obo:RO_0002566', X, Y],del,_,U) <=> true | fact(['obo:RO_0002566', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002473', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004031', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002352', Y, X],add,M1,_) \ fact(['obo:RO_0002233', X, Y],del,_,U) <=> true | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002233', Y, X],add,M1,_) \ fact(['obo:RO_0002352', X, Y],del,_,U) <=> true | fact(['obo:RO_0002352', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002507', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002304', X, Y],add,M1,_) \ fact(['obo:RO_0004047', X, Y],del,_,U) <=> true | fact(['obo:RO_0004047', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002352', X3, X1],add,M1,_), fact(['obo:RO_0002333', X2, X3],add,M2,_), fact(['obo:RO_0002014', X, X1],add,M3,_) \ fact(['obo:RO_0002630', X2, X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002630', X2, X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002158', X, Y],add,M1,_) \ fact(['obo:RO_0002320', X, Y],del,_,U) <=> true | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002352', X3, X1],add,M1,_), fact(['obo:RO_0002333', X2, X3],add,M2,_), fact(['obo:RO_0002015', X, X1],add,M3,_) \ fact(['obo:RO_0002629', X2, X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002629', X2, X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002412', X, Y],add,M1,_) \ fact(['obo:RO_0002090', X, Y],del,_,U) <=> true | fact(['obo:RO_0002090', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002013', X, Y],add,M1,_) \ fact(['obo:RO_0002334', X, Y],del,_,U) <=> true | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X, Y],add,M1,_) \ fact(['obo:RO_0002215', X, Y],del,_,U) <=> true | fact(['obo:RO_0002215', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002286', X0, X1],add,M1,_), fact(['obo:RO_0002497', X1, X2],add,M2,_) \ fact(['obo:RO_0002497', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002204', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000301', X, Y],add,M1,_), fact(['obo:RO_0000301', Y, Z],add,M2,_) \ fact(['obo:RO_0000301', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0000301', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001018', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002557', Y, X],add,M1,_) \ fact(['obo:RO_0002556', X, Y],del,_,U) <=> true | fact(['obo:RO_0002556', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002556', Y, X],add,M1,_) \ fact(['obo:RO_0002557', X, Y],del,_,U) <=> true | fact(['obo:RO_0002557', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000302', X, Y],add,M1,_), fact(['obo:RO_0000302', Y, Z],add,M2,_) \ fact(['obo:RO_0000302', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0000302', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002371', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002177', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002177', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002176', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002493', X, Y],add,M1,_) \ fact(['obo:RO_0002492', X, Y],del,_,U) <=> true | fact(['obo:RO_0002492', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002345', X0, X1],add,M1,_), fact(['obo:BFO_0000051', X1, X2],add,M2,_) \ fact(['obo:RO_0002345', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002345', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002112', Y, X],add,M1,_) \ fact(['obo:RO_0002106', X, Y],del,_,U) <=> true | fact(['obo:RO_0002106', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002106', Y, X],add,M1,_) \ fact(['obo:RO_0002112', X, Y],del,_,U) <=> true | fact(['obo:RO_0002112', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002023', X, Y],add,M1,_) \ fact(['obo:RO_0002022', X, Y],del,_,U) <=> true | fact(['obo:RO_0002022', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002353', Y, X],add,M1,_) \ fact(['obo:RO_0002234', X, Y],del,_,U) <=> true | fact(['obo:RO_0002234', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002234', Y, X],add,M1,_) \ fact(['obo:RO_0002353', X, Y],del,_,U) <=> true | fact(['obo:RO_0002353', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002022', X, Y],add,M1,_) \ fact(['obo:RO_0002334', X, Y],del,_,U) <=> true | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002296', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002257', Y, X],add,M1,_) \ fact(['obo:RO_0002256', X, Y],del,_,U) <=> true | fact(['obo:RO_0002256', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002256', Y, X],add,M1,_) \ fact(['obo:RO_0002257', X, Y],del,_,U) <=> true | fact(['obo:RO_0002257', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002026', _, X1],add,M1,_) \ fact(['foaf:image', X1],del,_,U) <=> true | fact(['foaf:image', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002559', X, Y],add,M1,_) \ fact(['obo:RO_0002506', X, Y],del,_,U) <=> true | fact(['obo:RO_0002506', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002332', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002297', X, Y],add,M1,_) \ fact(['obo:RO_0002234', X, Y],del,_,U) <=> true | fact(['obo:RO_0002234', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002373', X, Y],add,M1,_) \ fact(['obo:RO_0002567', X, Y],del,_,U) <=> true | fact(['obo:RO_0002567', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002557', X, Y],add,M1,_) \ fact(['obo:RO_0002453', X, Y],del,_,U) <=> true | fact(['obo:RO_0002453', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002342', X, Y],add,M1,_) \ fact(['obo:RO_0002021', X, Y],del,_,U) <=> true | fact(['obo:RO_0002021', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002121', X, _],add,M1,_) \ fact(['obo:CL_0000540', X],del,_,U) <=> true | fact(['obo:CL_0000540', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002305', X, Y],add,M1,_) \ fact(['obo:RO_0002411', X, Y],del,_,U) <=> true | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002254', _, X1],add,M1,_) \ fact(['obo:CARO_0000000', X1],del,_,U) <=> true | fact(['obo:CARO_0000000', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002450', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002513', X, Y],add,M1,_) \ fact(['obo:RO_0002330', X, Y],del,_,U) <=> true | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002599', X, Y],add,M1,_) \ fact(['obo:RO_0002597', X, Y],del,_,U) <=> true | fact(['obo:RO_0002597', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002639', X, Y],add,M1,_) \ fact(['obo:RO_0002635', X, Y],del,_,U) <=> true | fact(['obo:RO_0002635', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011014', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002461', X0, X1],add,M1,_), fact(['obo:RO_0002468', X1, X2],add,M2,_), fact(['obo:RO_0002461', X3, X2],add,M3,_) \ fact(['obo:RO_0002443', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002443', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004014', X, Y],add,M1,_) \ fact(['obo:RO_0004010', X, Y],del,_,U) <=> true | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002554', Y, X],add,M1,_) \ fact(['obo:RO_0002553', X, Y],del,_,U) <=> true | fact(['obo:RO_0002553', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002553', Y, X],add,M1,_) \ fact(['obo:RO_0002554', X, Y],del,_,U) <=> true | fact(['obo:RO_0002554', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002176', X1, X0],add,M1,_), fact(['obo:RO_0002176', X1, X2],add,M2,_) \ fact(['obo:RO_0002170', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002170', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002630', X, X2],add,M1,_), fact(['obo:RO_0002025', X, X1],add,M2,_) \ fact(['obo:RO_0002630', X1, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002630', X1, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004019', X, Y],add,M1,_) \ fact(['obo:RO_0004023', X, Y],del,_,U) <=> true | fact(['obo:RO_0004023', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002331', X, Y],add,M1,_) \ fact(['obo:RO_0000056', X, Y],del,_,U) <=> true | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002110', Y, X],add,M1,_) \ fact(['obo:RO_0002102', X, Y],del,_,U) <=> true | fact(['obo:RO_0002102', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002102', Y, X],add,M1,_) \ fact(['obo:RO_0002110', X, Y],del,_,U) <=> true | fact(['obo:RO_0002110', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002224', X0, X1],add,M1,_), fact(['obo:RO_0002400', X1, X2],add,M2,_) \ fact(['obo:RO_0002400', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002400', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002221', Y, X],add,M1,_) \ fact(['obo:RO_0002219', X, Y],del,_,U) <=> true | fact(['obo:RO_0002219', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002219', Y, X],add,M1,_) \ fact(['obo:RO_0002221', X, Y],del,_,U) <=> true | fact(['obo:RO_0002221', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002298', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002526', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004022', X, Y],add,M1,_) \ fact(['obo:RO_0004019', X, Y],del,_,U) <=> true | fact(['obo:RO_0004019', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002509', X, Y],add,M1,_) \ fact(['obo:RO_0002506', X, Y],del,_,U) <=> true | fact(['obo:RO_0002506', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002566', _, X1],add,M1,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002517', X, Y],add,M1,_), fact(['obo:RO_0002517', Y, Z],add,M2,_) \ fact(['obo:RO_0002517', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002517', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002570', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0001018', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0001018', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002519', X, Y],add,M1,_), fact(['obo:RO_0002519', Y, Z],add,M2,_) \ fact(['obo:RO_0002519', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002519', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002340', X0, X1],add,M1,_), fact(['obo:BFO_0000051', X1, X2],add,M2,_) \ fact(['obo:RO_0002340', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002340', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002162', _, X1],add,M1,_) \ fact(['obo:CARO_0001010', X1],del,_,U) <=> true | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002384', X, Y],add,M1,_) \ fact(['obo:RO_0002324', X, Y],del,_,U) <=> true | fact(['obo:RO_0002324', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011023', X, Y],add,M1,_) \ fact(['obo:RO_0011022', X, Y],del,_,U) <=> true | fact(['obo:RO_0011022', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002518', X, Y],add,M1,_), fact(['obo:RO_0002518', Y, Z],add,M2,_) \ fact(['obo:RO_0002518', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002518', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002456', X, Y],add,M1,_) \ fact(['obo:RO_0002442', X, Y],del,_,U) <=> true | fact(['obo:RO_0002442', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002441', X, Y],add,M1,_) \ fact(['obo:RO_0002440', X, Y],del,_,U) <=> true | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002106', X, Y],add,M1,_) \ fact(['obo:RO_0002120', X, Y],del,_,U) <=> true | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002232', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002565', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002503', X, Y],add,M1,_) \ fact(['obo:RO_0002502', X, Y],del,_,U) <=> true | fact(['obo:RO_0002502', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002300', X, Y],add,M1,_) \ fact(['obo:RO_0002552', X, Y],del,_,U) <=> true | fact(['obo:RO_0002552', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002008', X, _],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002375', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X2, X],add,M1,_), fact(['obo:BFO_0000066', X, X1],add,M2,_) \ fact(['obo:BFO_0000050', X2, X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X2, X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002526', X, Y],add,M1,_) \ fact(['obo:RO_0002514', X, Y],del,_,U) <=> true | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002248', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003311', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002516', X, Y],add,M1,_), fact(['obo:RO_0002516', Y, Z],add,M2,_) \ fact(['obo:RO_0002516', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002516', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002377', X0, X1],add,M1,_), fact(['obo:RO_0002381', X1, X2],add,M2,_) \ fact(['obo:RO_0002380', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002380', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002356', _, X1],add,M1,_) \ fact(['obo:CL_0000000', X1],del,_,U) <=> true | fact(['obo:CL_0000000', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002458', Y, X],add,M1,_) \ fact(['obo:RO_0002439', X, Y],del,_,U) <=> true | fact(['obo:RO_0002439', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002439', Y, X],add,M1,_) \ fact(['obo:RO_0002458', X, Y],del,_,U) <=> true | fact(['obo:RO_0002458', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002552', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002170', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002180', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002211', X1, X2],add,M2,_), fact(['obo:RO_0002333', X2, X3],add,M3,_) \ fact(['obo:RO_0002448', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002448', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002509', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002408', X, Y],add,M1,_) \ fact(['obo:RO_0002630', X, Y],del,_,U) <=> true | fact(['obo:RO_0002630', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003302', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004022', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002445', Y, X],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002444', Y, X],add,M1,_) \ fact(['obo:RO_0002445', X, Y],del,_,U) <=> true | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002176', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002240', X, Y],add,M1,_) \ fact(['obo:RO_0002244', X, Y],del,_,U) <=> true | fact(['obo:RO_0002244', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004018', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002477', X, Y],add,M1,_) \ fact(['obo:RO_0002476', X, Y],del,_,U) <=> true | fact(['obo:RO_0002476', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0004047', X1, X2],add,M2,_) \ fact(['obo:RO_0004032', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004032', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002015', X, Y],add,M1,_) \ fact(['obo:RO_0002013', X, Y],del,_,U) <=> true | fact(['obo:RO_0002013', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002525', X, Y],add,M1,_) \ fact(['obo:RO_0002526', X, Y],del,_,U) <=> true | fact(['obo:RO_0002526', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009001', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011007', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000300', X, Y],add,M1,_), fact(['obo:RO_0000300', Y, Z],add,M2,_) \ fact(['obo:RO_0000300', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0000300', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002472', X, Y],add,M1,_) \ fact(['obo:RO_0002616', X, Y],del,_,U) <=> true | fact(['obo:RO_0002616', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002433', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000000', X, X1],add,M1,_), fact(['obo:BFO_0000003', X],add,M2,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000003', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002551', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011010', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002412', Y, X],add,M1,_) \ fact(['obo:RO_0002405', X, Y],del,_,U) <=> true | fact(['obo:RO_0002405', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002405', Y, X],add,M1,_) \ fact(['obo:RO_0002412', X, Y],del,_,U) <=> true | fact(['obo:RO_0002412', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002293', Y, X],add,M1,_) \ fact(['obo:RO_0002291', X, Y],del,_,U) <=> true | fact(['obo:RO_0002291', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002291', Y, X],add,M1,_) \ fact(['obo:RO_0002293', X, Y],del,_,U) <=> true | fact(['obo:RO_0002293', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002460', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002229', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002333', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002573', _, X1],add,M1,_) \ fact(['obo:BFO_0000020', X1],del,_,U) <=> true | fact(['obo:BFO_0000020', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002426', _, X1],add,M1,_) \ fact(['obo:BFO_0000020', X1],del,_,U) <=> true | fact(['obo:BFO_0000020', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002516', X, Y],add,M1,_) \ fact(['obo:RO_0002524', X, Y],del,_,U) <=> true | fact(['obo:RO_0002524', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002223', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002205', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002509', X, _],add,M1,_) \ fact(['obo:RO_0002577', X],del,_,U) <=> true | fact(['obo:RO_0002577', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002462', X0, X1],add,M1,_), fact(['obo:RO_0002468', X1, X2],add,M2,_), fact(['obo:RO_0002463', X3, X2],add,M3,_) \ fact(['obo:RO_0002444', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002444', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011016', X, Y],add,M1,_) \ fact(['obo:RO_0011004', X, Y],del,_,U) <=> true | fact(['obo:RO_0011004', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002411', Y, X],add,M1,_) \ fact(['obo:RO_0002404', X, Y],del,_,U) <=> true | fact(['obo:RO_0002404', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002404', Y, X],add,M1,_) \ fact(['obo:RO_0002411', X, Y],del,_,U) <=> true | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002254', X, Y],add,M1,_) \ fact(['obo:RO_0002258', X, Y],del,_,U) <=> true | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002463', X, Y],add,M1,_) \ fact(['obo:RO_0002461', X, Y],del,_,U) <=> true | fact(['obo:RO_0002461', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002525', X, Y],add,M1,_) \ fact(['obo:RO_0002523', X, Y],del,_,U) <=> true | fact(['obo:RO_0002523', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004019', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002569', Y, X],add,M1,_) \ fact(['obo:RO_0002380', X, Y],del,_,U) <=> true | fact(['obo:RO_0002380', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002380', Y, X],add,M1,_) \ fact(['obo:RO_0002569', X, Y],del,_,U) <=> true | fact(['obo:RO_0002569', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000301', X, Y],add,M1,_) \ fact(['obo:RO_0000300', X, Y],del,_,U) <=> true | fact(['obo:RO_0000300', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002432', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002103', X, Y],add,M1,_) \ fact(['obo:RO_0000301', X, Y],del,_,U) <=> true | fact(['obo:RO_0000301', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011022', X, Y],add,M1,_) \ fact(['obo:RO_0011003', X, Y],del,_,U) <=> true | fact(['obo:RO_0011003', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011010', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001023', X, Y],add,M1,_) \ fact(['obo:RO_0003302', X, Y],del,_,U) <=> true | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003003', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002468', X, Y],add,M1,_) \ fact(['obo:RO_0002465', X, Y],del,_,U) <=> true | fact(['obo:RO_0002465', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002025', X, Y],add,M1,_) \ fact(['obo:RO_0002211', X, Y],del,_,U) <=> true | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002134', X, Y],add,M1,_) \ fact(['owl:topObjectProperty', X, Y],del,_,U) <=> true | fact(['owl:topObjectProperty', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:BFO_0000051', X1, X2],add,M2,_) \ fact(['obo:RO_0002327', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002327', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002411', X1, X2],add,M2,_), fact(['obo:RO_0002333', X2, X3],add,M3,_) \ fact(['obo:RO_0002566', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002566', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X0, X1],add,M1,_), fact(['obo:RO_0002482', X1, X2],add,M2,_), fact(['obo:RO_0002400', X2, X3],add,M3,_) \ fact(['obo:RO_0002480', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002480', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002201', X, Y1],add,M1,_), fact(['obo:RO_0002201', X, Y2],add,M2,_) \ fact(['owl:sameAs', Y1, Y2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002384', X, _],add,M1,_) \ fact(['obo:CARO_0000000', X],del,_,U) <=> true | fact(['obo:CARO_0000000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:BFO_0000062', X1, X2],add,M2,_) \ fact(['obo:BFO_0000062', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000062', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002515', X, Y],add,M1,_) \ fact(['obo:RO_0002527', X, Y],del,_,U) <=> true | fact(['obo:RO_0002527', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002570', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002462', X, Y],add,M1,_) \ fact(['obo:RO_0002461', X, Y],del,_,U) <=> true | fact(['obo:RO_0002461', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002552', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002007', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002517', Y, X],add,M1,_) \ fact(['obo:RO_0002516', X, Y],del,_,U) <=> true | fact(['obo:RO_0002516', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002516', Y, X],add,M1,_) \ fact(['obo:RO_0002517', X, Y],del,_,U) <=> true | fact(['obo:RO_0002517', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000054', X0, X1],add,M1,_), fact(['obo:RO_0002404', X1, X2],add,M2,_) \ fact(['obo:RO_0009501', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0009501', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002109', Y, X],add,M1,_) \ fact(['obo:RO_0002105', X, Y],del,_,U) <=> true | fact(['obo:RO_0002105', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002105', Y, X],add,M1,_) \ fact(['obo:RO_0002109', X, Y],del,_,U) <=> true | fact(['obo:RO_0002109', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002113', X, Y],add,M1,_) \ fact(['obo:RO_0002130', X, Y],del,_,U) <=> true | fact(['obo:RO_0002130', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002448', X, Y],add,M1,_) \ fact(['obo:RO_0011002', X, Y],del,_,U) <=> true | fact(['obo:RO_0011002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002234', X, Y],add,M1,_) \ fact(['obo:RO_0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0040036', X, Y],add,M1,_) \ fact(['obo:RO_0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002524', X, Y],add,M1,_) \ fact(['obo:RO_0002526', X, Y],del,_,U) <=> true | fact(['obo:RO_0002526', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002572', X, _],add,M1,_) \ fact(['obo:BFO_0000141', X],del,_,U) <=> true | fact(['obo:BFO_0000141', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002445', X, Y],add,M1,_) \ fact(['obo:RO_0002453', X, Y],del,_,U) <=> true | fact(['obo:RO_0002453', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002329', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004028', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002492', X, Y],add,M1,_) \ fact(['obo:RO_0002497', X, Y],del,_,U) <=> true | fact(['obo:RO_0002497', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002018', X, Y],add,M1,_) \ fact(['obo:RO_0002180', X, Y],del,_,U) <=> true | fact(['obo:RO_0002180', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002326', X, Y],add,M1,_) \ fact(['obo:RO_0002216', X, Y],del,_,U) <=> true | fact(['obo:RO_0002216', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002524', X, Y],add,M1,_) \ fact(['obo:RO_0002522', X, Y],del,_,U) <=> true | fact(['obo:RO_0002522', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002332', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003307', X, Y],add,M1,_) \ fact(['obo:RO_0003305', X, Y],del,_,U) <=> true | fact(['obo:RO_0003305', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002511', Y, X],add,M1,_) \ fact(['obo:RO_0002510', X, Y],del,_,U) <=> true | fact(['obo:RO_0002510', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002510', Y, X],add,M1,_) \ fact(['obo:RO_0002511', X, Y],del,_,U) <=> true | fact(['obo:RO_0002511', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003003', X, Y],add,M1,_) \ fact(['obo:RO_0002450', X, Y],del,_,U) <=> true | fact(['obo:RO_0002450', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002625', Y, X],add,M1,_) \ fact(['obo:RO_0002624', X, Y],del,_,U) <=> true | fact(['obo:RO_0002624', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002624', Y, X],add,M1,_) \ fact(['obo:RO_0002625', X, Y],del,_,U) <=> true | fact(['obo:RO_0002625', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002452', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002625', X, Y],add,M1,_) \ fact(['obo:RO_0002619', X, Y],del,_,U) <=> true | fact(['obo:RO_0002619', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002343', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002014', X, Y],add,M1,_) \ fact(['obo:RO_0002013', X, Y],del,_,U) <=> true | fact(['obo:RO_0002013', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002349', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002513', Y, X],add,M1,_) \ fact(['obo:RO_0002512', X, Y],del,_,U) <=> true | fact(['obo:RO_0002512', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002512', Y, X],add,M1,_) \ fact(['obo:RO_0002513', X, Y],del,_,U) <=> true | fact(['obo:RO_0002513', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002375', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002354', Y, X],add,M1,_) \ fact(['obo:RO_0002297', X, Y],del,_,U) <=> true | fact(['obo:RO_0002297', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002297', Y, X],add,M1,_) \ fact(['obo:RO_0002354', X, Y],del,_,U) <=> true | fact(['obo:RO_0002354', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002507', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002568', X, Y],add,M1,_) \ fact(['obo:RO_0002567', X, Y],del,_,U) <=> true | fact(['obo:RO_0002567', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002224', X0, X1],add,M1,_), fact(['obo:RO_0002230', X1, X2],add,M2,_) \ fact(['obo:RO_0002087', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002087', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002025', X, X1],add,M1,_), fact(['obo:RO_0002233', X1, X2],add,M2,_) \ fact(['obo:RO_0002233', X, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002233', X, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002007', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011003', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002485', X, Y],add,M1,_) \ fact(['obo:RO_0002170', X, Y],del,_,U) <=> true | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000001', X, Y],add,M1,_) \ fact(['obo:RO_0002158', X, Y],del,_,U) <=> true | fact(['obo:RO_0002158', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002627', Y, X],add,M1,_) \ fact(['obo:RO_0002626', X, Y],del,_,U) <=> true | fact(['obo:RO_0002626', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002626', Y, X],add,M1,_) \ fact(['obo:RO_0002627', X, Y],del,_,U) <=> true | fact(['obo:RO_0002627', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002331', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002331', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002476', X, _],add,M1,_) \ fact(['obo:GO_0005634', X],del,_,U) <=> true | fact(['obo:GO_0005634', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002339', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002339', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002339', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001020', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008506', _, X1],add,M1,_) \ fact(['obo:CARO_0001010', X1],del,_,U) <=> true | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004006', X, Y],add,M1,_) \ fact(['obo:RO_0004000', X, Y],del,_,U) <=> true | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002244', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002253', Y, X],add,M1,_) \ fact(['obo:RO_0002252', X, Y],del,_,U) <=> true | fact(['obo:RO_0002252', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002252', Y, X],add,M1,_) \ fact(['obo:RO_0002253', X, Y],del,_,U) <=> true | fact(['obo:RO_0002253', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002447', X, Y],add,M1,_) \ fact(['obo:RO_0002436', X, Y],del,_,U) <=> true | fact(['obo:RO_0002436', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002558', Y, X],add,M1,_) \ fact(['obo:RO_0002472', X, Y],del,_,U) <=> true | fact(['obo:RO_0002472', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002472', Y, X],add,M1,_) \ fact(['obo:RO_0002558', X, Y],del,_,U) <=> true | fact(['obo:RO_0002558', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002225', X, Y],add,M1,_) \ fact(['obo:RO_0002202', X, Y],del,_,U) <=> true | fact(['obo:RO_0002202', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003301', Y, X],add,M1,_) \ fact(['obo:RO_0002615', X, Y],del,_,U) <=> true | fact(['obo:RO_0002615', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002615', Y, X],add,M1,_) \ fact(['obo:RO_0003301', X, Y],del,_,U) <=> true | fact(['obo:RO_0003301', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002216', X, Y],add,M1,_) \ fact(['obo:RO_0002500', X, Y],del,_,U) <=> true | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002130', Y, X],add,M1,_) \ fact(['obo:RO_0002006', X, Y],del,_,U) <=> true | fact(['obo:RO_0002006', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002006', Y, X],add,M1,_) \ fact(['obo:RO_0002130', X, Y],del,_,U) <=> true | fact(['obo:RO_0002130', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002333', Y, X],add,M1,_) \ fact(['obo:RO_0002327', X, Y],del,_,U) <=> true | fact(['obo:RO_0002327', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', Y, X],add,M1,_) \ fact(['obo:RO_0002333', X, Y],del,_,U) <=> true | fact(['obo:RO_0002333', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002578', X, X2],add,M1,_), fact(['obo:RO_0002025', X, X1],add,M2,_) \ fact(['obo:RO_0002578', X1, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002578', X1, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011009', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002354', X, Y],add,M1,_) \ fact(['obo:RO_0002353', X, Y],del,_,U) <=> true | fact(['obo:RO_0002353', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002406', X0, X1],add,M1,_), fact(['obo:RO_0002407', X1, X2],add,M2,_) \ fact(['obo:RO_0002407', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002578', X, Y],add,M1,_) \ fact(['obo:RO_0002412', X, Y],del,_,U) <=> true | fact(['obo:RO_0002412', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002473', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008508', X, Y],add,M1,_) \ fact(['obo:RO_0002619', X, Y],del,_,U) <=> true | fact(['obo:RO_0002619', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000300', _, X1],add,M1,_) \ fact(['obo:CL_0000540', X1],del,_,U) <=> true | fact(['obo:CL_0000540', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002608', Y, X],add,M1,_) \ fact(['obo:RO_0002500', X, Y],del,_,U) <=> true | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002500', Y, X],add,M1,_) \ fact(['obo:RO_0002608', X, Y],del,_,U) <=> true | fact(['obo:RO_0002608', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002134', Y, X],add,M1,_) \ fact(['obo:RO_0002005', X, Y],del,_,U) <=> true | fact(['obo:RO_0002005', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002005', Y, X],add,M1,_) \ fact(['obo:RO_0002134', X, Y],del,_,U) <=> true | fact(['obo:RO_0002134', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004025', _, X1],add,M1,_) \ fact(['obo:CARO_0000006', X1],del,_,U) <=> true | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002255', Y, X],add,M1,_) \ fact(['obo:RO_0002254', X, Y],del,_,U) <=> true | fact(['obo:RO_0002254', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002254', Y, X],add,M1,_) \ fact(['obo:RO_0002255', X, Y],del,_,U) <=> true | fact(['obo:RO_0002255', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002256', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011009', X, Y],add,M1,_) \ fact(['obo:RO_0011021', X, Y],del,_,U) <=> true | fact(['obo:RO_0011021', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002255', X, Y],add,M1,_) \ fact(['obo:RO_0002385', X, Y],del,_,U) <=> true | fact(['obo:RO_0002385', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002258', X, _],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002257', X, Y],add,M1,_) \ fact(['obo:RO_0002286', X, Y],del,_,U) <=> true | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002376', X, Y],add,M1,_) \ fact(['obo:RO_0002375', X, Y],del,_,U) <=> true | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002211', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002407', X0, X1],add,M1,_), fact(['obo:RO_0002406', X1, X2],add,M2,_) \ fact(['obo:RO_0002407', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000063', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002584', X, Y],add,M1,_) \ fact(['obo:RO_0002595', X, Y],del,_,U) <=> true | fact(['obo:RO_0002595', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002207', X, Y],add,M1,_) \ fact(['obo:RO_0002202', X, Y],del,_,U) <=> true | fact(['obo:RO_0002202', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002233', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002497', X0, X1],add,M1,_), fact(['obo:RO_0002082', X1, X2],add,M2,_) \ fact(['obo:RO_0002497', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002455', X, Y],add,M1,_) \ fact(['obo:RO_0002442', X, Y],del,_,U) <=> true | fact(['obo:RO_0002442', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002012', X, Y],add,M1,_) \ fact(['obo:RO_0002418', X, Y],del,_,U) <=> true | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002630', Y, X],add,M1,_) \ fact(['obo:RO_0002023', X, Y],del,_,U) <=> true | fact(['obo:RO_0002023', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002023', Y, X],add,M1,_) \ fact(['obo:RO_0002630', X, Y],del,_,U) <=> true | fact(['obo:RO_0002630', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002585', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002105', X, Y],add,M1,_) \ fact(['obo:RO_0002120', X, Y],del,_,U) <=> true | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002211', X, Y],add,M1,_) \ fact(['obo:RO_0002411', X, Y],del,_,U) <=> true | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002005', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002476', X, Y],add,M1,_) \ fact(['obo:RO_0002258', X, Y],del,_,U) <=> true | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002636', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002108', Y, X],add,M1,_) \ fact(['obo:RO_0002107', X, Y],del,_,U) <=> true | fact(['obo:RO_0002107', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002107', Y, X],add,M1,_) \ fact(['obo:RO_0002108', X, Y],del,_,U) <=> true | fact(['obo:RO_0002108', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001022', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002210', X, Y],add,M1,_) \ fact(['obo:RO_0002203', X, Y],del,_,U) <=> true | fact(['obo:RO_0002203', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002114', X, Y],add,M1,_) \ fact(['obo:RO_0002120', X, Y],del,_,U) <=> true | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004026', X, Y],add,M1,_) \ fact(['obo:RO_0040035', X, Y],del,_,U) <=> true | fact(['obo:RO_0040035', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002437', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002018', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009002', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008504', X, Y],add,M1,_) \ fact(['obo:RO_0002445', X, Y],del,_,U) <=> true | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002496', X0, X1],add,M1,_), fact(['obo:BFO_0000062', X1, X2],add,M2,_) \ fact(['obo:RO_0002496', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002519', Y, X],add,M1,_) \ fact(['obo:RO_0002518', X, Y],del,_,U) <=> true | fact(['obo:RO_0002518', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002518', Y, X],add,M1,_) \ fact(['obo:RO_0002519', X, Y],del,_,U) <=> true | fact(['obo:RO_0002519', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002414', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002352', X3, X1],add,M1,_), fact(['obo:RO_0002333', X2, X3],add,M2,_), fact(['obo:RO_0002013', X, X1],add,M3,_) \ fact(['obo:RO_0002578', X2, X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002578', X2, X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002180', X1, X],add,M1,_), fact(['obo:BFO_0000015', X1],add,M2,_), fact(['obo:BFO_0000015', X],add,M3,_) \ fact(['obo:RO_0002018', X1, X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002018', X1, X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X, Y],add,M1,_) \ fact(['obo:RO_0002216', X, Y],del,_,U) <=> true | fact(['obo:RO_0002216', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003310', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002635', X, Y],add,M1,_) \ fact(['obo:RO_0002445', X, Y],del,_,U) <=> true | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002216', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002216', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002373', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002285', X, Y],add,M1,_) \ fact(['obo:RO_0002258', X, Y],del,_,U) <=> true | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X0, X1],add,M1,_), fact(['obo:RO_0002215', X1, X2],add,M2,_) \ fact(['obo:RO_0002584', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002584', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002204', _, X1],add,M1,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011008', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X0, X1],add,M1,_), fact(['obo:RO_0002131', X1, X2],add,M2,_) \ fact(['obo:RO_0002131', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002131', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002591', X, Y],add,M1,_) \ fact(['obo:RO_0002233', X, Y],del,_,U) <=> true | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002411', X, X1],add,M1,_), fact(['obo:RO_0002131', X, X1],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002411', X, X1],add,M1,_), fact(['obo:RO_0002131', X, X1],add,M2,_) \ fact(['owl:Nothing', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002021', X, Y],add,M1,_) \ fact(['obo:RO_0002479', X, Y],del,_,U) <=> true | fact(['obo:RO_0002479', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002508', X, Y],add,M1,_) \ fact(['obo:RO_0002566', X, Y],del,_,U) <=> true | fact(['obo:RO_0002566', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011002', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0072519', X],add,M1,_) \ fact(['obo:RO_0002468', X, X],del,_,U) <=> true | fact(['obo:RO_0002468', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002507', X, Y],add,M1,_) \ fact(['obo:RO_0002509', X, Y],del,_,U) <=> true | fact(['obo:RO_0002509', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000066', X1, X0],add,M1,_), fact(['obo:RO_0002234', X1, X2],add,M2,_) \ fact(['obo:RO_0003000', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0003000', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002437', X, Y],add,M1,_) \ fact(['obo:RO_0002434', X, Y],del,_,U) <=> true | fact(['obo:RO_0002434', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008507', X, Y],add,M1,_) \ fact(['obo:RO_0002618', X, Y],del,_,U) <=> true | fact(['obo:RO_0002618', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002130', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002375', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002411', X, Y],add,M1,_) \ fact(['obo:BFO_0000063', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000063', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:RO_0002210', X1, X2],add,M2,_) \ fact(['obo:RO_0002287', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002287', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002428', X, Y],add,M1,_) \ fact(['obo:RO_0002431', X, Y],del,_,U) <=> true | fact(['obo:RO_0002431', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003301', X, X],add,M1,_) \ fact(['owl:Nothing', X, X],del,_,U) <=> true | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002254', X0, X1],add,M1,_), fact(['obo:RO_0002162', X1, X2],add,M2,_) \ fact(['obo:RO_0002162', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002131', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002131', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002013', X, Y],add,M1,_) \ fact(['obo:RO_0002017', X, Y],del,_,U) <=> true | fact(['obo:RO_0002017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002249', Y, X],add,M1,_) \ fact(['obo:RO_0002248', X, Y],del,_,U) <=> true | fact(['obo:RO_0002248', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002248', Y, X],add,M1,_) \ fact(['obo:RO_0002249', X, Y],del,_,U) <=> true | fact(['obo:RO_0002249', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000302', X, Y],add,M1,_) \ fact(['obo:RO_0000300', X, Y],del,_,U) <=> true | fact(['obo:RO_0000300', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002220', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002445', X, Y],add,M1,_) \ fact(['obo:RO_0002443', X, Y],del,_,U) <=> true | fact(['obo:RO_0002443', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002233', X, Y],add,M1,_) \ fact(['obo:RO_0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002454', X, Y],add,M1,_) \ fact(['obo:RO_0002440', X, Y],del,_,U) <=> true | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002534', X],add,M1,_) \ fact(['obo:RO_0002532', X],del,_,U) <=> true | fact(['obo:RO_0002532', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002177', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004023', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002489', X, Y],add,M1,_) \ fact(['obo:RO_0002488', X, Y],del,_,U) <=> true | fact(['obo:RO_0002488', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004018', Y, X],add,M1,_) \ fact(['obo:RO_0004017', X, Y],del,_,U) <=> true | fact(['obo:RO_0004017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004017', Y, X],add,M1,_) \ fact(['obo:RO_0004018', X, Y],del,_,U) <=> true | fact(['obo:RO_0004018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004029', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002444', X, Y],add,M1,_) \ fact(['obo:RO_0002454', X, Y],del,_,U) <=> true | fact(['obo:RO_0002454', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004020', _, X1],add,M1,_) \ fact(['obo:CARO_0000006', X1],del,_,U) <=> true | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002450', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002203', X, Y],add,M1,_) \ fact(['obo:RO_0002388', X, Y],del,_,U) <=> true | fact(['obo:RO_0002388', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002120', X, Y],add,M1,_) \ fact(['obo:RO_0000302', X, Y],del,_,U) <=> true | fact(['obo:RO_0000302', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002465', X, Y],add,M1,_) \ fact(['obo:RO_0002563', X, Y],del,_,U) <=> true | fact(['obo:RO_0002563', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002160', X, Y],add,M1,_) \ fact(['obo:RO_0002162', X, Y],del,_,U) <=> true | fact(['obo:RO_0002162', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002131', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002131', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002203', X, Y],add,M1,_) \ fact(['obo:RO_0002387', X, Y],del,_,U) <=> true | fact(['obo:RO_0002387', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003002', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002467', X, Y],add,M1,_) \ fact(['obo:RO_0002465', X, Y],del,_,U) <=> true | fact(['obo:RO_0002465', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002529', X, Y],add,M1,_) \ fact(['obo:RO_0002527', X, Y],del,_,U) <=> true | fact(['obo:RO_0002527', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002254', X, _],add,M1,_) \ fact(['obo:CARO_0000000', X],del,_,U) <=> true | fact(['obo:CARO_0000000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002372', X, Y],add,M1,_) \ fact(['obo:RO_0002567', X, Y],del,_,U) <=> true | fact(['obo:RO_0002567', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002629', Y, X],add,M1,_) \ fact(['obo:RO_0002024', X, Y],del,_,U) <=> true | fact(['obo:RO_0002024', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002024', Y, X],add,M1,_) \ fact(['obo:RO_0002629', X, Y],del,_,U) <=> true | fact(['obo:RO_0002629', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002500', X, Y],add,M1,_) \ fact(['obo:RO_0002595', X, Y],del,_,U) <=> true | fact(['obo:RO_0002595', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002556', X, Y],add,M1,_) \ fact(['obo:RO_0002454', X, Y],del,_,U) <=> true | fact(['obo:RO_0002454', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002304', X, Y],add,M1,_) \ fact(['obo:RO_0002411', X, Y],del,_,U) <=> true | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002619', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002577', X],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002492', X, Y],add,M1,_) \ fact(['obo:RO_0002490', X, Y],del,_,U) <=> true | fact(['obo:RO_0002490', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002438', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008503', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002248', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002202', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002325', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001021', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002297', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002488', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002488', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002488', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002298', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002292', Y, X],add,M1,_) \ fact(['obo:RO_0002206', X, Y],del,_,U) <=> true | fact(['obo:RO_0002206', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002206', Y, X],add,M1,_) \ fact(['obo:RO_0002292', X, Y],del,_,U) <=> true | fact(['obo:RO_0002292', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0010002', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002226', X, Y],add,M1,_) \ fact(['obo:RO_0002258', X, Y],del,_,U) <=> true | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002004', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002641', X, Y],add,M1,_) \ fact(['obo:RO_0002635', X, Y],del,_,U) <=> true | fact(['obo:RO_0002635', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002630', X, Y],add,M1,_) \ fact(['obo:RO_0002212', X, Y],del,_,U) <=> true | fact(['obo:RO_0002212', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002157', X, Y],add,M1,_) \ fact(['obo:RO_0002320', X, Y],del,_,U) <=> true | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002295', X, Y],add,M1,_) \ fact(['obo:RO_0002324', X, Y],del,_,U) <=> true | fact(['obo:RO_0002324', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002570', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002595', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002026', X, _],add,M1,_) \ fact(['foaf:image', X],del,_,U) <=> true | fact(['foaf:image', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002102', X, _],add,M1,_) \ fact(['obo:CL_0000540', X],del,_,U) <=> true | fact(['obo:CL_0000540', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002623', Y, X],add,M1,_) \ fact(['obo:RO_0002622', X, Y],del,_,U) <=> true | fact(['obo:RO_0002622', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002622', Y, X],add,M1,_) \ fact(['obo:RO_0002623', X, Y],del,_,U) <=> true | fact(['obo:RO_0002623', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003306', X, Y],add,M1,_) \ fact(['obo:RO_0003304', X, Y],del,_,U) <=> true | fact(['obo:RO_0003304', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009001', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001018', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002115', X, Y],add,M1,_) \ fact(['obo:RO_0002103', X, Y],del,_,U) <=> true | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002598', X, Y],add,M1,_) \ fact(['obo:RO_0002596', X, Y],del,_,U) <=> true | fact(['obo:RO_0002596', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002638', X, Y],add,M1,_) \ fact(['obo:RO_0002634', X, Y],del,_,U) <=> true | fact(['obo:RO_0002634', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004046', X, Y],add,M1,_) \ fact(['obo:RO_0002418', X, Y],del,_,U) <=> true | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002150', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002607', X, Y],add,M1,_) \ fact(['obo:RO_0002610', X, Y],del,_,U) <=> true | fact(['obo:RO_0002610', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002207', X0, X1],add,M1,_), fact(['obo:RO_0001025', X1, X2],add,M2,_) \ fact(['obo:RO_0002226', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002226', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002008', _, X1],add,M1,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002514', X, _],add,M1,_) \ fact(['obo:RO_0002532', X],del,_,U) <=> true | fact(['obo:RO_0002532', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002512', X, Y],add,M1,_) \ fact(['obo:RO_0002330', X, Y],del,_,U) <=> true | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002213', X, Y],add,M1,_) \ fact(['obo:RO_0002304', X, Y],del,_,U) <=> true | fact(['obo:RO_0002304', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008505', _, X1],add,M1,_) \ fact(['obo:CARO_0001010', X1],del,_,U) <=> true | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002313', X, Y],add,M1,_) \ fact(['obo:RO_0002337', X, Y],del,_,U) <=> true | fact(['obo:RO_0002337', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004015', X, Y],add,M1,_) \ fact(['obo:RO_0004010', X, Y],del,_,U) <=> true | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004028', X, _],add,M1,_) \ fact(['obo:BFO_0000017', X],del,_,U) <=> true | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002085', X, Y],add,M1,_), fact(['obo:RO_0002085', Y, Z],add,M2,_) \ fact(['obo:RO_0002085', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002085', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002202', X, Y],add,M1,_) \ fact(['obo:RO_0002258', X, Y],del,_,U) <=> true | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002303', _, X1],add,M1,_) \ fact(['obo:ENVO_01000254', X1],del,_,U) <=> true | fact(['obo:ENVO_01000254', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002446', X, Y],add,M1,_) \ fact(['obo:RO_0002437', X, Y],del,_,U) <=> true | fact(['obo:RO_0002437', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002121', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002121', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002121', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002233', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011007', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004001', X, Y],add,M1,_) \ fact(['obo:RO_0004000', X, Y],del,_,U) <=> true | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002012', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002429', X, Y],add,M1,_) \ fact(['obo:RO_0002428', X, Y],del,_,U) <=> true | fact(['obo:RO_0002428', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002337', _, X1],add,M1,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002111', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002006', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002640', X, Y],add,M1,_) \ fact(['obo:RO_0002634', X, Y],del,_,U) <=> true | fact(['obo:RO_0002634', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002589', X, Y],add,M1,_) \ fact(['obo:RO_0002586', X, Y],del,_,U) <=> true | fact(['obo:RO_0002586', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001023', Y, X],add,M1,_) \ fact(['obo:RO_0001021', X, Y],del,_,U) <=> true | fact(['obo:RO_0001021', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001021', Y, X],add,M1,_) \ fact(['obo:RO_0001023', X, Y],del,_,U) <=> true | fact(['obo:RO_0001023', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002508', Y, X],add,M1,_) \ fact(['obo:RO_0002507', X, Y],del,_,U) <=> true | fact(['obo:RO_0002507', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002507', Y, X],add,M1,_) \ fact(['obo:RO_0002508', X, Y],del,_,U) <=> true | fact(['obo:RO_0002508', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004032', X, Y],add,M1,_) \ fact(['obo:RO_0002264', X, Y],del,_,U) <=> true | fact(['obo:RO_0002264', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002012', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002630', X1, X2],add,M2,_), fact(['obo:RO_0002333', X2, X3],add,M3,_) \ fact(['obo:RO_0002449', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002449', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002232', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002305', X1, X2],add,M2,_) \ fact(['obo:RO_0004035', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004035', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X0, X1],add,M1,_), fact(['obo:RO_0002202', X1, X2],add,M2,_) \ fact(['obo:RO_0002254', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002254', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002563', X, Y],add,M1,_) \ fact(['obo:RO_0002464', X, Y],del,_,U) <=> true | fact(['obo:RO_0002464', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011007', X, Y],add,M1,_) \ fact(['obo:RO_0011023', X, Y],del,_,U) <=> true | fact(['obo:RO_0011023', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002255', X, Y],add,M1,_) \ fact(['obo:RO_0002286', X, Y],del,_,U) <=> true | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002476', _, X1],add,M1,_) \ fact(['obo:GO_0005634', X1],del,_,U) <=> true | fact(['obo:GO_0005634', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002005', _, X1],add,M1,_) \ fact(['obo:CARO_0001001', X1],del,_,U) <=> true | fact(['obo:CARO_0001001', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011010', X, Y],add,M1,_) \ fact(['obo:RO_0011021', X, Y],del,_,U) <=> true | fact(['obo:RO_0011021', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002593', X, Y],add,M1,_) \ fact(['obo:RO_0002497', X, Y],del,_,U) <=> true | fact(['obo:RO_0002497', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003003', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002349', _, X1],add,M1,_) \ fact(['obo:CL_0000000', X1],del,_,U) <=> true | fact(['obo:CL_0000000', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002296', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004047', X, Y],add,M1,_) \ fact(['obo:RO_0002418', X, Y],del,_,U) <=> true | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008502', X, Y],add,M1,_) \ fact(['obo:RO_0002440', X, Y],del,_,U) <=> true | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004002', X, Y],add,M1,_) \ fact(['obo:RO_0004000', X, Y],del,_,U) <=> true | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002383', X, Y],add,M1,_) \ fact(['obo:RO_0002376', X, Y],del,_,U) <=> true | fact(['obo:RO_0002376', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002451', X, Y],add,M1,_) \ fact(['obo:RO_0002321', X, Y],del,_,U) <=> true | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002313', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002408', X0, X1],add,M1,_), fact(['obo:RO_0002409', X1, X2],add,M2,_) \ fact(['obo:RO_0002409', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002409', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004016', X, Y],add,M1,_) \ fact(['obo:RO_0004010', X, Y],del,_,U) <=> true | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004024', X, Y],add,M1,_) \ fact(['obo:RO_0004023', X, Y],del,_,U) <=> true | fact(['obo:RO_0004023', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002256', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002315', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002511', X, Y],add,M1,_) \ fact(['obo:RO_0002330', X, Y],del,_,U) <=> true | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002150', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002597', X, Y],add,M1,_) \ fact(['obo:RO_0002596', X, Y],del,_,U) <=> true | fact(['obo:RO_0002596', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002404', X, X1],add,M1,_), fact(['obo:RO_0002131', X, X1],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002404', X, X1],add,M1,_), fact(['obo:RO_0002131', X, X1],add,M2,_) \ fact(['owl:Nothing', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002619', Y, X],add,M1,_) \ fact(['obo:RO_0002618', X, Y],del,_,U) <=> true | fact(['obo:RO_0002618', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002618', Y, X],add,M1,_) \ fact(['obo:RO_0002619', X, Y],del,_,U) <=> true | fact(['obo:RO_0002619', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002591', X, Y],add,M1,_) \ fact(['obo:RO_0002592', X, Y],del,_,U) <=> true | fact(['obo:RO_0002592', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002388', X, Y],add,M1,_) \ fact(['obo:RO_0002387', X, Y],del,_,U) <=> true | fact(['obo:RO_0002387', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002206', X, _],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002406', X, Y],add,M1,_) \ fact(['obo:RO_0002629', X, Y],del,_,U) <=> true | fact(['obo:RO_0002629', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002409', X0, X1],add,M1,_), fact(['obo:RO_0002408', X1, X2],add,M2,_) \ fact(['obo:RO_0002409', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002409', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003308', X, Y],add,M1,_) \ fact(['obo:RO_0002610', X, Y],del,_,U) <=> true | fact(['obo:RO_0002610', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002209', Y, X],add,M1,_) \ fact(['obo:RO_0002208', X, Y],del,_,U) <=> true | fact(['obo:RO_0002208', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002208', Y, X],add,M1,_) \ fact(['obo:RO_0002209', X, Y],del,_,U) <=> true | fact(['obo:RO_0002209', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X0, X1],add,M1,_), fact(['obo:RO_0002211', X1, X2],add,M2,_) \ fact(['obo:RO_0002596', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002596', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004024', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004008', X, Y],add,M1,_) \ fact(['obo:RO_0002234', X, Y],del,_,U) <=> true | fact(['obo:RO_0002234', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003002', X, Y],add,M1,_) \ fact(['obo:RO_0002449', X, Y],del,_,U) <=> true | fact(['obo:RO_0002449', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002404', X, Y],add,M1,_) \ fact(['obo:RO_0002427', X, Y],del,_,U) <=> true | fact(['obo:RO_0002427', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002258', X, Y],add,M1,_) \ fact(['obo:RO_0002324', X, Y],del,_,U) <=> true | fact(['obo:RO_0002324', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002212', X, Y],add,M1,_) \ fact(['obo:RO_0002305', X, Y],del,_,U) <=> true | fact(['obo:RO_0002305', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002634', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002436', X, Y],add,M1,_) \ fact(['obo:RO_0002434', X, Y],del,_,U) <=> true | fact(['obo:RO_0002434', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002574', X, Y],add,M1,_) \ fact(['obo:RO_0002437', X, Y],del,_,U) <=> true | fact(['obo:RO_0002437', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001022', Y, X],add,M1,_) \ fact(['obo:RO_0001020', X, Y],del,_,U) <=> true | fact(['obo:RO_0001020', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001020', Y, X],add,M1,_) \ fact(['obo:RO_0001022', X, Y],del,_,U) <=> true | fact(['obo:RO_0001022', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002220', X, Y],add,M1,_) \ fact(['obo:RO_0002163', X, Y],del,_,U) <=> true | fact(['obo:RO_0002163', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002130', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002130', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002130', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002440', Y, X],add,M1,_) \ fact(['obo:RO_0002440', X, Y],del,_,U) <=> true | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000300', X, _],add,M1,_) \ fact(['obo:CL_0000540', X],del,_,U) <=> true | fact(['obo:CL_0000540', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002588', X, Y],add,M1,_) \ fact(['obo:RO_0002592', X, Y],del,_,U) <=> true | fact(['obo:RO_0002592', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004010', X, Y],add,M1,_) \ fact(['obo:RO_0004018', X, Y],del,_,U) <=> true | fact(['obo:RO_0004018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002414', X, Y],add,M1,_) \ fact(['obo:RO_0002411', X, Y],del,_,U) <=> true | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002588', X, Y],add,M1,_) \ fact(['obo:RO_0002297', X, Y],del,_,U) <=> true | fact(['obo:RO_0002297', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002375', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002630', X, Y],add,M1,_) \ fact(['obo:RO_0002578', X, Y],del,_,U) <=> true | fact(['obo:RO_0002578', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009004', _, X1],add,M1,_) \ fact(['obo:CARO_0001010', X1],del,_,U) <=> true | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002507', X, _],add,M1,_) \ fact(['obo:RO_0002577', X],del,_,U) <=> true | fact(['obo:RO_0002577', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002228', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002258', _, X1],add,M1,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009001', X, X],add,M1,_) \ fact(['owl:Nothing', X, X],del,_,U) <=> true | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004023', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', X0, X1],add,M1,_), fact(['obo:RO_0001025', X2, X1],add,M2,_) \ fact(['obo:RO_0002379', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002379', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002210', Y, X],add,M1,_) \ fact(['obo:RO_0002207', X, Y],del,_,U) <=> true | fact(['obo:RO_0002207', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002207', Y, X],add,M1,_) \ fact(['obo:RO_0002210', X, Y],del,_,U) <=> true | fact(['obo:RO_0002210', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002411', X, Y],add,M1,_), fact(['obo:RO_0002411', Y, Z],add,M2,_) \ fact(['obo:RO_0002411', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002411', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008506', X, Y],add,M1,_) \ fact(['obo:RO_0002321', X, Y],del,_,U) <=> true | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002479', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002355', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009501', X, _],add,M1,_) \ fact(['obo:BFO_0000017', X],del,_,U) <=> true | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X0, X1],add,M1,_), fact(['obo:BFO_0000066', X1, X2],add,M2,_) \ fact(['obo:RO_0002232', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002232', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009002', X, X],add,M1,_) \ fact(['owl:Nothing', X, X],del,_,U) <=> true | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001021', X, Y],add,M1,_) \ fact(['obo:RO_0003302', X, Y],del,_,U) <=> true | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002237', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011003', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002357', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002101', _, X1],add,M1,_) \ fact(['obo:CARO_0001001', X1],del,_,U) <=> true | fact(['obo:CARO_0001001', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011009', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009003', X, X],add,M1,_) \ fact(['owl:Nothing', X, X],del,_,U) <=> true | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002449', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011021', X, Y],add,M1,_) \ fact(['obo:RO_0011003', X, Y],del,_,U) <=> true | fact(['obo:RO_0011003', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009005', X, X],add,M1,_) \ fact(['owl:Nothing', X, X],del,_,U) <=> true | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004024', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004022', X, Y],add,M1,_) \ fact(['obo:RO_0002200', X, Y],del,_,U) <=> true | fact(['obo:RO_0002200', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002624', X, Y],add,M1,_) \ fact(['obo:RO_0002618', X, Y],del,_,U) <=> true | fact(['obo:RO_0002618', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002219', X, Y],add,M1,_) \ fact(['obo:RO_0002220', X, Y],del,_,U) <=> true | fact(['obo:RO_0002220', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002627', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002019', X, Y],add,M1,_) \ fact(['obo:RO_0002233', X, Y],del,_,U) <=> true | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002249', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002286', X, Y],add,M1,_) \ fact(['obo:RO_0002384', X, Y],del,_,U) <=> true | fact(['obo:RO_0002384', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002156', X, Y],add,M1,_) \ fact(['obo:RO_0002320', X, Y],del,_,U) <=> true | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002440', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002348', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002491', X, Y],add,M1,_) \ fact(['obo:RO_0002492', X, Y],del,_,U) <=> true | fact(['obo:RO_0002492', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002211', X1, X2],add,M2,_) \ fact(['obo:RO_0002428', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002428', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002434', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X0, X1],add,M1,_), fact(['obo:BFO_0000066', X1, X2],add,M2,_) \ fact(['obo:RO_0002479', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002479', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004028', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002501', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002418', X, Y],add,M1,_), fact(['obo:RO_0002418', Y, Z],add,M2,_) \ fact(['obo:RO_0002418', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002418', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002488', X, Y],add,M1,_) \ fact(['obo:RO_0002496', X, Y],del,_,U) <=> true | fact(['obo:RO_0002496', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002374', X, Y],add,M1,_) \ fact(['obo:RO_0002156', X, Y],del,_,U) <=> true | fact(['obo:RO_0002156', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002469', X, Y],add,M1,_) \ fact(['obo:RO_0002438', X, Y],del,_,U) <=> true | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002571', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002322', X, Y],add,M1,_) \ fact(['obo:RO_0002321', X, Y],del,_,U) <=> true | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002334', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002150', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002551', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002340', X, Y],add,M1,_) \ fact(['obo:RO_0002020', X, Y],del,_,U) <=> true | fact(['obo:RO_0002020', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002488', X, Y],add,M1,_) \ fact(['obo:RO_0002490', X, Y],del,_,U) <=> true | fact(['obo:RO_0002490', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002353', X, Y],add,M1,_) \ fact(['obo:RO_0000056', X, Y],del,_,U) <=> true | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002336', X, Y],add,M1,_) \ fact(['obo:RO_0002334', X, Y],del,_,U) <=> true | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002113', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002113', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002113', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002431', X, Y],add,M1,_) \ fact(['obo:RO_0002500', X, Y],del,_,U) <=> true | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0010002', Y, X],add,M1,_) \ fact(['obo:RO_0010001', X, Y],del,_,U) <=> true | fact(['obo:RO_0010001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0010001', Y, X],add,M1,_) \ fact(['obo:RO_0010002', X, Y],del,_,U) <=> true | fact(['obo:RO_0010002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002566', X, Y],add,M1,_) \ fact(['obo:RO_0002506', X, Y],del,_,U) <=> true | fact(['obo:RO_0002506', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002414', X, Y],add,M1,_), fact(['obo:RO_0002414', Y, Z],add,M2,_) \ fact(['obo:RO_0002414', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002414', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002618', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002338', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002338', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002338', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:BFO_0000063', X1, X2],add,M2,_) \ fact(['obo:BFO_0000063', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000063', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004010', Y, X],add,M1,_) \ fact(['obo:RO_0004000', X, Y],del,_,U) <=> true | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004000', Y, X],add,M1,_) \ fact(['obo:RO_0004010', X, Y],del,_,U) <=> true | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002264', X, Y],add,M1,_) \ fact(['obo:RO_0002500', X, Y],del,_,U) <=> true | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002352', X, Y],add,M1,_) \ fact(['obo:RO_0000056', X, Y],del,_,U) <=> true | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002100', X, _],add,M1,_) \ fact(['obo:CL_0000540', X],del,_,U) <=> true | fact(['obo:CL_0000540', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002207', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002225', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002225', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002344', X, Y],add,M1,_) \ fact(['obo:RO_0002337', X, Y],del,_,U) <=> true | fact(['obo:RO_0002337', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002209', X, Y],add,M1,_) \ fact(['obo:RO_0002445', X, Y],del,_,U) <=> true | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002501', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003305', X, Y],add,M1,_) \ fact(['obo:RO_0003304', X, Y],del,_,U) <=> true | fact(['obo:RO_0003304', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002002', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004011', Y, X],add,M1,_) \ fact(['obo:RO_0004001', X, Y],del,_,U) <=> true | fact(['obo:RO_0004001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004001', Y, X],add,M1,_) \ fact(['obo:RO_0004011', X, Y],del,_,U) <=> true | fact(['obo:RO_0004011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002206', X, Y],add,M1,_) \ fact(['obo:RO_0002330', X, Y],del,_,U) <=> true | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002356', X, Y],add,M1,_) \ fact(['obo:RO_0002295', X, Y],del,_,U) <=> true | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002461', X0, X1],add,M1,_), fact(['obo:RO_0002465', X1, X2],add,M2,_), fact(['obo:RO_0002461', X3, X2],add,M3,_) \ fact(['obo:RO_0002440', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002440', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002287', X, Y],add,M1,_) \ fact(['obo:RO_0002286', X, Y],del,_,U) <=> true | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002578', X, X2],add,M1,_), fact(['obo:RO_0002333', X2, X3],add,M2,_), fact(['obo:RO_0002333', X, X1],add,M3,_), fact(['obo:GO_0016301', X],add,M4,_) \ fact(['obo:RO_0002447', X1, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4],M), fact(['obo:RO_0002447', X1, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002629', X1, X2],add,M2,_), fact(['obo:RO_0002333', X2, X3],add,M3,_) \ fact(['obo:RO_0002450', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002450', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004025', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0004025', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004025', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002471', X, Y],add,M1,_) \ fact(['obo:RO_0002438', X, Y],del,_,U) <=> true | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002614', X, Y],add,M1,_) \ fact(['obo:RO_0002616', X, Y],del,_,U) <=> true | fact(['obo:RO_0002616', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002227', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002431', X, Y],add,M1,_) \ fact(['obo:RO_0002264', X, Y],del,_,U) <=> true | fact(['obo:RO_0002264', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002480', X, Y],add,M1,_) \ fact(['obo:RO_0002436', X, Y],del,_,U) <=> true | fact(['obo:RO_0002436', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002360', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002201', Y, X],add,M1,_) \ fact(['obo:RO_0002200', X, Y],del,_,U) <=> true | fact(['obo:RO_0002200', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002200', Y, X],add,M1,_) \ fact(['obo:RO_0002201', X, Y],del,_,U) <=> true | fact(['obo:RO_0002201', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002016', X, Y],add,M1,_) \ fact(['obo:RO_0002336', X, Y],del,_,U) <=> true | fact(['obo:RO_0002336', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002008', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008505', X, Y],add,M1,_) \ fact(['obo:RO_0002321', X, Y],del,_,U) <=> true | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002626', X, Y],add,M1,_) \ fact(['obo:RO_0002574', X, Y],del,_,U) <=> true | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000052', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002314', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002314', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002215', X0, X1],add,M1,_), fact(['obo:RO_0002212', X1, X2],add,M2,_) \ fact(['obo:RO_0002597', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002597', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002177', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011002', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002299', X, Y],add,M1,_) \ fact(['obo:RO_0040036', X, Y],del,_,U) <=> true | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002496', X0, X1],add,M1,_), fact(['obo:RO_0002082', X1, X2],add,M2,_) \ fact(['obo:RO_0002496', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011008', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002411', X0, X1],add,M1,_), fact(['obo:RO_0002402', X1, X2],add,M2,_) \ fact(['obo:RO_0002403', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002403', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002435', Y, X],add,M1,_) \ fact(['obo:RO_0002435', X, Y],del,_,U) <=> true | fact(['obo:RO_0002435', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002428', X, Y],add,M1,_) \ fact(['obo:RO_0002263', X, Y],del,_,U) <=> true | fact(['obo:RO_0002263', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002434', Y, X],add,M1,_) \ fact(['obo:RO_0002434', X, Y],del,_,U) <=> true | fact(['obo:RO_0002434', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002427', X, Y],add,M1,_) \ fact(['obo:RO_0002501', X, Y],del,_,U) <=> true | fact(['obo:RO_0002501', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002102', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002102', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002102', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002303', X, _],add,M1,_) \ fact(['obo:CARO_0001010', X],del,_,U) <=> true | fact(['obo:CARO_0001010', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X0, X1],add,M1,_), fact(['obo:RO_0002211', X1, X2],add,M2,_) \ fact(['obo:RO_0002211', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002211', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002595', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002406', X0, X1],add,M1,_), fact(['obo:RO_0002406', X1, X2],add,M2,_) \ fact(['obo:RO_0002407', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0004842', X],add,M1,_) \ fact(['obo:RO_0002482', X, X],del,_,U) <=> true | fact(['obo:RO_0002482', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002567', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002121', X, Y],add,M1,_) \ fact(['obo:RO_0002110', X, Y],del,_,U) <=> true | fact(['obo:RO_0002110', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002302', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004033', X, Y],add,M1,_) \ fact(['obo:RO_0002264', X, Y],del,_,U) <=> true | fact(['obo:RO_0002264', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002335', X, Y],add,M1,_) \ fact(['obo:RO_0002334', X, Y],del,_,U) <=> true | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002554', X, Y],add,M1,_) \ fact(['obo:RO_0002453', X, Y],del,_,U) <=> true | fact(['obo:RO_0002453', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002177', X, Y],add,M1,_) \ fact(['obo:RO_0002567', X, Y],del,_,U) <=> true | fact(['obo:RO_0002567', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002576', _, X1],add,M1,_) \ fact(['obo:CARO_0000003', X1],del,_,U) <=> true | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002437', Y, X],add,M1,_) \ fact(['obo:RO_0002437', X, Y],del,_,U) <=> true | fact(['obo:RO_0002437', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002345', X, Y],add,M1,_) \ fact(['obo:RO_0002020', X, Y],del,_,U) <=> true | fact(['obo:RO_0002020', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009005', X, Y],add,M1,_) \ fact(['obo:RO_0009001', X, Y],del,_,U) <=> true | fact(['obo:RO_0009001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002436', Y, X],add,M1,_) \ fact(['obo:RO_0002436', X, Y],del,_,U) <=> true | fact(['obo:RO_0002436', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002132', X, _],add,M1,_) \ fact(['obo:CARO_0001001', X],del,_,U) <=> true | fact(['obo:CARO_0001001', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002405', X, Y],add,M1,_) \ fact(['obo:RO_0002404', X, Y],del,_,U) <=> true | fact(['obo:RO_0002404', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004011', X, Y],add,M1,_) \ fact(['obo:RO_0004010', X, Y],del,_,U) <=> true | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002111', X, Y],add,M1,_) \ fact(['owl:topObjectProperty', X, Y],del,_,U) <=> true | fact(['owl:topObjectProperty', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002312', X, Y],add,M1,_) \ fact(['obo:RO_0002320', X, Y],del,_,U) <=> true | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002246', X, Y],add,M1,_) \ fact(['obo:RO_0002206', X, Y],del,_,U) <=> true | fact(['obo:RO_0002206', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004025', X, Y],add,M1,_) \ fact(['obo:RO_0004023', X, Y],del,_,U) <=> true | fact(['obo:RO_0004023', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002430', X, Y],add,M1,_) \ fact(['obo:RO_0002428', X, Y],del,_,U) <=> true | fact(['obo:RO_0002428', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002510', X, Y],add,M1,_) \ fact(['obo:RO_0002330', X, Y],del,_,U) <=> true | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002469', Y, X],add,M1,_) \ fact(['obo:RO_0002457', X, Y],del,_,U) <=> true | fact(['obo:RO_0002457', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002457', Y, X],add,M1,_) \ fact(['obo:RO_0002469', X, Y],del,_,U) <=> true | fact(['obo:RO_0002469', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002104', _, X1],add,M1,_) \ fact(['obo:CARO_0000006', X1],del,_,U) <=> true | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002331', X0, X1],add,M1,_), fact(['obo:RO_0002212', X1, X2],add,M2,_) \ fact(['obo:RO_0002430', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002430', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002131', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002327', X0, X1],add,M1,_), fact(['obo:RO_0002304', X1, X2],add,M2,_) \ fact(['obo:RO_0004034', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0004034', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002418', X, Y],add,M1,_) \ fact(['obo:RO_0002501', X, Y],del,_,U) <=> true | fact(['obo:RO_0002501', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002330', X, _],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011008', X, Y],add,M1,_) \ fact(['obo:RO_0011024', X, Y],del,_,U) <=> true | fact(['obo:RO_0011024', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002334', X, Y],add,M1,_), fact(['obo:RO_0002334', Y, Z],add,M2,_) \ fact(['obo:RO_0002334', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002334', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002253', X, Y],add,M1,_) \ fact(['obo:RO_0002375', X, Y],del,_,U) <=> true | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002010', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0010002', _, X1],add,M1,_) \ fact(['obo:BFO_0000031', X1],del,_,U) <=> true | fact(['obo:BFO_0000031', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002092', Y, X],add,M1,_) \ fact(['obo:RO_0002085', X, Y],del,_,U) <=> true | fact(['obo:RO_0002085', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002085', Y, X],add,M1,_) \ fact(['obo:RO_0002092', X, Y],del,_,U) <=> true | fact(['obo:RO_0002092', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002220', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002453', X, Y],add,M1,_) \ fact(['obo:RO_0002440', X, Y],del,_,U) <=> true | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002444', X, Y],add,M1,_) \ fact(['obo:RO_0002443', X, Y],del,_,U) <=> true | fact(['obo:RO_0002443', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002507', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002509', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002509', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002533', X],add,M1,_) \ fact(['obo:RO_0002532', X],del,_,U) <=> true | fact(['obo:RO_0002532', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004008', X, Y],add,M1,_) \ fact(['obo:RO_0004007', X, Y],del,_,U) <=> true | fact(['obo:RO_0004007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002409', X0, X1],add,M1,_), fact(['obo:RO_0002409', X1, X2],add,M2,_) \ fact(['obo:RO_0002407', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002213', X, Y],add,M1,_) \ fact(['obo:RO_0002211', X, Y],del,_,U) <=> true | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, Y],add,M1,_) \ fact(['obo:RO_0002131', X, Y],del,_,U) <=> true | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002205', Y, X],add,M1,_) \ fact(['obo:RO_0002204', X, Y],del,_,U) <=> true | fact(['obo:RO_0002204', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002204', Y, X],add,M1,_) \ fact(['obo:RO_0002205', X, Y],del,_,U) <=> true | fact(['obo:RO_0002205', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002409', X, Y],add,M1,_) \ fact(['obo:RO_0002212', X, Y],del,_,U) <=> true | fact(['obo:RO_0002212', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004010', _, X1],add,M1,_) \ fact(['obo:BFO_0000017', X1],del,_,U) <=> true | fact(['obo:BFO_0000017', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002322', _, X1],add,M1,_) \ fact(['obo:ENVO_01000254', X1],del,_,U) <=> true | fact(['obo:ENVO_01000254', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002378', X, Y],add,M1,_) \ fact(['obo:RO_0002376', Y, X],del,_,U) <=> true | fact(['obo:RO_0002376', Y, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002482', X, Y],add,M1,_) \ fact(['obo:RO_0002564', X, Y],del,_,U) <=> true | fact(['obo:RO_0002564', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002625', X, Y],add,M1,_) \ fact(['obo:RO_0002445', X, Y],del,_,U) <=> true | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000059', X0, X1],add,M1,_), fact(['obo:RO_0000053', X1, X2],add,M2,_) \ fact(['obo:RO_0010002', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0010002', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002497', X0, X1],add,M1,_), fact(['obo:BFO_0000063', X1, X2],add,M2,_) \ fact(['obo:RO_0002497', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004015', Y, X],add,M1,_) \ fact(['obo:RO_0004005', X, Y],del,_,U) <=> true | fact(['obo:RO_0004005', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004005', Y, X],add,M1,_) \ fact(['obo:RO_0004015', X, Y],del,_,U) <=> true | fact(['obo:RO_0004015', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002491', X, Y],add,M1,_) \ fact(['obo:RO_0002488', X, Y],del,_,U) <=> true | fact(['obo:RO_0002488', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002466', X, Y],add,M1,_) \ fact(['obo:RO_0002465', X, Y],del,_,U) <=> true | fact(['obo:RO_0002465', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002244', X, _],add,M1,_) \ fact(['obo:RO_0002310', X],del,_,U) <=> true | fact(['obo:RO_0002310', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0003001', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002224', X0, X1],add,M1,_), fact(['obo:BFO_0000066', X1, X2],add,M2,_) \ fact(['obo:RO_0002231', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002231', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004016', Y, X],add,M1,_) \ fact(['obo:RO_0004006', X, Y],del,_,U) <=> true | fact(['obo:RO_0004006', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004006', Y, X],add,M1,_) \ fact(['obo:RO_0004016', X, Y],del,_,U) <=> true | fact(['obo:RO_0004016', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0010001', X, _],add,M1,_) \ fact(['obo:BFO_0000031', X],del,_,U) <=> true | fact(['obo:BFO_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002531', X, Y],add,M1,_) \ fact(['obo:RO_0002528', X, Y],del,_,U) <=> true | fact(['obo:RO_0002528', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:RO_0002215', X1, X2],add,M2,_) \ fact(['obo:RO_0002329', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002329', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002010', X, Y],add,M1,_) \ fact(['obo:RO_0002418', X, Y],del,_,U) <=> true | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004000', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002216', X, Y],add,M1,_) \ fact(['obo:RO_0002328', X, Y],del,_,U) <=> true | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002523', X, Y],add,M1,_) \ fact(['obo:RO_0002514', X, Y],del,_,U) <=> true | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0008505', X, _],add,M1,_) \ fact(['obo:CARO_0001010', X],del,_,U) <=> true | fact(['obo:CARO_0001010', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002236', X, Y],add,M1,_) \ fact(['obo:RO_0002444', X, Y],del,_,U) <=> true | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011004', X, Y],add,M1,_) \ fact(['obo:RO_0011002', X, Y],del,_,U) <=> true | fact(['obo:RO_0011002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002409', X, Y],add,M1,_), fact(['obo:RO_0002409', Y, Z],add,M2,_) \ fact(['obo:RO_0002409', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002409', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004014', Y, X],add,M1,_) \ fact(['obo:RO_0004004', X, Y],del,_,U) <=> true | fact(['obo:RO_0004004', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004004', Y, X],add,M1,_) \ fact(['obo:RO_0004014', X, Y],del,_,U) <=> true | fact(['obo:RO_0004014', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002203', Y, X],add,M1,_) \ fact(['obo:RO_0002202', X, Y],del,_,U) <=> true | fact(['obo:RO_0002202', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002202', Y, X],add,M1,_) \ fact(['obo:RO_0002203', X, Y],del,_,U) <=> true | fact(['obo:RO_0002203', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002325', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002243', X, Y],add,M1,_) \ fact(['obo:RO_0002244', X, Y],del,_,U) <=> true | fact(['obo:RO_0002244', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002026', X, Y],add,M1,_) \ fact(['obo:RO_0002323', X, Y],del,_,U) <=> true | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001022', X, Y],add,M1,_) \ fact(['obo:RO_0003302', X, Y],del,_,U) <=> true | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004026', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002528', X, Y],add,M1,_) \ fact(['obo:RO_0002527', X, Y],del,_,U) <=> true | fact(['obo:RO_0002527', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002012', _, X1],add,M1,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004025', X, _],add,M1,_) \ fact(['obo:OGMS_0000031', X],del,_,U) <=> true | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002019', X, _],add,M1,_) \ fact(['obo:GO_0004872', X],del,_,U) <=> true | fact(['obo:GO_0004872', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002497', X, Y],add,M1,_) \ fact(['obo:RO_0002487', X, Y],del,_,U) <=> true | fact(['obo:RO_0002487', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009501', X, Y],add,M1,_) \ fact(['obo:RO_0002410', X, Y],del,_,U) <=> true | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011004', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0009004', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011013', _, X1],add,M1,_) \ fact(['obo:BFO_0000040', X1],del,_,U) <=> true | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002331', X0, X1],add,M1,_), fact(['obo:RO_0002213', X1, X2],add,M2,_) \ fact(['obo:RO_0002429', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002429', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002407', X, Y],add,M1,_), fact(['obo:RO_0002407', Y, Z],add,M2,_) \ fact(['obo:RO_0002407', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002291', X, Y],add,M1,_) \ fact(['obo:RO_0002206', X, Y],del,_,U) <=> true | fact(['obo:RO_0002206', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002514', _, X1],add,M1,_) \ fact(['obo:RO_0002532', X1],del,_,U) <=> true | fact(['obo:RO_0002532', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002623', X, Y],add,M1,_) \ fact(['obo:RO_0002619', X, Y],del,_,U) <=> true | fact(['obo:RO_0002619', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004012', Y, X],add,M1,_) \ fact(['obo:RO_0004002', X, Y],del,_,U) <=> true | fact(['obo:RO_0004002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004002', Y, X],add,M1,_) \ fact(['obo:RO_0004012', X, Y],del,_,U) <=> true | fact(['obo:RO_0004012', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002111', X, _],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002334', X, Y],add,M1,_) \ fact(['obo:RO_0002427', X, Y],del,_,U) <=> true | fact(['obo:RO_0002427', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002131', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:RO_0002131', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002131', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002202', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002206', _, X1],add,M1,_) \ fact(['obo:CARO_0000006', X1],del,_,U) <=> true | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004013', Y, X],add,M1,_) \ fact(['obo:RO_0004003', X, Y],del,_,U) <=> true | fact(['obo:RO_0004003', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0004003', Y, X],add,M1,_) \ fact(['obo:RO_0004013', X, Y],del,_,U) <=> true | fact(['obo:RO_0004013', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002519', X, Y],add,M1,_) \ fact(['obo:RO_0002525', X, Y],del,_,U) <=> true | fact(['obo:RO_0002525', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0011013', X, Y],add,M1,_) \ fact(['obo:RO_0011004', X, Y],del,_,U) <=> true | fact(['obo:RO_0011004', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002258', X0, X1],add,M1,_), fact(['obo:RO_0002496', X1, X2],add,M2,_) \ fact(['obo:RO_0002496', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002179', X, Y],add,M1,_) \ fact(['obo:RO_0002170', X, Y],del,_,U) <=> true | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002221', X, Y],add,M1,_) \ fact(['obo:RO_0002220', X, Y],del,_,U) <=> true | fact(['obo:RO_0002220', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0003824', X],add,M1,_) \ fact(['obo:GO_0003674', X],del,_,U) <=> true | fact(['obo:GO_0003674', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0016874', X],add,M1,_) \ fact(['obo:GO_0003824', X],del,_,U) <=> true | fact(['obo:GO_0003824', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0016740', X],add,M1,_) \ fact(['obo:GO_0003824', X],del,_,U) <=> true | fact(['obo:GO_0003824', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0019787', X],add,M1,_) \ fact(['obo:GO_0016881', X],del,_,U) <=> true | fact(['obo:GO_0016881', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0004842', X],add,M1,_) \ fact(['obo:GO_0019787', X],del,_,U) <=> true | fact(['obo:GO_0019787', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0016301', X],add,M1,_) \ fact(['obo:GO_0016772', X],del,_,U) <=> true | fact(['obo:GO_0016772', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0016879', X],add,M1,_) \ fact(['obo:GO_0016874', X],del,_,U) <=> true | fact(['obo:GO_0016874', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0016772', X],add,M1,_) \ fact(['obo:GO_0016740', X],del,_,U) <=> true | fact(['obo:GO_0016740', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0016881', X],add,M1,_) \ fact(['obo:GO_0016879', X],del,_,U) <=> true | fact(['obo:GO_0016879', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000053', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000053', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000053', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000073', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000022', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000022', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000004', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000002', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000046', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000046', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000046', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000026', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000034', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000034', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000060', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000060', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000060', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000007', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000001', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000024', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000018', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000047', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000052', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000052', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000052', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000061', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000018', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000074', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000066', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000066', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000033', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000004', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000004', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000051', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000051', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000029', X, Y],add,M1,_), fact(['obo:RO_HOM0000030', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000045', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000045', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000045', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000037', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000037', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000037', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000029', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000028', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000028', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000057', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000058', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000058', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000044', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000044', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000044', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000036', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000036', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000074', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000003', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000003', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000050', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000050', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000043', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000043', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000043', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000042', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000042', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000042', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000029', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000029', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000029', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000046', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000047', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000047', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000036', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000028', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000028', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000028', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000027', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000027', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000027', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000062', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000013', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000010', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000032', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000029', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000029', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000034', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000034', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000034', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000073', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000073', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000073', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000023', X, Y],add,M1,_), fact(['obo:RO_HOM0000024', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000027', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000066', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000066', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000071', X, Y],add,M1,_), fact(['obo:RO_HOM0000072', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000066', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000066', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000066', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000012', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000010', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000062', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000065', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000065', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000031', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000029', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000029', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000044', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000003', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000003', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000058', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000058', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000058', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000072', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000072', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000072', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000052', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000030', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000030', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000065', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000065', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000065', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000057', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000071', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000071', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000071', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000034', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000037', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000037', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000063', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000063', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000063', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000044', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000005', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000005', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000049', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000049', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000049', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000020', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000062', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000062', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000062', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000060', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000050', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000012', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000054', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000062', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000062', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000048', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000048', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000048', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000065', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000050', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000055', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000055', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000055', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000020', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000019', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000019', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000047', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000047', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000047', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000061', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000061', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000061', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000015', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000054', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000054', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000054', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000001', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000063', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000054', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000006', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000005', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000005', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000005', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000011', X, Y],add,M1,_), fact(['obo:RO_HOM0000017', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000012', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000012', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000012', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000004', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000004', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000004', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000066', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000008', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000008', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000011', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000003', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000003', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000003', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000037', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000049', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000010', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000010', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000010', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000048', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000036', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000036', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000002', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000002', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000043', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000055', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000006', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000001', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000075', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000034', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000023', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000017', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000049', X, Y],add,M1,_), fact(['obo:RO_HOM0000050', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000069', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000069', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000069', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000003', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000014', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000011', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000058', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000003', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000003', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000075', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000075', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000075', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000009', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000002', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000068', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000068', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000068', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000001', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000001', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000051', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000029', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000029', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000060', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000019', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000019', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000025', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000034', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000034', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000074', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000074', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000074', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000072', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000008', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000008', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000000', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000026', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000026', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000026', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000002', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000000', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000071', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000016', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000033', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000033', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000033', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000053', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000018', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000025', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000025', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000025', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000010', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000006', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000019', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000019', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000019', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000032', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000032', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000032', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000031', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000031', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000031', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000019', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000008', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000001', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000024', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000024', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000024', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000018', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000018', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000042', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000030', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000030', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000030', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000022', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000017', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000045', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000016', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000016', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000016', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000016', X, Y],add,M1,_), fact(['obo:RO_HOM0000062', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000009', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000009', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000009', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000023', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000023', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000023', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000001', X, Y],add,M1,_), fact(['obo:RO_HOM0000002', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000015', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000015', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000015', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000057', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000005', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000005', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000005', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000002', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000042', X, Y],add,M1,_), fact(['obo:RO_HOM0000043', X, Y],add,M2,_) \ fact(['owl:Nothing', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000022', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000022', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000022', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000068', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000018', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000018', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000030', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000028', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000028', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000014', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000014', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000014', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000008', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000008', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000008', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000069', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000011', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000028', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000008', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000008', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000020', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000020', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000020', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000013', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000013', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000013', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000007', Y, X],add,M1,_) \ fact(['obo:RO_HOM0000007', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000048', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000017', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000073', X, Y],add,M1,_) \ fact(['obo:RO_HOM0000053', X, Y],del,_,U) <=> true | fact(['obo:RO_HOM0000053', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002090', Y, X],add,M1,_) \ fact(['obo:RO_0002087', X, Y],del,_,U) <=> true | fact(['obo:RO_0002087', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002087', Y, X],add,M1,_) \ fact(['obo:RO_0002090', X, Y],del,_,U) <=> true | fact(['obo:RO_0002090', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002093', Y, X],add,M1,_) \ fact(['obo:RO_0002084', X, Y],del,_,U) <=> true | fact(['obo:RO_0002084', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002084', Y, X],add,M1,_) \ fact(['obo:RO_0002093', X, Y],del,_,U) <=> true | fact(['obo:RO_0002093', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002087', X, Y],add,M1,_) \ fact(['obo:BFO_0000062', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000062', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002084', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002081', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000062', X, Y],add,M1,_), fact(['obo:BFO_0000062', Y, Z],add,M2,_) \ fact(['obo:BFO_0000062', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000062', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000063', _, X1],add,M1,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000063', Y, X],add,M1,_) \ fact(['obo:BFO_0000062', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000062', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000062', Y, X],add,M1,_) \ fact(['obo:BFO_0000063', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000063', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', Y, X],add,M1,_) \ fact(['obo:RO_0002229', X, Y],del,_,U) <=> true | fact(['obo:RO_0002229', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002229', Y, X],add,M1,_) \ fact(['obo:RO_0002230', X, Y],del,_,U) <=> true | fact(['obo:RO_0002230', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002092', X0, X1],add,M1,_), fact(['obo:BFO_0000062', X1, X2],add,M2,_) \ fact(['obo:BFO_0000062', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000062', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002091', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002083', X, Y],add,M1,_), fact(['obo:RO_0002083', Y, Z],add,M2,_) \ fact(['obo:RO_0002083', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002083', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002230', X, Y],add,M1,_), fact(['obo:RO_0002230', Y, Z],add,M2,_) \ fact(['obo:RO_0002230', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002230', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002091', X0, X1],add,M1,_), fact(['obo:BFO_0000062', X1, X2],add,M2,_) \ fact(['obo:BFO_0000062', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000062', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002091', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002089', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002224', X, Y],add,M1,_), fact(['obo:RO_0002224', Y, Z],add,M2,_) \ fact(['obo:RO_0002224', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002224', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002086', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002082', X, Y],add,M1,_), fact(['obo:RO_0002082', Y, Z],add,M2,_) \ fact(['obo:RO_0002082', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002082', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002222', _, X1],add,M1,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002092', X, Y],add,M1,_) \ fact(['obo:RO_0002093', X, Y],del,_,U) <=> true | fact(['obo:RO_0002093', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002089', X, Y],add,M1,_), fact(['obo:RO_0002089', Y, Z],add,M2,_) \ fact(['obo:RO_0002089', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002089', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000063', X, Y],add,M1,_), fact(['obo:BFO_0000063', Y, Z],add,M2,_) \ fact(['obo:BFO_0000063', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000063', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000062', _, X1],add,M1,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002093', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002093', X0, X1],add,M1,_), fact(['obo:BFO_0000062', X1, X2],add,M2,_) \ fact(['obo:RO_0002086', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002086', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002224', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002088', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002090', X, Y],add,M1,_) \ fact(['obo:BFO_0000063', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000063', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000063', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000062', X, Y],add,M1,_) \ fact(['obo:RO_0002086', X, Y],del,_,U) <=> true | fact(['obo:RO_0002086', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002091', _, X1],add,M1,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002083', X, Y],add,M1,_) \ fact(['obo:RO_0002081', X, Y],del,_,U) <=> true | fact(['obo:RO_0002081', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002229', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002091', X0, X1],add,M1,_), fact(['obo:BFO_0000060', X1, X2],add,M2,_) \ fact(['obo:RO_0002089', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002089', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000060', X, Y],add,M1,_), fact(['obo:BFO_0000060', Y, Z],add,M2,_) \ fact(['obo:BFO_0000060', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000060', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002223', X, Y],add,M1,_) \ fact(['obo:RO_0002222', X, Y],del,_,U) <=> true | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002224', Y, X],add,M1,_) \ fact(['obo:RO_0002223', X, Y],del,_,U) <=> true | fact(['obo:RO_0002223', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002223', Y, X],add,M1,_) \ fact(['obo:RO_0002224', X, Y],del,_,U) <=> true | fact(['obo:RO_0002224', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002082', X, Y],add,M1,_) \ fact(['obo:RO_0002081', X, Y],del,_,U) <=> true | fact(['obo:RO_0002081', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000062', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002092', X, Y],add,M1,_), fact(['obo:RO_0002092', Y, Z],add,M2,_) \ fact(['obo:RO_0002092', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002092', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002222', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002091', Y, X],add,M1,_) \ fact(['obo:RO_0002088', X, Y],del,_,U) <=> true | fact(['obo:RO_0002088', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002088', Y, X],add,M1,_) \ fact(['obo:RO_0002091', X, Y],del,_,U) <=> true | fact(['obo:RO_0002091', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002086', X, Y],add,M1,_), fact(['obo:RO_0002086', Y, Z],add,M2,_) \ fact(['obo:RO_0002086', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0002086', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', X, Y],add,M1,_), fact(['obo:RO_0001025', Y, Z],add,M2,_) \ fact(['obo:RO_0001025', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0001025', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000057', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000086', X, Y],add,M1,_) \ fact(['obo:RO_0000053', X, Y],del,_,U) <=> true | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000067', Y, X],add,M1,_) \ fact(['obo:BFO_0000066', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000066', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000066', Y, X],add,M1,_) \ fact(['obo:BFO_0000067', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000067', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000055', _, X1],add,M1,_) \ fact(['obo:BFO_0000017', X1],del,_,U) <=> true | fact(['obo:BFO_0000017', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000079', X, _],add,M1,_) \ fact(['obo:BFO_0000034', X],del,_,U) <=> true | fact(['obo:BFO_0000034', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000079', X, Y],add,M1,_) \ fact(['obo:RO_0000052', X, Y],del,_,U) <=> true | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000087', _, X1],add,M1,_) \ fact(['obo:BFO_0000023', X1],del,_,U) <=> true | fact(['obo:BFO_0000023', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000080', X, Y],add,M1,_) \ fact(['obo:RO_0000052', X, Y],del,_,U) <=> true | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, Y],add,M1,_), fact(['obo:BFO_0000050', Y, Z],add,M2,_) \ fact(['obo:BFO_0000050', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X0, X1],add,M1,_), fact(['obo:BFO_0000066', X1, X2],add,M2,_) \ fact(['obo:BFO_0000066', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000066', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000085', _, X1],add,M1,_) \ fact(['obo:BFO_0000034', X1],del,_,U) <=> true | fact(['obo:BFO_0000034', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000002', X],add,M1,_), fact(['obo:BFO_0000050', X, X1],add,M2,_), fact(['obo:BFO_0000003', X1],add,M3,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000003', X],add,M1,_), fact(['obo:BFO_0000050', X, X1],add,M2,_), fact(['obo:BFO_0000002', X1],add,M3,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000055', Y, X],add,M1,_) \ fact(['obo:BFO_0000054', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000054', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000054', Y, X],add,M1,_) \ fact(['obo:BFO_0000055', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000055', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000056', X, _],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000066', X, _],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000058', X, _],add,M1,_) \ fact(['obo:BFO_0000031', X],del,_,U) <=> true | fact(['obo:BFO_0000031', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002350', X, Y],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', Y, X],add,M1,_) \ fact(['obo:RO_0001015', X, Y],del,_,U) <=> true | fact(['obo:RO_0001015', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001015', Y, X],add,M1,_) \ fact(['obo:RO_0001025', X, Y],del,_,U) <=> true | fact(['obo:RO_0001025', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001015', X, Y],add,M1,_), fact(['obo:RO_0001015', Y, Z],add,M2,_) \ fact(['obo:RO_0001015', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:RO_0001015', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000086', Y, X],add,M1,_) \ fact(['obo:RO_0000080', X, Y],del,_,U) <=> true | fact(['obo:RO_0000080', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000080', Y, X],add,M1,_) \ fact(['obo:RO_0000086', X, Y],del,_,U) <=> true | fact(['obo:RO_0000086', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000054', _, X1],add,M1,_) \ fact(['obo:BFO_0000015', X1],del,_,U) <=> true | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000092', X, Y],add,M1,_) \ fact(['obo:RO_0000052', X, Y],del,_,U) <=> true | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000055', X, _],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000056', _, X1],add,M1,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000066', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000057', Y, X],add,M1,_) \ fact(['obo:RO_0000056', X, Y],del,_,U) <=> true | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000056', Y, X],add,M1,_) \ fact(['obo:RO_0000057', X, Y],del,_,U) <=> true | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002351', X, X],add,M1,_) \ fact(['owl:Nothing', X, X],del,_,U) <=> true | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002351', X, Y],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000087', Y, X],add,M1,_) \ fact(['obo:RO_0000081', X, Y],del,_,U) <=> true | fact(['obo:RO_0000081', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000081', Y, X],add,M1,_) \ fact(['obo:RO_0000087', X, Y],del,_,U) <=> true | fact(['obo:RO_0000087', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002002', X, _],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002002', Y, X],add,M1,_) \ fact(['obo:RO_0002000', X, Y],del,_,U) <=> true | fact(['obo:RO_0002000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002000', Y, X],add,M1,_) \ fact(['obo:RO_0002002', X, Y],del,_,U) <=> true | fact(['obo:RO_0002002', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002351', Y, X],add,M1,_) \ fact(['obo:RO_0002350', X, Y],del,_,U) <=> true | fact(['obo:RO_0002350', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002350', Y, X],add,M1,_) \ fact(['obo:RO_0002351', X, Y],del,_,U) <=> true | fact(['obo:RO_0002351', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000091', X, Y],add,M1,_) \ fact(['obo:RO_0000053', X, Y],del,_,U) <=> true | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000081', X, Y],add,M1,_) \ fact(['obo:RO_0000052', X, Y],del,_,U) <=> true | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000085', X, Y],add,M1,_) \ fact(['obo:RO_0000053', X, Y],del,_,U) <=> true | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000092', Y, X],add,M1,_) \ fact(['obo:RO_0000091', X, Y],del,_,U) <=> true | fact(['obo:RO_0000091', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000091', Y, X],add,M1,_) \ fact(['obo:RO_0000092', X, Y],del,_,U) <=> true | fact(['obo:RO_0000092', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000085', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000086', _, X1],add,M1,_) \ fact(['obo:BFO_0000019', X1],del,_,U) <=> true | fact(['obo:BFO_0000019', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000006', X],add,M1,_), fact(['obo:RO_0001025', X, X1],add,M2,_) \ fact(['owl:Nothing', X, X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000053', _, X1],add,M1,_) \ fact(['obo:BFO_0000020', X1],del,_,U) <=> true | fact(['obo:BFO_0000020', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000085', Y, X],add,M1,_) \ fact(['obo:RO_0000079', X, Y],del,_,U) <=> true | fact(['obo:RO_0000079', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000079', Y, X],add,M1,_) \ fact(['obo:RO_0000085', X, Y],del,_,U) <=> true | fact(['obo:RO_0000085', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000066', X0, X1],add,M1,_), fact(['obo:BFO_0000050', X1, X2],add,M2,_) \ fact(['obo:BFO_0000066', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000066', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000059', Y, X],add,M1,_) \ fact(['obo:RO_0000058', X, Y],del,_,U) <=> true | fact(['obo:RO_0000058', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000058', Y, X],add,M1,_) \ fact(['obo:RO_0000059', X, Y],del,_,U) <=> true | fact(['obo:RO_0000059', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000087', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002002', _, X1],add,M1,_) \ fact(['obo:BFO_0000141', X1],del,_,U) <=> true | fact(['obo:BFO_0000141', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000091', _, X1],add,M1,_) \ fact(['obo:BFO_0000016', X1],del,_,U) <=> true | fact(['obo:BFO_0000016', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', Y, X],add,M1,_) \ fact(['obo:BFO_0000050', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', Y, X],add,M1,_) \ fact(['obo:BFO_0000051', X, Y],del,_,U) <=> true | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000051', X, Y],add,M1,_), fact(['obo:BFO_0000051', Y, Z],add,M2,_) \ fact(['obo:BFO_0000051', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000051', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000059', X, _],add,M1,_) \ fact(['obo:BFO_0000020', X],del,_,U) <=> true | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000053', Y, X],add,M1,_) \ fact(['obo:RO_0000052', X, Y],del,_,U) <=> true | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000052', Y, X],add,M1,_) \ fact(['obo:RO_0000053', X, Y],del,_,U) <=> true | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000057', _, X1],add,M1,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000058', _, X1],add,M1,_) \ fact(['obo:BFO_0000020', X1],del,_,U) <=> true | fact(['obo:BFO_0000020', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000059', _, X1],add,M1,_) \ fact(['obo:BFO_0000031', X1],del,_,U) <=> true | fact(['obo:BFO_0000031', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001001', Y, X],add,M1,_) \ fact(['obo:RO_0001000', X, Y],del,_,U) <=> true | fact(['obo:RO_0001000', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001000', Y, X],add,M1,_) \ fact(['obo:RO_0001001', X, Y],del,_,U) <=> true | fact(['obo:RO_0001001', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000054', X, _],add,M1,_) \ fact(['obo:BFO_0000017', X],del,_,U) <=> true | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0001025', _, X1],add,M1,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000006', X1],add,M1,_), fact(['obo:RO_0001025', X, X1],add,M2,_) \ fact(['owl:Nothing', X, X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000087', X, Y],add,M1,_) \ fact(['obo:RO_0000053', X, Y],del,_,U) <=> true | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0000091', X, _],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0001199', X],add,M1,_) \ fact(['obo:PATO_0000052', X],del,_,U) <=> true | fact(['obo:PATO_0000052', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0000052', X],add,M1,_) \ fact(['obo:PATO_0000051', X],del,_,U) <=> true | fact(['obo:PATO_0000051', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0000051', X],add,M1,_) \ fact(['obo:PATO_0001241', X],del,_,U) <=> true | fact(['obo:PATO_0001241', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0002124', X],add,M1,_) \ fact(['obo:PATO_0000141', X],del,_,U) <=> true | fact(['obo:PATO_0000141', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0001241', X],add,M1,_) \ fact(['obo:PATO_0000001', X],del,_,U) <=> true | fact(['obo:PATO_0000001', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0000141', X],add,M1,_) \ fact(['obo:PATO_0000051', X],del,_,U) <=> true | fact(['obo:PATO_0000051', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0016020', X],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0042734', X],add,M1,_) \ fact(['obo:GO_0044456', X],del,_,U) <=> true | fact(['obo:GO_0044456', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0005634', X],add,M1,_) \ fact(['obo:GO_0044464', X],del,_,U) <=> true | fact(['obo:GO_0044464', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0043005', X],add,M1,_) \ fact(['obo:GO_0042995', X],del,_,U) <=> true | fact(['obo:GO_0042995', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0045211', X],add,M1,_) \ fact(['obo:GO_0044456', X],del,_,U) <=> true | fact(['obo:GO_0044456', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0044456', X],add,M1,_) \ fact(['obo:GO_0044464', X],del,_,U) <=> true | fact(['obo:GO_0044464', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0044464', X],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0042995', X],add,M1,_) \ fact(['obo:GO_0044464', X],del,_,U) <=> true | fact(['obo:GO_0044464', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0045211', X],add,M1,_) \ fact(['obo:GO_0016020', X],del,_,U) <=> true | fact(['obo:GO_0016020', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0030424', X],add,M1,_) \ fact(['obo:GO_0043005', X],del,_,U) <=> true | fact(['obo:GO_0043005', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0042734', X],add,M1,_) \ fact(['obo:GO_0016020', X],del,_,U) <=> true | fact(['obo:GO_0016020', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0008150', X],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0030425', X],add,M1,_) \ fact(['obo:GO_0043005', X],del,_,U) <=> true | fact(['obo:GO_0043005', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0045202', X],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000040', X],add,M1,_), fact(['obo:BFO_0000141', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000017', X],add,M1,_), fact(['obo:BFO_0000019', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000002', X],add,M1,_), fact(['obo:BFO_0000003', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000016', X],add,M1,_), fact(['obo:BFO_0000023', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000004', X],add,M1,_), fact(['obo:BFO_0000020', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000004', X],add,M1,_), fact(['obo:BFO_0000031', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000020', X],add,M1,_), fact(['obo:BFO_0000031', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0000006', X],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CL_0000000', X],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0030000', X],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0000000', X],add,M1,_) \ fact(['obo:CARO_0030000', X],del,_,U) <=> true | fact(['obo:CARO_0030000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0000011', X],add,M1,_) \ fact(['obo:CARO_0010000', X],del,_,U) <=> true | fact(['obo:CARO_0010000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0010000', X],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0001001', X],add,M1,_) \ fact(['obo:CARO_0001000', X],del,_,U) <=> true | fact(['obo:CARO_0001000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0000011', X],add,M1,_) \ fact(['obo:RO_0002577', X],del,_,U) <=> true | fact(['obo:RO_0002577', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0000001', X],add,M1,_) \ fact(['obo:BFO_0000020', X],del,_,U) <=> true | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CL_0000540', X],add,M1,_) \ fact(['obo:CL_0000000', X],del,_,U) <=> true | fact(['obo:CL_0000000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:ENVO_00000428', X],add,M1,_) \ fact(['obo:ENVO_01000254', X],del,_,U) <=> true | fact(['obo:ENVO_01000254', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0002009', X],add,M1,_) \ fact(['obo:PATO_0000052', X],del,_,U) <=> true | fact(['obo:PATO_0000052', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002207', X, X1],add,M1,_), fact(['obo:CL_0000000', X],add,M2,_) \ fact(['obo:CL_0000000', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:CL_0000000', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:ENVO_01000254', X],add,M1,_) \ fact(['obo:RO_0002577', X],del,_,U) <=> true | fact(['obo:RO_0002577', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002207', X, X1],add,M1,_), fact(['obo:CARO_0010000', X],add,M2,_) \ fact(['obo:CARO_0010000', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:CARO_0010000', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:OGMS_0000031', X],add,M1,_) \ fact(['obo:BFO_0000016', X],del,_,U) <=> true | fact(['obo:BFO_0000016', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:UPHENO_0001001', X],add,M1,_) \ fact(['obo:PATO_0000001', X],del,_,U) <=> true | fact(['obo:PATO_0000001', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0001010', X],add,M1,_) \ fact(['obo:BFO_0000040', X],del,_,U) <=> true | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0001000', X],add,M1,_) \ fact(['obo:CARO_0000003', X],del,_,U) <=> true | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0000006', X],add,M1,_) \ fact(['obo:CARO_0000000', X],del,_,U) <=> true | fact(['obo:CARO_0000000', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0000007', X],add,M1,_) \ fact(['obo:BFO_0000141', X],del,_,U) <=> true | fact(['obo:BFO_0000141', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:CARO_0000003', X],add,M1,_) \ fact(['obo:CARO_0000006', X],del,_,U) <=> true | fact(['obo:CARO_0000006', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0000402', X],add,M1,_) \ fact(['obo:PATO_0002009', X],del,_,U) <=> true | fact(['obo:PATO_0002009', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0000052', X],add,M1,_) \ fact(['obo:PATO_0000051', X],del,_,U) <=> true | fact(['obo:PATO_0000051', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:PATO_0000051', X],add,M1,_) \ fact(['obo:BFO_0000019', X],del,_,U) <=> true | fact(['obo:BFO_0000019', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0003674', X],add,M1,_) \ fact(['obo:BFO_0000015', X],del,_,U) <=> true | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002262', X, Y],add,M1,_) \ fact(['obo:RO_0000087', X, Y],del,_,U) <=> true | fact(['obo:RO_0000087', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002260', X, Y],add,M1,_) \ fact(['obo:RO_0000087', X, Y],del,_,U) <=> true | fact(['obo:RO_0000087', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:RO_0002261', X, Y],add,M1,_) \ fact(['obo:RO_0000087', X, Y],del,_,U) <=> true | fact(['obo:RO_0000087', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000019', X],add,M1,_) \ fact(['obo:BFO_0000020', X],del,_,U) <=> true | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000016', X],add,M1,_) \ fact(['obo:BFO_0000017', X],del,_,U) <=> true | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000031', X],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000015', X],add,M1,_) \ fact(['obo:BFO_0000003', X],del,_,U) <=> true | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000020', X],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000004', X],add,M1,_) \ fact(['obo:BFO_0000002', X],del,_,U) <=> true | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000017', X],add,M1,_) \ fact(['obo:BFO_0000020', X],del,_,U) <=> true | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000141', X],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000040', X],add,M1,_) \ fact(['obo:BFO_0000004', X],del,_,U) <=> true | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000005', X],add,M1,_) \ fact(['go:ObsoleteClass', X],del,_,U) <=> true | fact(['go:ObsoleteClass', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000034', X],add,M1,_) \ fact(['obo:BFO_0000016', X],del,_,U) <=> true | fact(['obo:BFO_0000016', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000006', X],add,M1,_) \ fact(['obo:BFO_0000141', X],del,_,U) <=> true | fact(['obo:BFO_0000141', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000023', X],add,M1,_) \ fact(['obo:BFO_0000017', X],del,_,U) <=> true | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0085031', X],add,M1,_) \ fact(['obo:GO_0044403', X],del,_,U) <=> true | fact(['obo:GO_0044403', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0051705', X],add,M1,_) \ fact(['obo:GO_0007610', X],del,_,U) <=> true | fact(['obo:GO_0007610', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0051704', X],add,M1,_) \ fact(['obo:GO_0008150', X],del,_,U) <=> true | fact(['obo:GO_0008150', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0007610', X],add,M1,_) \ fact(['obo:GO_0050896', X],del,_,U) <=> true | fact(['obo:GO_0050896', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0051816', X],add,M1,_) \ fact(['obo:GO_0007631', X],del,_,U) <=> true | fact(['obo:GO_0007631', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0044403', X],add,M1,_) \ fact(['obo:GO_0044419', X],del,_,U) <=> true | fact(['obo:GO_0044419', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0044419', X],add,M1,_) \ fact(['obo:GO_0051704', X],del,_,U) <=> true | fact(['obo:GO_0051704', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0072519', X],add,M1,_) \ fact(['obo:GO_0044403', X],del,_,U) <=> true | fact(['obo:GO_0044403', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0007631', X],add,M1,_) \ fact(['obo:GO_0007610', X],del,_,U) <=> true | fact(['obo:GO_0007610', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0050896', X],add,M1,_) \ fact(['obo:GO_0008150', X],del,_,U) <=> true | fact(['obo:GO_0008150', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0051702', X],add,M1,_) \ fact(['obo:GO_0044419', X],del,_,U) <=> true | fact(['obo:GO_0044419', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0085030', X],add,M1,_) \ fact(['obo:GO_0044403', X],del,_,U) <=> true | fact(['obo:GO_0044403', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0051850', X],add,M1,_) \ fact(['obo:GO_0051702', X],del,_,U) <=> true | fact(['obo:GO_0051702', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0051705', X],add,M1,_) \ fact(['obo:GO_0051704', X],del,_,U) <=> true | fact(['obo:GO_0051704', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0051850', X],add,M1,_) \ fact(['obo:GO_0051816', X],del,_,U) <=> true | fact(['obo:GO_0051816', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:GO_0051850', X],add,M1,_) \ fact(['obo:GO_0051705', X],del,_,U) <=> true | fact(['obo:GO_0051705', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, X1],add,M1,_), fact(['obo:BFO_0000020', X],add,M2,_) \ fact(['obo:BFO_0000020', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000020', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, X1],add,M1,_), fact(['obo:BFO_0000031', X],add,M2,_) \ fact(['obo:BFO_0000031', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000031', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000000', X, X1],add,M1,_), fact(['obo:BFO_0000002', X],add,M2,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000002', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, X1],add,M1,_), fact(['obo:BFO_0000003', X],add,M2,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000003', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, X1],add,M1,_), fact(['obo:BFO_0000002', X],add,M2,_) \ fact(['obo:BFO_0000002', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000002', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:RO_HOM0000000', X, X1],add,M1,_), fact(['obo:BFO_0000003', X],add,M2,_) \ fact(['obo:BFO_0000003', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000003', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, X1],add,M1,_), fact(['obo:BFO_0000004', X],add,M2,_) \ fact(['obo:BFO_0000004', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000004', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, X1],add,M1,_), fact(['obo:BFO_0000017', X],add,M2,_) \ fact(['obo:BFO_0000017', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000017', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000050', X, X1],add,M1,_), fact(['obo:BFO_0000019', X],add,M2,_) \ fact(['obo:BFO_0000019', X1],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000019', X1],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000141', X],add,M1,_), fact(['obo:BFO_0000051', X, X1],add,M2,_), fact(['obo:BFO_0000040', X1],add,M3,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['obo:BFO_0000040', X],add,M1,_), fact(['obo:BFO_0000050', X, X1],add,M2,_), fact(['obo:BFO_0000141', X1],add,M3,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).

phase(2) <=> phase(3).


% -- keep marked del-facts for next update --
phase(3), num_updates(N) \ fact(F,del,1,_) <=> 
	pending_fact(F,add,N),
	marked_facts(1,del,F).

% -- remove (unmarked) facts that cannot be rederived --
phase(3) \ fact(_,del,_,_) <=> true.

% note: update-constraint ensures that we first process update before moving to insertion phase
phase(3), update(add,[],_) <=> phase(4).


%-------------------------------------------------
% -- insertions --

% insert every new fact
phase(4), current_update(U) \ pending_fact(F,add,U) <=> fact(F,add,_,U).
phase(4) <=> phase(5), finish_update.
	
% -- compute new derivable facts	--
phase(5), fact(['obo:RO_0003000', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002490', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002487', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001020', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002178', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002203', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002372', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X0, X1],add,M1,U1), fact(['obo:RO_0002234', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002234', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002506', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002496', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002487', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002353', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002256', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002443', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002522', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009501', X0, X1],add,M1,U1), fact(['obo:RO_0002233', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004028', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002248', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002295', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011013', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002242', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002244', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002595', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002448', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002235', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002212', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002020', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002313', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X0, X1],add,M1,U1), fact(['obo:RO_0002212', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002212', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002110', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002130', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002134', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001001', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002009', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002017', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002101', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002104', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002179', X, X1],add,M1,U1), fact(['obo:CARO_0000006', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:CARO_0000003', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002233', X, X2],add,M1,U1), fact(['obo:RO_0002025', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002233', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002459', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002004', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002326', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002329', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:RO_0002497', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002578', X0, X1],add,M1,U1), fact(['obo:RO_0002578', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002211', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002622', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002618', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002224', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002331', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002331', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002576', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002400', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004000', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002518', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002524', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002206', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X0, X1],add,M1,U1), fact(['obo:RO_0002224', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002090', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003301', X, Y],add,M1,U1), fact(['obo:RO_0003301', Y, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002015', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002336', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002134', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002134', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000052', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002314', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009003', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002427', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002418', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002427', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002225', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002461', X0, X1],add,M1,U1), fact(['obo:RO_0002466', X1, X2],add,M2,U2), fact(['obo:RO_0002461', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002441', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002641', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002640', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002640', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002641', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002211', X, Y],add,M1,U1), fact(['obo:RO_0002211', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002211', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002163', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009501', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002495', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002494', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003304', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002380', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002332', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002506', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002213', X, Y],add,M1,U1), fact(['obo:RO_0002213', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002213', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002355', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002413', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002414', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004003', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002334', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002211', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002159', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002159', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0085030', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002467', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002156', X0, X1],add,M1,U1), fact(['obo:RO_0002157', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002158', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002303', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011015', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003002', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002432', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002569', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002212', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002430', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002496', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002496', X, Y],add,M1,U1), fact(['obo:RO_NonExist', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002131', X, Y],add,M1,U1), fact(['obo:RO_NonExist', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002162', X, Y],add,M1,U1), fact(['obo:RO_NonExist', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002315', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002382', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002377', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002507', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002559', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0001025', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002314', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002314', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002224', X0, X1],add,M1,U1), fact(['obo:RO_0002233', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002233', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002336', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002213', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002213', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002336', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002583', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002496', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002371', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002177', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002449', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002448', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002567', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004009', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002092', X0, X1],add,M1,U1), fact(['obo:BFO_0000063', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000063', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002460', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002459', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002459', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002460', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002158', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002158', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002606', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002599', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002335', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002212', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002212', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002335', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002201', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:topObjectProperty', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002292', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002574', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002593', X0, X1],add,M1,U1), fact(['obo:BFO_0000063', X1, X2],add,M2,U2), fact(['obo:RO_0002593', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002497', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002413', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002412', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002404', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000062', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002590', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002592', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002100', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002100', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002214', X, X1],add,M1,U1), fact(['obo:BFO_0000015', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000015', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002600', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002598', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002481', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002564', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008501', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001019', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001018', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001019', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002007', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002525', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002309', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002244', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002313', X0, X1],add,M1,U1), fact(['obo:BFO_0000051', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002313', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002348', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000000', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004009', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002479', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002449', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X0, X1],add,M1,U1), fact(['obo:BFO_0000055', X1, X2],add,M2,U2), fact(['obo:RO_0000052', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0000057', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002373', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002371', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002531', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002515', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002495', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002207', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002387', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002384', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002587', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002297', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002286', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002258', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002633', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002435', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002434', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002100', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002586', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002593', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002492', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004023', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040035', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011024', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011022', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002408', X0, X1],add,M1,U1), fact(['obo:RO_0002408', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002409', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002371', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004029', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040035', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002434', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002206', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002206', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002418', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002264', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004020', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004019', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002501', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002334', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002624', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002530', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002529', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:BFO_0000066', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002432', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002202', X, Y],add,M1,U1), fact(['obo:RO_0002202', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002202', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008508', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0008507', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008507', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0008508', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002214', X, X1],add,M1,U1), fact(['obo:BFO_0000002', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000002', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002606', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002302', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002302', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002606', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002437', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002426', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002424', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002203', X, Y],add,M1,U1), fact(['obo:RO_0002203', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002203', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002107', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002412', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002578', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002414', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002132', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002101', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002101', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002132', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002371', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002371', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002551', X, Y],add,M1,U1), fact(['obo:RO_0002551', Y, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002530', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002515', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002427', X, Y],add,M1,U1), fact(['obo:RO_0002427', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002427', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002411', X1, X2],add,M2,U2), fact(['obo:RO_0002233', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002566', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004021', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004019', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002576', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002551', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002551', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002576', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003001', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003000', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008506', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0008506', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009002', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002527', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002527', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002407', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002213', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002511', X0, X1],add,M1,U1), fact(['obo:RO_0002513', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002205', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002632', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002372', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002371', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002386', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002384', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0085031', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002466', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002526', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002526', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000000', X, X1],add,M1,U1), fact(['obo:BFO_0000002', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000002', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004025', X0, X1],add,M1,U1), fact(['obo:RO_0002215', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004024', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002104', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000006', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002301', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002552', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002494', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002202', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002521', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002527', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004030', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004019', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002100', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011014', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002405', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002087', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002016', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002010', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002411', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002263', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004026', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X0, X1],add,M1,U1), fact(['obo:RO_0000057', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0000057', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002330', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002566', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008506', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002200', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:topObjectProperty', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002567', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002478', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002476', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002025', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002576', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002352', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002442', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002009', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002292', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002245', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002206', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002333', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002109', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002524', X0, X1],add,M1,U1), fact(['obo:RO_0002525', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002526', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002553', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002454', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002470', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002252', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0016301', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002481', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002232', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002479', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004024', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004024', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008502', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0008501', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008501', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0008502', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X0, X1],add,M1,U1), fact(['obo:RO_0002213', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002598', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002342', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002344', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002231', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002211', X0, X1],add,M1,U1), fact(['obo:RO_0002313', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002011', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002205', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002208', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003309', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003305', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002203', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002255', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004034', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002263', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008504', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0008503', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008503', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0008504', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002112', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002378', X, Y],add,M1,U1), fact(['obo:RO_0002382', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002590', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002586', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002445', X0, X1],add,M1,U1), fact(['obo:RO_0002445', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002554', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002378', X, Y],add,M1,U1), fact(['obo:RO_0002383', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002456', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002455', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002455', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002456', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004034', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004032', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002551', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002102', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002113', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002431', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002573', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002521', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002521', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002339', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002344', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002584', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003303', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002558', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002616', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002505', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002458', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004012', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002494', X, Y],add,M1,U1), fact(['obo:RO_0002494', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002494', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002205', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002608', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X0, X1],add,M1,U1), fact(['obo:RO_0002481', X1, X2],add,M2,U2), fact(['obo:RO_0002400', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002447', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002487', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003001', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002378', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002377', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002257', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002386', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002151', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004007', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002381', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004004', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000003', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002213', X2, X],add,M1,U1), fact(['obo:RO_0002212', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002212', X2, X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002212', X, X1],add,M1,U1), fact(['obo:RO_0002213', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002212', X, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002085', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002088', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002555', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002157', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002156', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002156', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002157', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011004', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002457', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002120', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002103', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002629', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002213', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0010001', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002293', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002292', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002524', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002487', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002497', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002017', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002327', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002635', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002634', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002634', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002635', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000052', X0, X1],add,M1,U1), fact(['obo:RO_0000058', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0010001', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002157', X, Y],add,M1,U1), fact(['obo:RO_0002157', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002157', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002331', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002431', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004035', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004033', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002202', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004030', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002156', X, Y],add,M1,U1), fact(['obo:RO_0002156', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002156', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001023', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002380', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002299', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002523', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002522', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002522', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002523', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002506', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003000', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002551', X, X],add,M1,U1) ==> member(U,[U1]) | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002108', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002231', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002479', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004005', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004027', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002448', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004013', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002338', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002344', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002411', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X2, X],add,M1,U1), fact(['obo:BFO_0000051', X, X1],add,M2,U2), fact(['obo:GO_0003674', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002327', X2, X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002572', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002571', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002637', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002636', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002636', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002637', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002132', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002425', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002424', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002473', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009003', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002214', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002377', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002583', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002488', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002450', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002448', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011014', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002295', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0008150', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002574', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004027', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004026', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002310', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002211', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002439', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002110', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002110', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002512', X0, X1],add,M1,U1), fact(['obo:RO_0002510', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002204', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002448', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002436', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004021', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002509', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002385', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002384', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002461', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:BFO_0000051', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004031', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002585', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002158', X, Y],add,M1,U1), fact(['obo:RO_0002158', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002158', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002633', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002632', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002632', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002633', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002402', X0, X1],add,M1,U1), fact(['obo:RO_0002400', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002413', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004019', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002592', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002159', X, Y],add,M1,U1), fact(['obo:RO_0002159', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002159', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002571', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002637', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002384', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000000', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011003', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002566', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002524', X, Y],add,M1,U1), fact(['obo:RO_0002524', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002524', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002629', X, X2],add,M1,U1), fact(['obo:RO_0002025', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002629', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0004046', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004033', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002218', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002523', X, Y],add,M1,U1), fact(['obo:RO_0002523', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002523', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004017', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X0, X1],add,M1,U1), fact(['obo:RO_0002213', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002213', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002018', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002492', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002492', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002517', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002525', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002001', X, Y],add,M1,U1), fact(['obo:RO_0002001', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002001', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002212', X0, X1],add,M1,U1), fact(['obo:RO_0002212', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002213', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002520', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002524', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002314', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002502', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002525', X, Y],add,M1,U1), fact(['obo:RO_0002525', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002525', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002583', X0, X1],add,M1,U1), fact(['obo:BFO_0000062', X1, X2],add,M2,U2), fact(['obo:RO_0002583', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002496', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002379', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002177', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002226', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002305', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004046', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X2, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X],add,M2,U2), fact(['obo:GO_0008150', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002331', X2, X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002331', X0, X1],add,M1,U1), fact(['obo:RO_0002211', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002428', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002522', X, Y],add,M1,U1), fact(['obo:RO_0002522', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002522', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011015', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004027', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002529', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002529', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002529', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002529', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002204', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002525', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002524', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002524', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002525', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002639', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002638', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002638', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002639', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002343', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002159', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002315', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002004', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002578', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002022', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002022', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002578', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002295', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002437', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002115', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002114', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002114', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002115', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002596', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0044403', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002465', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011015', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011009', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002461', X0, X1],add,M1,U1), fact(['obo:RO_0002467', X1, X2],add,M2,U2), fact(['obo:RO_0002461', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002442', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002337', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002162', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002000', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002263', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002264', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002528', X, Y],add,M1,U1), fact(['obo:RO_0002528', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002528', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002444', X0, X1],add,M1,U1), fact(['obo:RO_0002444', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002553', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:RO_0002496', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002200', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:UPHENO_0001001', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002564', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002563', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002024', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002022', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002566', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002559', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002559', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002566', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002529', X, Y],add,M1,U1), fact(['obo:RO_0002529', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002529', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002486', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002485', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002485', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002486', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004035', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002263', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002325', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002452', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002200', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002231', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002014', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002335', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002213', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002429', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002341', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002337', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002025', X, Y1],add,M1,U1), fact(['obo:RO_0002025', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002241', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002309', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002486', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002578', X, X1],add,M1,U1), fact(['obo:RO_0002327', X2, X1],add,M2,U2), fact(['obo:GO_0003674', X1],add,M3,U3), fact(['obo:GO_0003674', X],add,M4,U4) ==> member(U,[U1,U2,U3,U4]) | check_neg_mark([M1,M2,M3,M4],M), fact(['obo:RO_0002233', X, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002629', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002578', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011002', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002566', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002473', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004031', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002352', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002233', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002352', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002507', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002304', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004047', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002352', X3, X1],add,M1,U1), fact(['obo:RO_0002333', X2, X3],add,M2,U2), fact(['obo:RO_0002014', X, X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002630', X2, X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002158', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002352', X3, X1],add,M1,U1), fact(['obo:RO_0002333', X2, X3],add,M2,U2), fact(['obo:RO_0002015', X, X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002629', X2, X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002412', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002090', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002013', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002215', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002286', X0, X1],add,M1,U1), fact(['obo:RO_0002497', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002204', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000301', X, Y],add,M1,U1), fact(['obo:RO_0000301', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0000301', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001018', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002557', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002556', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002556', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002557', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000302', X, Y],add,M1,U1), fact(['obo:RO_0000302', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0000302', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002371', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002177', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002176', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002493', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002492', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002345', X0, X1],add,M1,U1), fact(['obo:BFO_0000051', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002345', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002112', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002106', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002106', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002112', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002023', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002022', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002353', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002234', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002234', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002353', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002022', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002296', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002257', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002256', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002256', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002257', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002026', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['foaf:image', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002559', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002506', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002332', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002297', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002234', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002373', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002567', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002557', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002453', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002342', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002021', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002121', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000540', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002305', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002254', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000000', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002450', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002513', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002599', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002597', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002639', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002635', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011014', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002461', X0, X1],add,M1,U1), fact(['obo:RO_0002468', X1, X2],add,M2,U2), fact(['obo:RO_0002461', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002443', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004014', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002554', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002553', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002553', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002554', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002176', X1, X0],add,M1,U1), fact(['obo:RO_0002176', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002170', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002630', X, X2],add,M1,U1), fact(['obo:RO_0002025', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002630', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004019', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004023', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002331', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002110', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002102', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002102', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002110', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002224', X0, X1],add,M1,U1), fact(['obo:RO_0002400', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002400', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002221', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002219', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002219', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002221', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002298', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002526', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004022', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004019', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002509', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002506', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002566', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002517', X, Y],add,M1,U1), fact(['obo:RO_0002517', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002517', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002570', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0001018', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002519', X, Y],add,M1,U1), fact(['obo:RO_0002519', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002519', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002340', X0, X1],add,M1,U1), fact(['obo:BFO_0000051', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002340', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002162', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002384', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002324', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011023', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011022', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002518', X, Y],add,M1,U1), fact(['obo:RO_0002518', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002518', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002456', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002442', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002441', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002106', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002232', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002565', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002503', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002502', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002300', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002552', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002008', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002375', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X2, X],add,M1,U1), fact(['obo:BFO_0000066', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X2, X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002526', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002248', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003311', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002516', X, Y],add,M1,U1), fact(['obo:RO_0002516', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002516', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002377', X0, X1],add,M1,U1), fact(['obo:RO_0002381', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002380', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002356', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000000', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002458', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002439', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002439', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002458', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002552', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002170', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002180', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002211', X1, X2],add,M2,U2), fact(['obo:RO_0002333', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002448', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002509', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002408', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002630', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003302', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004022', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002445', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002444', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002176', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002240', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002244', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004018', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002477', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002476', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0004047', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004032', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002015', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002013', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002525', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002526', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009001', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011007', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000300', X, Y],add,M1,U1), fact(['obo:RO_0000300', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0000300', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002472', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002616', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002433', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000000', X, X1],add,M1,U1), fact(['obo:BFO_0000003', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000003', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002551', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011010', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002412', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002405', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002405', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002412', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002293', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002291', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002291', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002293', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002460', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002229', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002333', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002573', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002426', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002516', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002524', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002223', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002205', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002509', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002577', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002462', X0, X1],add,M1,U1), fact(['obo:RO_0002468', X1, X2],add,M2,U2), fact(['obo:RO_0002463', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002444', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011016', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011004', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002411', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002404', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002404', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002254', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002463', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002461', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002525', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002523', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004019', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002569', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002380', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002380', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002569', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000301', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000300', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002432', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002103', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000301', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011022', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011003', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011010', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001023', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003003', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002468', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002465', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002025', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002134', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:topObjectProperty', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:BFO_0000051', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002327', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002411', X1, X2],add,M2,U2), fact(['obo:RO_0002333', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002566', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X0, X1],add,M1,U1), fact(['obo:RO_0002482', X1, X2],add,M2,U2), fact(['obo:RO_0002400', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002480', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002201', X, Y1],add,M1,U1), fact(['obo:RO_0002201', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002384', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:BFO_0000062', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000062', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002515', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002527', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002570', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002462', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002461', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002552', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002007', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002517', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002516', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002516', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002517', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000054', X0, X1],add,M1,U1), fact(['obo:RO_0002404', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0009501', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002109', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002105', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002105', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002109', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002113', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002130', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002448', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002234', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0040036', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002524', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002526', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002572', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000141', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002445', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002453', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002329', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004028', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002492', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002497', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002018', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002180', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002326', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002216', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002524', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002522', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002332', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003307', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003305', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002511', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002510', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002510', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002511', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003003', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002450', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002625', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002624', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002624', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002625', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002452', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002625', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002619', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002343', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002014', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002013', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002349', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002513', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002512', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002512', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002513', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002375', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002354', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002297', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002297', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002354', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002507', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002568', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002567', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002224', X0, X1],add,M1,U1), fact(['obo:RO_0002230', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002087', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002025', X, X1],add,M1,U1), fact(['obo:RO_0002233', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002233', X, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002007', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011003', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002485', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000001', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002158', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002627', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002626', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002626', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002627', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002331', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002476', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0005634', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002339', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002339', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001020', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008506', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004006', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002244', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002253', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002252', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002252', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002253', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002447', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002436', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002558', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002472', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002472', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002558', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002225', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002202', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003301', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002615', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002615', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003301', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002216', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002130', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002006', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002006', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002130', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002333', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002327', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002333', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002578', X, X2],add,M1,U1), fact(['obo:RO_0002025', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002578', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011009', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002354', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002353', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002406', X0, X1],add,M1,U1), fact(['obo:RO_0002407', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002578', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002412', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002473', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008508', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002619', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000300', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000540', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002608', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002500', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002608', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002134', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002005', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002005', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002134', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004025', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002255', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002254', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002254', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002255', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002256', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011009', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011021', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002255', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002385', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002258', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002257', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002376', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002211', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002407', X0, X1],add,M1,U1), fact(['obo:RO_0002406', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000063', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002584', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002595', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002207', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002202', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002233', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002497', X0, X1],add,M1,U1), fact(['obo:RO_0002082', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002455', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002442', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002012', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002630', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002023', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002023', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002630', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002585', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002105', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002211', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002005', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002476', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002636', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002108', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002107', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002107', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002108', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001022', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002210', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002203', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002114', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002120', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004026', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040035', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002437', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002018', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009002', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008504', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002496', X0, X1],add,M1,U1), fact(['obo:BFO_0000062', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002519', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002518', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002518', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002519', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002414', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002352', X3, X1],add,M1,U1), fact(['obo:RO_0002333', X2, X3],add,M2,U2), fact(['obo:RO_0002013', X, X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002578', X2, X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002180', X1, X],add,M1,U1), fact(['obo:BFO_0000015', X1],add,M2,U2), fact(['obo:BFO_0000015', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002018', X1, X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002216', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003310', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002635', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002216', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002373', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002285', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X0, X1],add,M1,U1), fact(['obo:RO_0002215', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002584', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002204', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011008', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X0, X1],add,M1,U1), fact(['obo:RO_0002131', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002131', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002591', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002411', X, X1],add,M1,U1), fact(['obo:RO_0002131', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002411', X, X1],add,M1,U1), fact(['obo:RO_0002131', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002021', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002479', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002508', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002566', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011002', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0072519', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002468', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002507', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002509', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000066', X1, X0],add,M1,U1), fact(['obo:RO_0002234', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0003000', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002437', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002434', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008507', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002618', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002130', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002375', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002411', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000063', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:RO_0002210', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002287', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002428', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002431', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003301', X, X],add,M1,U1) ==> member(U,[U1]) | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002254', X0, X1],add,M1,U1), fact(['obo:RO_0002162', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002162', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002131', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002013', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002249', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002248', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002248', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002249', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000302', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000300', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002220', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002445', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002443', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002233', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002454', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002534', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002532', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002177', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004023', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002489', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002488', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004018', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004017', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004029', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002444', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002454', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004020', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002450', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002203', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002388', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002120', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000302', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002465', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002563', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002160', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002162', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002131', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002203', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002387', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003002', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002467', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002465', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002529', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002527', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002254', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002372', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002567', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002629', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002024', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002024', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002629', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002500', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002595', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002556', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002454', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002304', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002619', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002577', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002492', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002490', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002438', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008503', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002248', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002202', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002325', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001021', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002297', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002488', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002488', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002298', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002292', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002206', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002206', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002292', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0010002', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002226', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002004', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002641', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002635', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002630', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002212', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002157', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002295', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002324', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002570', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002595', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002026', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['foaf:image', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002102', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000540', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002623', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002622', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002622', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002623', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003306', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003304', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009001', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001018', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002115', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002103', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002598', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002596', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002638', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002634', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004046', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002150', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002607', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002610', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002207', X0, X1],add,M1,U1), fact(['obo:RO_0001025', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002226', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002008', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002514', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002532', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002512', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002213', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002304', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008505', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002313', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002337', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004015', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004028', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002085', X, Y],add,M1,U1), fact(['obo:RO_0002085', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002085', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002202', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002258', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002303', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:ENVO_01000254', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002446', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002437', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002121', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002121', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002233', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011007', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004001', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002012', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002429', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002428', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002337', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002111', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002006', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002640', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002634', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002589', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002586', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001023', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001021', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001021', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001023', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002508', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002507', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002507', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002508', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004032', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002264', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002012', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002630', X1, X2],add,M2,U2), fact(['obo:RO_0002333', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002449', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002232', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002305', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004035', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X0, X1],add,M1,U1), fact(['obo:RO_0002202', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002254', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002563', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002464', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011007', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011023', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002255', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002476', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0005634', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002005', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001001', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011010', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011021', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002593', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002497', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003003', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002349', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000000', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002296', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004047', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008502', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004002', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002383', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002376', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002451', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002313', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002408', X0, X1],add,M1,U1), fact(['obo:RO_0002409', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002409', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004016', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004024', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004023', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002256', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002315', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002511', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002150', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002597', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002596', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002404', X, X1],add,M1,U1), fact(['obo:RO_0002131', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002404', X, X1],add,M1,U1), fact(['obo:RO_0002131', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002619', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002618', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002618', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002619', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002591', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002592', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002388', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002387', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002206', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002406', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002629', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002409', X0, X1],add,M1,U1), fact(['obo:RO_0002408', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002409', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003308', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002610', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002209', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002208', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002208', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002209', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X0, X1],add,M1,U1), fact(['obo:RO_0002211', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002596', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004024', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004008', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002234', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003002', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002449', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002404', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002427', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002258', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002324', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002212', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002305', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002634', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002436', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002434', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002574', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002437', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001022', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001020', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001020', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001022', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002220', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002163', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002130', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002130', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002440', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000300', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000540', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002588', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002592', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004010', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002414', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002411', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002588', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002297', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002375', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002630', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002578', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009004', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002507', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002577', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002228', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002258', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009001', X, X],add,M1,U1) ==> member(U,[U1]) | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004023', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', X0, X1],add,M1,U1), fact(['obo:RO_0001025', X2, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002379', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002210', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002207', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002207', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002210', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002411', X, Y],add,M1,U1), fact(['obo:RO_0002411', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002411', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008506', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002479', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002355', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009501', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X0, X1],add,M1,U1), fact(['obo:BFO_0000066', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002232', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009002', X, X],add,M1,U1) ==> member(U,[U1]) | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001021', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002237', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011003', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002357', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002101', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001001', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011009', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009003', X, X],add,M1,U1) ==> member(U,[U1]) | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002449', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011021', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011003', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009005', X, X],add,M1,U1) ==> member(U,[U1]) | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004024', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004022', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002200', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002624', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002618', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002219', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002220', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002627', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002019', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002233', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002249', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002286', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002384', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002156', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002440', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002348', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002491', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002492', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002211', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002428', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002434', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X0, X1],add,M1,U1), fact(['obo:BFO_0000066', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002479', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004028', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002501', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002418', X, Y],add,M1,U1), fact(['obo:RO_0002418', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002418', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002488', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002496', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002374', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002156', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002469', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002571', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002322', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002334', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002150', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002551', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002340', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002020', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002488', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002490', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002353', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002336', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002113', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002113', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002431', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0010002', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0010001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0010001', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0010002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002566', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002506', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002414', X, Y],add,M1,U1), fact(['obo:RO_0002414', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002414', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002618', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002338', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002338', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:BFO_0000063', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000063', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004010', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004000', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002264', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002500', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002352', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002100', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000540', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002207', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002225', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002344', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002337', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002209', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002501', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003305', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003304', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002002', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004011', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004001', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002206', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002356', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002295', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002461', X0, X1],add,M1,U1), fact(['obo:RO_0002465', X1, X2],add,M2,U2), fact(['obo:RO_0002461', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002440', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002287', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002286', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002578', X, X2],add,M1,U1), fact(['obo:RO_0002333', X2, X3],add,M2,U2), fact(['obo:RO_0002333', X, X1],add,M3,U3), fact(['obo:GO_0016301', X],add,M4,U4) ==> member(U,[U1,U2,U3,U4]) | check_neg_mark([M1,M2,M3,M4],M), fact(['obo:RO_0002447', X1, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002629', X1, X2],add,M2,U2), fact(['obo:RO_0002333', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['obo:RO_0002450', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004025', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004025', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002471', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002438', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002614', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002616', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002227', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002431', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002264', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002480', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002436', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002360', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002201', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002200', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002200', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002201', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002016', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002336', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002008', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008505', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002321', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002626', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002574', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000052', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002314', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002215', X0, X1],add,M1,U1), fact(['obo:RO_0002212', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002597', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002177', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011002', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002299', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0040036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002496', X0, X1],add,M1,U1), fact(['obo:RO_0002082', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011008', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002411', X0, X1],add,M1,U1), fact(['obo:RO_0002402', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002403', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002435', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002435', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002428', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002263', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002434', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002434', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002427', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002501', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002102', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002102', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002303', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X0, X1],add,M1,U1), fact(['obo:RO_0002211', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002211', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002595', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002406', X0, X1],add,M1,U1), fact(['obo:RO_0002406', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0004842', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002482', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002567', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002121', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002110', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002302', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004033', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002264', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002335', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002334', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002554', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002453', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002177', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002567', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002576', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002437', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002437', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002345', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002020', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009005', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0009001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002436', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002436', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002132', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001001', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002405', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002404', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004011', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002111', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:topObjectProperty', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002312', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002320', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002246', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002206', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004025', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004023', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002430', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002428', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002510', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002330', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002469', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002457', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002457', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002469', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002104', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002331', X0, X1],add,M1,U1), fact(['obo:RO_0002212', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002430', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002131', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002327', X0, X1],add,M1,U1), fact(['obo:RO_0002304', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0004034', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002418', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002501', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002330', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011008', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011024', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002334', X, Y],add,M1,U1), fact(['obo:RO_0002334', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002334', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002253', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002375', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002010', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0010002', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000031', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002092', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002085', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002085', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002092', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002220', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002453', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002440', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002444', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002443', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002507', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002509', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002533', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002532', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004008', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002409', X0, X1],add,M1,U1), fact(['obo:RO_0002409', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002213', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002211', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002131', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002205', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002204', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002204', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002205', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002409', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002212', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004010', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000017', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002322', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:ENVO_01000254', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002378', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002376', Y, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002482', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002564', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002625', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002445', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000059', X0, X1],add,M1,U1), fact(['obo:RO_0000053', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0010002', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002497', X0, X1],add,M1,U1), fact(['obo:BFO_0000063', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002497', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004015', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004005', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004005', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004015', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002491', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002488', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002466', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002465', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002244', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002310', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0003001', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002224', X0, X1],add,M1,U1), fact(['obo:BFO_0000066', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002231', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004016', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004006', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004006', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004016', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0010001', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002531', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002528', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:RO_0002215', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002329', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002010', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002418', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004000', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002216', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002328', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002523', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002514', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0008505', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001010', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002236', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002444', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011004', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002409', X, Y],add,M1,U1), fact(['obo:RO_0002409', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002409', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004014', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004004', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004004', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004014', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002203', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002202', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002202', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002203', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002325', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002243', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002244', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002026', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002323', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001022', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0003302', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004026', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002528', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002527', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002012', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004025', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:OGMS_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002019', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0004872', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002497', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002487', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009501', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002410', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011004', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0009004', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011013', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002331', X0, X1],add,M1,U1), fact(['obo:RO_0002213', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002429', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002407', X, Y],add,M1,U1), fact(['obo:RO_0002407', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002407', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002291', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002206', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002514', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002532', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002623', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002619', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004012', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004002', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004012', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002111', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002334', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002427', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002131', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002131', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002202', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002206', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000006', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004013', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004003', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0004003', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0004013', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002519', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002525', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0011013', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0011004', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002258', X0, X1],add,M1,U1), fact(['obo:RO_0002496', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002496', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002179', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002170', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002221', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002220', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0003824', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0003674', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0016874', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0003824', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0016740', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0003824', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0019787', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0016881', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0004842', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0019787', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0016301', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0016772', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0016879', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0016874', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0016772', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0016740', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0016881', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0016879', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000053', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000053', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000073', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000022', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000004', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000046', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000046', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000026', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000034', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000060', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000060', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000007', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000024', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000018', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000047', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000052', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000052', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000061', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000074', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000066', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000033', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000004', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000051', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000029', X, Y],add,M1,U1), fact(['obo:RO_HOM0000030', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000045', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000045', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000037', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000037', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000029', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000028', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000057', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000058', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000044', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000044', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000036', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000074', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000003', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000050', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000043', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000043', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000042', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000042', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000029', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000029', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000046', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000047', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000036', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000028', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000028', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000027', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000027', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000062', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000013', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000032', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000029', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000034', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000034', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000073', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000073', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000023', X, Y],add,M1,U1), fact(['obo:RO_HOM0000024', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000027', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000066', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000071', X, Y],add,M1,U1), fact(['obo:RO_HOM0000072', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000066', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000066', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000012', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000062', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000065', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000031', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000029', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000044', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000003', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000058', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000058', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000072', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000072', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000052', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000030', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000065', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000065', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000057', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000071', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000071', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000034', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000037', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000063', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000063', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000044', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000005', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000049', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000049', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000020', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000062', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000062', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000060', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000012', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000054', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000062', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000048', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000048', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000065', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000050', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000055', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000055', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000020', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000019', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000047', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000047', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000061', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000061', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000015', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000054', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000054', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000001', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000063', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000054', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000006', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000005', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000005', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000011', X, Y],add,M1,U1), fact(['obo:RO_HOM0000017', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000012', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000012', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000004', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000004', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000066', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000008', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000011', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000003', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000003', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000037', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000049', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000010', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000010', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000048', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000036', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000002', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000043', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000055', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000006', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000075', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000034', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000023', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000017', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000049', X, Y],add,M1,U1), fact(['obo:RO_HOM0000050', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000069', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000069', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000003', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000014', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000011', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000058', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000003', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000075', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000075', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000009', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000068', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000068', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000001', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000051', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000029', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000060', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000019', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000025', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000034', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000074', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000074', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000072', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000008', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000000', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000026', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000026', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000002', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000071', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000016', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000033', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000033', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000053', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000025', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000025', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000010', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000006', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000019', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000019', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000032', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000032', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000031', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000031', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000019', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000008', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000024', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000024', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000018', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000042', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000030', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000030', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000022', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000017', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000045', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000016', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000016', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000016', X, Y],add,M1,U1), fact(['obo:RO_HOM0000062', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000009', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000009', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000023', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000023', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000001', X, Y],add,M1,U1), fact(['obo:RO_HOM0000002', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000015', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000015', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000057', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000005', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000005', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000042', X, Y],add,M1,U1), fact(['obo:RO_HOM0000043', X, Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000022', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000022', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000068', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000018', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000030', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000028', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000014', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000014', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000008', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000008', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000069', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000011', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000028', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000008', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000020', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000020', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000013', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000013', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000007', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000007', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000048', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000017', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000073', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_HOM0000053', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002090', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002087', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002087', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002090', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002093', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002084', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002084', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002093', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002087', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000062', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002084', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002081', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000062', X, Y],add,M1,U1), fact(['obo:BFO_0000062', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000062', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000063', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000063', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000062', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000062', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000063', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002229', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002229', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002230', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002092', X0, X1],add,M1,U1), fact(['obo:BFO_0000062', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000062', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002091', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002083', X, Y],add,M1,U1), fact(['obo:RO_0002083', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002083', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002230', X, Y],add,M1,U1), fact(['obo:RO_0002230', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002230', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002091', X0, X1],add,M1,U1), fact(['obo:BFO_0000062', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000062', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002091', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002089', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002224', X, Y],add,M1,U1), fact(['obo:RO_0002224', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002224', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002086', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002082', X, Y],add,M1,U1), fact(['obo:RO_0002082', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002082', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002222', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002092', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002093', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002089', X, Y],add,M1,U1), fact(['obo:RO_0002089', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002089', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000063', X, Y],add,M1,U1), fact(['obo:BFO_0000063', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000063', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000062', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002093', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002093', X0, X1],add,M1,U1), fact(['obo:BFO_0000062', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002086', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002224', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002088', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002090', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000063', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000063', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000062', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002086', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002091', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002083', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002081', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002229', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002091', X0, X1],add,M1,U1), fact(['obo:BFO_0000060', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002089', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000060', X, Y],add,M1,U1), fact(['obo:BFO_0000060', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000060', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002223', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002222', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002224', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002223', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002223', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002224', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002082', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002081', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000062', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002092', X, Y],add,M1,U1), fact(['obo:RO_0002092', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002092', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002222', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002091', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002088', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002088', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002091', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002086', X, Y],add,M1,U1), fact(['obo:RO_0002086', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0002086', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', X, Y],add,M1,U1), fact(['obo:RO_0001025', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0001025', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000057', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000086', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000067', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000066', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000066', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000067', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000055', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000017', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000079', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000034', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000079', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000087', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000023', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000080', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, Y],add,M1,U1), fact(['obo:BFO_0000050', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000050', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X0, X1],add,M1,U1), fact(['obo:BFO_0000066', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000066', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000085', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000034', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000002', X],add,M1,U1), fact(['obo:BFO_0000050', X, X1],add,M2,U2), fact(['obo:BFO_0000003', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000003', X],add,M1,U1), fact(['obo:BFO_0000050', X, X1],add,M2,U2), fact(['obo:BFO_0000002', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000055', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000054', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000054', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000055', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000056', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000066', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000058', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000031', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002350', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001015', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001015', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001025', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001015', X, Y],add,M1,U1), fact(['obo:RO_0001015', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:RO_0001015', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000086', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000080', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000080', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000086', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000054', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000092', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000055', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000056', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000066', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000057', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000056', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000056', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000057', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002351', X, X],add,M1,U1) ==> member(U,[U1]) | fact(['owl:Nothing', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002351', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000087', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000081', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000081', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000087', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002002', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002002', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002000', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002002', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002351', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002350', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002350', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002351', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000091', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000081', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000085', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000092', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000091', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000091', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000092', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000085', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000086', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000019', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000006', X],add,M1,U1), fact(['obo:RO_0001025', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000053', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000085', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000079', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000079', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000085', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000066', X0, X1],add,M1,U1), fact(['obo:BFO_0000050', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000066', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000059', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000058', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000058', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000059', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000087', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002002', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000141', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000091', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000016', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000050', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000051', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000051', X, Y],add,M1,U1), fact(['obo:BFO_0000051', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000051', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000059', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000053', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000052', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000052', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000057', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000058', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000059', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000031', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001001', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001000', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001000', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0001001', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000054', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0001025', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000006', X1],add,M1,U1), fact(['obo:RO_0001025', X, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X, X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000087', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000053', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0000091', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0001199', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0000052', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0000052', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0000051', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0000051', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0001241', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0002124', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0000141', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0001241', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0000001', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0000141', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0000051', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0016020', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0042734', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044456', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0005634', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044464', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0043005', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0042995', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0045211', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044456', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0044456', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044464', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0044464', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0042995', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044464', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0045211', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0016020', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0030424', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0043005', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0042734', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0016020', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0008150', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0030425', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0043005', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0045202', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000040', X],add,M1,U1), fact(['obo:BFO_0000141', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000017', X],add,M1,U1), fact(['obo:BFO_0000019', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000002', X],add,M1,U1), fact(['obo:BFO_0000003', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000016', X],add,M1,U1), fact(['obo:BFO_0000023', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000004', X],add,M1,U1), fact(['obo:BFO_0000020', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000004', X],add,M1,U1), fact(['obo:BFO_0000031', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000020', X],add,M1,U1), fact(['obo:BFO_0000031', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0000006', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CL_0000000', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0030000', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0000000', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0030000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0000011', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0010000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0010000', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0001001', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0001000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0000011', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002577', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0000001', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CL_0000540', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CL_0000000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:ENVO_00000428', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:ENVO_01000254', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0002009', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0000052', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002207', X, X1],add,M1,U1), fact(['obo:CL_0000000', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:CL_0000000', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:ENVO_01000254', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0002577', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002207', X, X1],add,M1,U1), fact(['obo:CARO_0010000', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:CARO_0010000', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:OGMS_0000031', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000016', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:UPHENO_0001001', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0000001', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0001010', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000040', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0001000', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0000006', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000000', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0000007', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000141', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:CARO_0000003', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:CARO_0000006', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0000402', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0002009', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0000052', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:PATO_0000051', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:PATO_0000051', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000019', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0003674', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000015', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002262', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000087', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002260', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000087', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_0002261', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['obo:RO_0000087', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000019', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000016', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000031', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000015', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000003', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000020', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000004', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000002', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000017', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000020', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000141', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000040', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000004', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000005', X],add,M1,U1) ==> member(U,[U1]) | fact(['go:ObsoleteClass', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000034', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000016', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000006', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000141', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000023', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:BFO_0000017', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0085031', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044403', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0051705', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0007610', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0051704', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0008150', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0007610', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0050896', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0051816', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0007631', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0044403', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044419', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0044419', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0051704', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0072519', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044403', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0007631', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0007610', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0050896', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0008150', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0051702', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044419', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0085030', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0044403', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0051850', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0051702', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0051705', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0051704', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0051850', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0051816', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:GO_0051850', X],add,M1,U1) ==> member(U,[U1]) | fact(['obo:GO_0051705', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, X1],add,M1,U1), fact(['obo:BFO_0000020', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000020', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, X1],add,M1,U1), fact(['obo:BFO_0000031', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000031', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000000', X, X1],add,M1,U1), fact(['obo:BFO_0000002', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000002', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, X1],add,M1,U1), fact(['obo:BFO_0000003', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000003', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, X1],add,M1,U1), fact(['obo:BFO_0000002', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000002', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:RO_HOM0000000', X, X1],add,M1,U1), fact(['obo:BFO_0000003', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000003', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, X1],add,M1,U1), fact(['obo:BFO_0000004', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000004', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, X1],add,M1,U1), fact(['obo:BFO_0000017', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000017', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000050', X, X1],add,M1,U1), fact(['obo:BFO_0000019', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['obo:BFO_0000019', X1],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000141', X],add,M1,U1), fact(['obo:BFO_0000051', X, X1],add,M2,U2), fact(['obo:BFO_0000040', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['obo:BFO_0000040', X],add,M1,U1), fact(['obo:BFO_0000050', X, X1],add,M2,U2), fact(['obo:BFO_0000141', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).

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
finish_update, phase(5), current_update(U) <=> 
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


% -- predicates for explicit facts --
explicit('obo:RO_0002178').
explicit('obo:RO_0002372').
explicit('obo:RO_0011013').
explicit('obo:RO_0002242').
explicit('obo:RO_0002235').
explicit('obo:RO_0002009').
explicit('obo:RO_0002104').
explicit('obo:RO_0002179').
explicit('obo:RO_0002025').
explicit('obo:RO_0002004').
explicit('obo:RO_0002326').
explicit('obo:RO_0002015').
explicit('obo:RO_0009003').
explicit('obo:RO_0002495').
explicit('obo:RO_0002332').
explicit('obo:RO_0002355').
explicit('obo:GO_0085030').
explicit('obo:RO_0002303').
explicit('obo:RO_0011015').
explicit('obo:RO_0003002').
explicit('obo:RO_NonExist').
explicit('obo:RO_0002315').
explicit('obo:RO_0002382').
explicit('obo:RO_0002583').
explicit('obo:RO_0004009').
explicit('obo:RO_0002593').
explicit('obo:RO_0002590').
explicit('obo:RO_0002214').
explicit('obo:RO_0002600').
explicit('obo:RO_0002007').
explicit('obo:RO_0002348').
explicit('obo:RO_0002373').
explicit('obo:RO_0002531').
explicit('obo:RO_0002587').
explicit('obo:RO_0002408').
explicit('obo:RO_0004029').
explicit('obo:RO_0004020').
explicit('obo:RO_0002530').
explicit('obo:RO_0002426').
explicit('obo:RO_0004021').
explicit('obo:RO_0009002').
explicit('obo:GO_0085031').
explicit('obo:RO_0002301').
explicit('obo:RO_0004030').
explicit('obo:RO_0011014').
explicit('obo:RO_0002016').
explicit('obo:RO_0002010').
explicit('obo:RO_0002478').
explicit('obo:RO_0002245').
explicit('obo:RO_0002470').
explicit('obo:GO_0016301').
explicit('obo:RO_0002342').
explicit('obo:RO_0003309').
explicit('obo:RO_0002378').
explicit('obo:RO_0002383').
explicit('obo:RO_0002573').
explicit('obo:RO_0003303').
explicit('obo:RO_0002505').
explicit('obo:RO_0002151').
explicit('obo:RO_0002381').
explicit('obo:RO_0002555').
explicit('obo:RO_0002299').
explicit('obo:RO_0004027').
explicit('obo:RO_0002572').
explicit('obo:RO_0002425').
explicit('obo:RO_0002473').
explicit('obo:RO_0002585').
explicit('obo:RO_0002402').
explicit('obo:RO_0002218').
explicit('obo:RO_0002520').
explicit('obo:RO_0002343').
explicit('obo:RO_0002325').
explicit('obo:RO_0002452').
explicit('obo:RO_0002014').
explicit('obo:RO_0002341').
explicit('obo:RO_0002241').
explicit('obo:RO_0002176').
explicit('obo:RO_0002493').
explicit('obo:RO_0002296').
explicit('obo:RO_0002026').
explicit('obo:RO_0002298').
explicit('obo:RO_0004022').
explicit('obo:RO_0002570').
explicit('obo:RO_0002565').
explicit('obo:RO_0002503').
explicit('obo:RO_0002300').
explicit('obo:RO_0002008').
explicit('obo:RO_0003311').
explicit('obo:RO_0002356').
explicit('obo:RO_0002240').
explicit('obo:RO_0002477').
explicit('obo:RO_0011007').
explicit('obo:RO_0002433').
explicit('obo:RO_0002462').
explicit('obo:RO_0002463').
explicit('obo:RO_0011016').
explicit('obo:RO_0003003').
explicit('obo:RO_0003307').
explicit('obo:RO_0002349').
explicit('obo:RO_0002568').
explicit('obo:RO_0002406').
explicit('obo:RO_0002012').
explicit('obo:RO_0003310').
explicit('obo:RO_0002285').
explicit('obo:RO_0011008').
explicit('obo:RO_0002591').
explicit('obo:GO_0072519').
explicit('obo:RO_0002534').
explicit('obo:RO_0002489').
explicit('obo:RO_0002160').
explicit('obo:RO_0003306').
explicit('obo:RO_0002150').
explicit('obo:RO_0002607').
explicit('obo:RO_0008505').
explicit('obo:RO_0002446').
explicit('obo:RO_0002111').
explicit('obo:RO_0002589').
explicit('obo:RO_0002451').
explicit('obo:RO_0003308').
explicit('obo:RO_0004008').
explicit('obo:RO_0002588').
explicit('obo:RO_0009004').
explicit('obo:RO_0002228').
explicit('obo:RO_0002237').
explicit('obo:RO_0002357').
explicit('obo:RO_0009005').
explicit('obo:RO_0002019').
explicit('obo:RO_0002491').
explicit('obo:RO_0002374').
explicit('obo:RO_0002322').
explicit('obo:RO_0002471').
explicit('obo:RO_0002614').
explicit('obo:RO_0002227').
explicit('obo:RO_0002360').
explicit('obo:GO_0004842').
explicit('obo:RO_0002312').
explicit('obo:RO_0002246').
explicit('obo:RO_0002533').
explicit('obo:RO_0002236').
explicit('obo:RO_0002243').
explicit('obo:BFO_0000006').
explicit('obo:PATO_0001199').
explicit('obo:PATO_0002124').
explicit('obo:GO_0042734').
explicit('obo:GO_0045211').
explicit('obo:GO_0030424').
explicit('obo:GO_0030425').
explicit('obo:GO_0045202').
explicit('obo:CARO_0000011').
explicit('obo:ENVO_00000428').
explicit('obo:CARO_0000007').
explicit('obo:PATO_0000402').
explicit('obo:RO_0002262').
explicit('obo:RO_0002260').
explicit('obo:RO_0002261').
explicit('obo:BFO_0000005').
explicit('obo:GO_0051850').
