
%----------------
% -- write materialization to stream --
finish_update, stream(S), current_update(N) ==> writeln(S, materialization(N)). 	
finish_update, stream(S), fact(F,add,_,_) ==> writeln(S,F).	
finish_update, stream(S) ==> writeln(S,""), flush_output(S).


% -- move on to next update --
% transform marked explicit add-facts into del-facts
finish_update \ fact([P|L],add,1,U) <=> 
	explicit(P) |
	fact([P|L],del,_,U),
	marked_facts(1,add,[P|L]).
% ... and marked implicit add-facts into facts that need to be checked
finish_update \ fact(F,add,1,U) <=> 
	fact(F,chk,_,U),
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
% check if at least one element is marked, indicated by 1
check_neg_mark([],_) <=> true.		
check_neg_mark([(P,1)|_],M) <=> explicit(P) | M = 1.
check_neg_mark([_|L],M) <=> check_neg_mark(L,M).	


% -- statistical information --
% count number of rule applications for each phase
applied_rules(N,P), applied_rules(M,P) <=>
	K is N + M,
	applied_rules(K,P).
		
% distinguish between explicit and implicit facts	
	% explicit
marked_facts(N,add,[P|_]) <=> explicit(P) | marked_facts(N,negEx).	
	% implicit
marked_facts(N,add,_) <=> marked_facts(N,negIm).

% count number of marked facts
marked_facts(N,O), marked_facts(M,O) <=>
	K is N + M,
	marked_facts(K,O).		

% print out collected statistics
print, applied_rules_list(P,L) ==> writeln(applied_rules(P,L)).
print, marked_facts_list(O,L) ==> writeln(marked_facts(O,L)).


% -- predicates for explicit facts --