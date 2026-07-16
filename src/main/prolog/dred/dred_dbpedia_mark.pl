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
phase(1), fact(['skos:OrderedCollection', X],O1,M1,_) \ fact(['skos:Collection', X],add,_,U) <=> member(del,[O1]) | fact(['skos:Collection', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:broadMatch', X, Y],O1,M1,_) \ fact(['skos:mappingRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:broadMatch', Y, X],O1,M1,_) \ fact(['skos:narrowMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrowMatch', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', Y, X],O1,M1,_) \ fact(['skos:broadMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:broadMatch', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:broader', X, Y],O1,M1,_) \ fact(['skos:broaderTransitive', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:broader', Y, X],O1,M1,_) \ fact(['skos:narrower', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrower', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', X, Y],O1,M1,_) \ fact(['skos:semanticRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', Y, X],O1,M1,_) \ fact(['skos:narrowerTransitive', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', Y, X],O1,M1,_) \ fact(['skos:broaderTransitive', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', X, Y],O1,M1,_), fact(['skos:broaderTransitive', Y, Z],O2,M2,_) \ fact(['skos:broaderTransitive', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('skos:broaderTransitive',O1,M1),('skos:broaderTransitive',O2,M2)],M), fact(['skos:broaderTransitive', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['skos:closeMatch', X, Y],O1,M1,_) \ fact(['skos:mappingRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:closeMatch', Y, X],O1,M1,_) \ fact(['skos:closeMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:closeMatch', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', X, Y],O1,M1,_) \ fact(['skos:closeMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:closeMatch', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', Y, X],O1,M1,_) \ fact(['skos:exactMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:exactMatch', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', X, Y],O1,M1,_), fact(['skos:exactMatch', Y, Z],O2,M2,_) \ fact(['skos:exactMatch', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('skos:exactMatch',O1,M1),('skos:exactMatch',O2,M2)],M), fact(['skos:exactMatch', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', Y, X],O1,M1,_) \ fact(['skos:topConceptOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:topConceptOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', Y, X],O1,M1,_) \ fact(['skos:hasTopConcept', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:hasTopConcept', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', X, _],O1,M1,_) \ fact(['skos:ConceptScheme', X],add,_,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', _, Y],O1,M1,_) \ fact(['skos:Concept', Y],add,_,U) <=> member(del,[O1]) | fact(['skos:Concept', Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:inScheme', _, Y],O1,M1,_) \ fact(['skos:ConceptScheme', Y],add,_,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:mappingRelation', X, Y],O1,M1,_) \ fact(['skos:semanticRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:member', X, _],O1,M1,_) \ fact(['skos:Collection', X],add,_,U) <=> member(del,[O1]) | fact(['skos:Collection', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:memberList', X, Y],O1,M1,_), fact(['skos:memberList', X, Z],O2,M2,_) \ fact(['owl:sameAs', Y, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('skos:memberList',O1,M1),('skos:memberList',O2,M2)],M), fact(['owl:sameAs', Y, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['skos:memberList', X, _],O1,M1,_) \ fact(['skos:OrderedCollection', X],add,_,U) <=> member(del,[O1]) | fact(['skos:OrderedCollection', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', X, Y],O1,M1,_) \ fact(['skos:mappingRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', X, Y],O1,M1,_) \ fact(['skos:narrower', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrower', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:narrower', X, Y],O1,M1,_) \ fact(['skos:narrowerTransitive', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', X, Y],O1,M1,_) \ fact(['skos:semanticRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', X, Y],O1,M1,_), fact(['skos:narrowerTransitive', Y, Z],O2,M2,_) \ fact(['skos:narrowerTransitive', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('skos:narrowerTransitive',O1,M1),('skos:narrowerTransitive',O2,M2)],M), fact(['skos:narrowerTransitive', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['skos:related', X, Y],O1,M1,_) \ fact(['skos:semanticRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:related', Y, X],O1,M1,_) \ fact(['skos:related', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:related', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', X, Y],O1,M1,_) \ fact(['skos:mappingRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', X, Y],O1,M1,_) \ fact(['skos:related', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:related', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', Y, X],O1,M1,_) \ fact(['skos:relatedMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:relatedMatch', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:semanticRelation', X, _],O1,M1,_) \ fact(['skos:Concept', X],add,_,U) <=> member(del,[O1]) | fact(['skos:Concept', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:semanticRelation', _, Y],O1,M1,_) \ fact(['skos:Concept', Y],add,_,U) <=> member(del,[O1]) | fact(['skos:Concept', Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', X, Y],O1,M1,_) \ fact(['skos:inScheme', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:inScheme', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', X, _],O1,M1,_) \ fact(['skos:Concept', X],add,_,U) <=> member(del,[O1]) | fact(['skos:Concept', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', _, Y],O1,M1,_) \ fact(['skos:ConceptScheme', Y],add,_,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', Y],del,M1,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact(['skos:OrderedCollection', X],add,M1,_) \ fact(['skos:Collection', X],del,_,U) <=> true | fact(['skos:Collection', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:broadMatch', X, Y],add,M1,_) \ fact(['skos:mappingRelation', X, Y],del,_,U) <=> true | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:broadMatch', Y, X],add,M1,_) \ fact(['skos:narrowMatch', X, Y],del,_,U) <=> true | fact(['skos:narrowMatch', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:narrowMatch', Y, X],add,M1,_) \ fact(['skos:broadMatch', X, Y],del,_,U) <=> true | fact(['skos:broadMatch', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:broader', X, Y],add,M1,_) \ fact(['skos:broaderTransitive', X, Y],del,_,U) <=> true | fact(['skos:broaderTransitive', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:broader', Y, X],add,M1,_) \ fact(['skos:narrower', X, Y],del,_,U) <=> true | fact(['skos:narrower', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:broaderTransitive', X, Y],add,M1,_) \ fact(['skos:semanticRelation', X, Y],del,_,U) <=> true | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:broaderTransitive', Y, X],add,M1,_) \ fact(['skos:narrowerTransitive', X, Y],del,_,U) <=> true | fact(['skos:narrowerTransitive', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:narrowerTransitive', Y, X],add,M1,_) \ fact(['skos:broaderTransitive', X, Y],del,_,U) <=> true | fact(['skos:broaderTransitive', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:broaderTransitive', X, Y],add,M1,_), fact(['skos:broaderTransitive', Y, Z],add,M2,_) \ fact(['skos:broaderTransitive', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['skos:broaderTransitive', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['skos:closeMatch', X, Y],add,M1,_) \ fact(['skos:mappingRelation', X, Y],del,_,U) <=> true | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:closeMatch', Y, X],add,M1,_) \ fact(['skos:closeMatch', X, Y],del,_,U) <=> true | fact(['skos:closeMatch', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:exactMatch', X, Y],add,M1,_) \ fact(['skos:closeMatch', X, Y],del,_,U) <=> true | fact(['skos:closeMatch', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:exactMatch', Y, X],add,M1,_) \ fact(['skos:exactMatch', X, Y],del,_,U) <=> true | fact(['skos:exactMatch', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:exactMatch', X, Y],add,M1,_), fact(['skos:exactMatch', Y, Z],add,M2,_) \ fact(['skos:exactMatch', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['skos:exactMatch', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['skos:hasTopConcept', Y, X],add,M1,_) \ fact(['skos:topConceptOf', X, Y],del,_,U) <=> true | fact(['skos:topConceptOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:topConceptOf', Y, X],add,M1,_) \ fact(['skos:hasTopConcept', X, Y],del,_,U) <=> true | fact(['skos:hasTopConcept', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:hasTopConcept', X, _],add,M1,_) \ fact(['skos:ConceptScheme', X],del,_,U) <=> true | fact(['skos:ConceptScheme', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:hasTopConcept', _, Y],add,M1,_) \ fact(['skos:Concept', Y],del,_,U) <=> true | fact(['skos:Concept', Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:inScheme', _, Y],add,M1,_) \ fact(['skos:ConceptScheme', Y],del,_,U) <=> true | fact(['skos:ConceptScheme', Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:mappingRelation', X, Y],add,M1,_) \ fact(['skos:semanticRelation', X, Y],del,_,U) <=> true | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:member', X, _],add,M1,_) \ fact(['skos:Collection', X],del,_,U) <=> true | fact(['skos:Collection', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:memberList', X, Y],add,M1,_), fact(['skos:memberList', X, Z],add,M2,_) \ fact(['owl:sameAs', Y, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['skos:memberList', X, _],add,M1,_) \ fact(['skos:OrderedCollection', X],del,_,U) <=> true | fact(['skos:OrderedCollection', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:narrowMatch', X, Y],add,M1,_) \ fact(['skos:mappingRelation', X, Y],del,_,U) <=> true | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:narrowMatch', X, Y],add,M1,_) \ fact(['skos:narrower', X, Y],del,_,U) <=> true | fact(['skos:narrower', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:narrower', X, Y],add,M1,_) \ fact(['skos:narrowerTransitive', X, Y],del,_,U) <=> true | fact(['skos:narrowerTransitive', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:narrowerTransitive', X, Y],add,M1,_) \ fact(['skos:semanticRelation', X, Y],del,_,U) <=> true | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:narrowerTransitive', X, Y],add,M1,_), fact(['skos:narrowerTransitive', Y, Z],add,M2,_) \ fact(['skos:narrowerTransitive', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['skos:narrowerTransitive', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['skos:related', X, Y],add,M1,_) \ fact(['skos:semanticRelation', X, Y],del,_,U) <=> true | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:related', Y, X],add,M1,_) \ fact(['skos:related', X, Y],del,_,U) <=> true | fact(['skos:related', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:relatedMatch', X, Y],add,M1,_) \ fact(['skos:mappingRelation', X, Y],del,_,U) <=> true | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:relatedMatch', X, Y],add,M1,_) \ fact(['skos:related', X, Y],del,_,U) <=> true | fact(['skos:related', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:relatedMatch', Y, X],add,M1,_) \ fact(['skos:relatedMatch', X, Y],del,_,U) <=> true | fact(['skos:relatedMatch', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:semanticRelation', X, _],add,M1,_) \ fact(['skos:Concept', X],del,_,U) <=> true | fact(['skos:Concept', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:semanticRelation', _, Y],add,M1,_) \ fact(['skos:Concept', Y],del,_,U) <=> true | fact(['skos:Concept', Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:topConceptOf', X, Y],add,M1,_) \ fact(['skos:inScheme', X, Y],del,_,U) <=> true | fact(['skos:inScheme', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:topConceptOf', X, _],add,M1,_) \ fact(['skos:Concept', X],del,_,U) <=> true | fact(['skos:Concept', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['skos:topConceptOf', _, Y],add,M1,_) \ fact(['skos:ConceptScheme', Y],del,_,U) <=> true | fact(['skos:ConceptScheme', Y],add,M1,U), applied_rules(1,red).

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
phase(5), fact(['skos:OrderedCollection', X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:Collection', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:broadMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:broadMatch', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:narrowMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowMatch', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:broadMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:broader', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:broaderTransitive', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:broader', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:narrower', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:broaderTransitive', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:broaderTransitive', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:narrowerTransitive', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowerTransitive', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:broaderTransitive', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:broaderTransitive', X, Y],add,M1,U1), fact(['skos:broaderTransitive', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['skos:broaderTransitive', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['skos:closeMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:closeMatch', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:closeMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:closeMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:exactMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', X, Y],add,M1,U1), fact(['skos:exactMatch', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['skos:exactMatch', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:topConceptOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:hasTopConcept', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['skos:ConceptScheme', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', _, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:Concept', Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:inScheme', _, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:ConceptScheme', Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:mappingRelation', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:member', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['skos:Collection', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:memberList', X, Y],add,M1,U1), fact(['skos:memberList', X, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['skos:memberList', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['skos:OrderedCollection', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:narrower', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrower', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:narrowerTransitive', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowerTransitive', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowerTransitive', X, Y],add,M1,U1), fact(['skos:narrowerTransitive', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['skos:narrowerTransitive', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['skos:related', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:related', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:related', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:relatedMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:relatedMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:related', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:relatedMatch', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:relatedMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:semanticRelation', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['skos:Concept', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:semanticRelation', _, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:Concept', Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:inScheme', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['skos:Concept', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', _, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:ConceptScheme', Y],add,M1,U), applied_rules(1,ins).

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
explicit('skos:broader').
explicit('skos:member').
explicit('skos:memberList').
