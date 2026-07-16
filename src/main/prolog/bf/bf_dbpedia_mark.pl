/*
Backward/Forward with Marking
*/

:- use_module(library(chr)).
:- chr_constraint init/1, stream/1,
	read_stream/1, phase/1,
	available_input/1, extract_input/2,
	update/3, stream_end/0,
	fact/4, finish_update/0,
	check_done/0, no_del/0,
	num_updates/1, current_update/1,
	pending_fact/3,
	marked_facts/2, marked_facts/3, applied_rules/2, 
	applied_rules_list/2, marked_facts_list/2,
	applied_rules_init, marked_facts_init,
	applied_rules_list_init, marked_facts_list_init,
	count_marked_facts, check_neg_mark/2,
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
		

% -- initialie lists to collect number of applied rules and marked facts for each update --
applied_rules_list_init <=>
	applied_rules_list(del,[]),
	applied_rules_list(bwd,[]),
	applied_rules_list(fwd,[]),
	applied_rules_list(ins,[]).
marked_facts_list_init <=>
	marked_facts_list(negIm,[]),
	marked_facts_list(negEx,[]).
	
% introduce counter for each type of rules
applied_rules_init <=>
	applied_rules(0,del),
	applied_rules(0,bwd),
	applied_rules(0,fwd),
	applied_rules(0,ins).	
% introduce counter for each type of marked facts
marked_facts_init <=>
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
applied_rules(_,O), num_updates(U), current_update(U) ==> 
	member(O,[ins,fwd]) |
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
%fact(F,O,M1,_) \ fact(F,O,M2,_) <=> M1 = M2.
fact(F,O,_,_) \ fact(F,O,_,_) <=> true.

% mark facts that are deleted by next update
fact(F,_,M,_) \ pending_fact(F,del,_) <=>
	% var(M) |
	M = 1.
	

%-------------------------------------------------
% -- deletions --
% remove deleted add-fact
fact(F,del,_,_) \ fact(F,add,_,_) <=> true.


% -- find every directly affected fact that needs to be checked --
phase(1), fact(['skos:OrderedCollection', X],O1,_,_) \ fact(['skos:Collection', X],add,_,U) <=> member(del,[O1]) | fact(['skos:Collection', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:broadMatch', X, Y],O1,_,_) \ fact(['skos:mappingRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:broadMatch', Y, X],O1,_,_) \ fact(['skos:narrowMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrowMatch', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', Y, X],O1,_,_) \ fact(['skos:broadMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:broadMatch', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:broader', X, Y],O1,_,_) \ fact(['skos:broaderTransitive', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:broader', Y, X],O1,_,_) \ fact(['skos:narrower', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrower', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', X, Y],O1,_,_) \ fact(['skos:semanticRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', Y, X],O1,_,_) \ fact(['skos:narrowerTransitive', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', Y, X],O1,_,_) \ fact(['skos:broaderTransitive', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', X, Y],O1,_,_), fact(['skos:broaderTransitive', Y, Z],O2,_,_) \ fact(['skos:broaderTransitive', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['skos:broaderTransitive', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:closeMatch', X, Y],O1,_,_) \ fact(['skos:mappingRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:closeMatch', Y, X],O1,_,_) \ fact(['skos:closeMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:closeMatch', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', X, Y],O1,_,_) \ fact(['skos:closeMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:closeMatch', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', Y, X],O1,_,_) \ fact(['skos:exactMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:exactMatch', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', X, Y],O1,_,_), fact(['skos:exactMatch', Y, Z],O2,_,_) \ fact(['skos:exactMatch', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['skos:exactMatch', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', Y, X],O1,_,_) \ fact(['skos:topConceptOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:topConceptOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', Y, X],O1,_,_) \ fact(['skos:hasTopConcept', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:hasTopConcept', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', X, _],O1,_,_) \ fact(['skos:ConceptScheme', X],add,_,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', _, Y],O1,_,_) \ fact(['skos:Concept', Y],add,_,U) <=> member(del,[O1]) | fact(['skos:Concept', Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:inScheme', _, Y],O1,_,_) \ fact(['skos:ConceptScheme', Y],add,_,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:mappingRelation', X, Y],O1,_,_) \ fact(['skos:semanticRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:member', X, _],O1,_,_) \ fact(['skos:Collection', X],add,_,U) <=> member(del,[O1]) | fact(['skos:Collection', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:memberList', X, Y],O1,_,_), fact(['skos:memberList', X, Z],O2,_,_) \ fact(['owl:sameAs', Y, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:memberList', X, _],O1,_,_) \ fact(['skos:OrderedCollection', X],add,_,U) <=> member(del,[O1]) | fact(['skos:OrderedCollection', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', X, Y],O1,_,_) \ fact(['skos:mappingRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', X, Y],O1,_,_) \ fact(['skos:narrower', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrower', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:narrower', X, Y],O1,_,_) \ fact(['skos:narrowerTransitive', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', X, Y],O1,_,_) \ fact(['skos:semanticRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', X, Y],O1,_,_), fact(['skos:narrowerTransitive', Y, Z],O2,_,_) \ fact(['skos:narrowerTransitive', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['skos:narrowerTransitive', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:related', X, Y],O1,_,_) \ fact(['skos:semanticRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:related', Y, X],O1,_,_) \ fact(['skos:related', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:related', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', X, Y],O1,_,_) \ fact(['skos:mappingRelation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', X, Y],O1,_,_) \ fact(['skos:related', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:related', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', Y, X],O1,_,_) \ fact(['skos:relatedMatch', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:relatedMatch', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:semanticRelation', X, _],O1,_,_) \ fact(['skos:Concept', X],add,_,U) <=> member(del,[O1]) | fact(['skos:Concept', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:semanticRelation', _, Y],O1,_,_) \ fact(['skos:Concept', Y],add,_,U) <=> member(del,[O1]) | fact(['skos:Concept', Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', X, Y],O1,_,_) \ fact(['skos:inScheme', X, Y],add,_,U) <=> member(del,[O1]) | fact(['skos:inScheme', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', X, _],O1,_,_) \ fact(['skos:Concept', X],add,_,U) <=> member(del,[O1]) | fact(['skos:Concept', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', _, Y],O1,_,_) \ fact(['skos:ConceptScheme', Y],add,_,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', Y],chk,_,U), applied_rules(1,del).

% -- delete already processed del-facts to avoid repetitions with new del-facts --
phase(1) <=> phase(2).
phase(2) \ fact(_,del,_,_) <=> true.
phase(2) <=> no_del, phase(3).


% prevent repeated checking
fact(F,chk1,_,_) \ fact(F,chk,_,_) <=> true.
fact(F,chk1,_,_) \ fact(F,add,_,_) <=> true.

% -- check facts for alternative derivation --
phase(3) \ fact(F,chk,M,U) <=> fact(F,chk1,M,U), check_done.

% fact can be proven
fact(F,prv,_,_) \ fact(F,_,_,_) <=> true.
fact([P|L],chk1,M,U) <=> explicit(P) | fact([P|L],prv,M,U).

% - forward -
fact(['skos:OrderedCollection', X],prv,_,_) \ fact(['skos:Collection', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:Collection', X],prv,_,U), applied_rules(1,fwd).
fact(['skos:broadMatch', X, Y],prv,_,_) \ fact(['skos:mappingRelation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:mappingRelation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:broadMatch', Y, X],prv,_,_) \ fact(['skos:narrowMatch', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:narrowMatch', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:narrowMatch', Y, X],prv,_,_) \ fact(['skos:broadMatch', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:broadMatch', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:broader', X, Y],prv,M1,_) \ fact(['skos:broaderTransitive', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:broaderTransitive', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['skos:broader', Y, X],prv,M1,_) \ fact(['skos:narrower', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:narrower', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['skos:broaderTransitive', X, Y],prv,_,_) \ fact(['skos:semanticRelation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:semanticRelation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:broaderTransitive', Y, X],prv,_,_) \ fact(['skos:narrowerTransitive', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:narrowerTransitive', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:narrowerTransitive', Y, X],prv,_,_) \ fact(['skos:broaderTransitive', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:broaderTransitive', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:broaderTransitive', X, Y],prv,_,_), fact(['skos:broaderTransitive', Y, Z],prv,_,_) \ fact(['skos:broaderTransitive', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:broaderTransitive', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['skos:closeMatch', X, Y],prv,_,_) \ fact(['skos:mappingRelation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:mappingRelation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:closeMatch', Y, X],prv,_,_) \ fact(['skos:closeMatch', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:closeMatch', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:exactMatch', X, Y],prv,_,_) \ fact(['skos:closeMatch', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:closeMatch', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:exactMatch', Y, X],prv,_,_) \ fact(['skos:exactMatch', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:exactMatch', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:exactMatch', X, Y],prv,_,_), fact(['skos:exactMatch', Y, Z],prv,_,_) \ fact(['skos:exactMatch', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:exactMatch', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['skos:hasTopConcept', Y, X],prv,_,_) \ fact(['skos:topConceptOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:topConceptOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:topConceptOf', Y, X],prv,_,_) \ fact(['skos:hasTopConcept', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:hasTopConcept', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:hasTopConcept', X, _],prv,_,_) \ fact(['skos:ConceptScheme', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:ConceptScheme', X],prv,_,U), applied_rules(1,fwd).
fact(['skos:hasTopConcept', _, Y],prv,_,_) \ fact(['skos:Concept', Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:Concept', Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:inScheme', _, Y],prv,_,_) \ fact(['skos:ConceptScheme', Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:ConceptScheme', Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:mappingRelation', X, Y],prv,_,_) \ fact(['skos:semanticRelation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:semanticRelation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:member', X, _],prv,M1,_) \ fact(['skos:Collection', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:Collection', X],prv,M1,U), applied_rules(1,fwd).
fact(['skos:memberList', X, Y],prv,M1,_), fact(['skos:memberList', X, Z],prv,M2,_) \ fact(['owl:sameAs', Y, Z],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('skos:memberList',M1),('skos:memberList',M2)],M), fact(['owl:sameAs', Y, Z],prv,M,U), applied_rules(1,fwd).
fact(['skos:memberList', X, _],prv,M1,_) \ fact(['skos:OrderedCollection', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:OrderedCollection', X],prv,M1,U), applied_rules(1,fwd).
fact(['skos:narrowMatch', X, Y],prv,_,_) \ fact(['skos:mappingRelation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:mappingRelation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:narrowMatch', X, Y],prv,_,_) \ fact(['skos:narrower', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:narrower', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:narrower', X, Y],prv,_,_) \ fact(['skos:narrowerTransitive', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:narrowerTransitive', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:narrowerTransitive', X, Y],prv,_,_) \ fact(['skos:semanticRelation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:semanticRelation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:narrowerTransitive', X, Y],prv,_,_), fact(['skos:narrowerTransitive', Y, Z],prv,_,_) \ fact(['skos:narrowerTransitive', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:narrowerTransitive', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['skos:related', X, Y],prv,_,_) \ fact(['skos:semanticRelation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:semanticRelation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:related', Y, X],prv,_,_) \ fact(['skos:related', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:related', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:relatedMatch', X, Y],prv,_,_) \ fact(['skos:mappingRelation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:mappingRelation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:relatedMatch', X, Y],prv,_,_) \ fact(['skos:related', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:related', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:relatedMatch', Y, X],prv,_,_) \ fact(['skos:relatedMatch', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:relatedMatch', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:semanticRelation', X, _],prv,_,_) \ fact(['skos:Concept', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:Concept', X],prv,_,U), applied_rules(1,fwd).
fact(['skos:semanticRelation', _, Y],prv,_,_) \ fact(['skos:Concept', Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:Concept', Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:topConceptOf', X, Y],prv,_,_) \ fact(['skos:inScheme', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:inScheme', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['skos:topConceptOf', X, _],prv,_,_) \ fact(['skos:Concept', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:Concept', X],prv,_,U), applied_rules(1,fwd).
fact(['skos:topConceptOf', _, Y],prv,_,_) \ fact(['skos:ConceptScheme', Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['skos:ConceptScheme', Y],prv,_,U), applied_rules(1,fwd).


% - backward -
fact(['skos:Collection', X],chk1,_,_), fact(['skos:OrderedCollection', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:OrderedCollection', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:mappingRelation', X, Y],chk1,_,_), fact(['skos:broadMatch', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:broadMatch', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:narrowMatch', X, Y],chk1,_,_), fact(['skos:broadMatch', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:broadMatch', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:broadMatch', X, Y],chk1,_,_), fact(['skos:narrowMatch', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowMatch', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:broaderTransitive', X, Y],chk1,_,_), fact(['skos:broader', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:broader', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:narrower', X, Y],chk1,_,_), fact(['skos:broader', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:broader', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:semanticRelation', X, Y],chk1,_,_), fact(['skos:broaderTransitive', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:narrowerTransitive', X, Y],chk1,_,_), fact(['skos:broaderTransitive', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:broaderTransitive', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:broaderTransitive', X, Y],chk1,_,_), fact(['skos:narrowerTransitive', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowerTransitive', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:broaderTransitive', X, Z],chk1,_,_), fact(['skos:broaderTransitive', X, Y],O1,M1,U1), fact(['skos:broaderTransitive', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['skos:broaderTransitive', X, Y],chk1,M1,U1), fact(['skos:broaderTransitive', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['skos:mappingRelation', X, Y],chk1,_,_), fact(['skos:closeMatch', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:closeMatch', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:closeMatch', X, Y],chk1,_,_), fact(['skos:closeMatch', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:closeMatch', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:closeMatch', X, Y],chk1,_,_), fact(['skos:exactMatch', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:exactMatch', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:exactMatch', X, Y],chk1,_,_), fact(['skos:exactMatch', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:exactMatch', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:exactMatch', X, Z],chk1,_,_), fact(['skos:exactMatch', X, Y],O1,M1,U1), fact(['skos:exactMatch', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['skos:exactMatch', X, Y],chk1,M1,U1), fact(['skos:exactMatch', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['skos:topConceptOf', X, Y],chk1,_,_), fact(['skos:hasTopConcept', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:hasTopConcept', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:hasTopConcept', X, Y],chk1,_,_), fact(['skos:topConceptOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:topConceptOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:ConceptScheme', X],chk1,_,_), fact(['skos:hasTopConcept', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:hasTopConcept', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:Concept', Y],chk1,_,_), fact(['skos:hasTopConcept', Anon0, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:hasTopConcept', Anon0, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:ConceptScheme', Y],chk1,_,_), fact(['skos:inScheme', Anon0, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:inScheme', Anon0, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:semanticRelation', X, Y],chk1,_,_), fact(['skos:mappingRelation', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:Collection', X],chk1,_,_), fact(['skos:member', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:member', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y, Z],chk1,_,_), fact(['skos:memberList', X, Y],O1,M1,U1), fact(['skos:memberList', X, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['skos:memberList', X, Y],chk1,M1,U1), fact(['skos:memberList', X, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['skos:OrderedCollection', X],chk1,_,_), fact(['skos:memberList', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:memberList', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:mappingRelation', X, Y],chk1,_,_), fact(['skos:narrowMatch', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowMatch', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:narrower', X, Y],chk1,_,_), fact(['skos:narrowMatch', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowMatch', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:narrowerTransitive', X, Y],chk1,_,_), fact(['skos:narrower', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:narrower', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:semanticRelation', X, Y],chk1,_,_), fact(['skos:narrowerTransitive', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:narrowerTransitive', X, Z],chk1,_,_), fact(['skos:narrowerTransitive', X, Y],O1,M1,U1), fact(['skos:narrowerTransitive', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['skos:narrowerTransitive', X, Y],chk1,M1,U1), fact(['skos:narrowerTransitive', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['skos:semanticRelation', X, Y],chk1,_,_), fact(['skos:related', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:related', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:related', X, Y],chk1,_,_), fact(['skos:related', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:related', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:mappingRelation', X, Y],chk1,_,_), fact(['skos:relatedMatch', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:relatedMatch', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:related', X, Y],chk1,_,_), fact(['skos:relatedMatch', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:relatedMatch', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:relatedMatch', X, Y],chk1,_,_), fact(['skos:relatedMatch', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:relatedMatch', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:Concept', X],chk1,_,_), fact(['skos:semanticRelation', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:semanticRelation', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:Concept', Y],chk1,_,_), fact(['skos:semanticRelation', Anon0, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:semanticRelation', Anon0, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:inScheme', X, Y],chk1,_,_), fact(['skos:topConceptOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:topConceptOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:Concept', X],chk1,_,_), fact(['skos:topConceptOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:topConceptOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['skos:ConceptScheme', Y],chk1,_,_), fact(['skos:topConceptOf', Anon0, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['skos:topConceptOf', Anon0, Y],chk1,M1,U1), applied_rules(1,bwd).

	
% turn facts without proof into del-facts
check_done \ fact(F,chk1,_,U) <=> fact(F,del,_,U).
check_done <=> true.


% -- repeat above steps iff new del-facts given --
fact(_,del,_,_) \ no_del <=> true.
phase(3), no_del  <=> phase(4). % move to insertion phase
phase(3) <=> phase(1).


% -- reset deletion phase --
phase(4) \ fact(F,prv,M,U) <=> fact(F,add,M,U).
phase(4) <=> true.


%-------------------------------------------------
% -- insertions --

% finish processing when every new fact has been inserted
current_update(U) \ update(add,[],U) <=> phase(5), finish_update.
% insert every new fact
current_update(U) \ update(add,[F|Fs],U) <=>
	fact(F,add,_,U),
	update(add,Fs,U).
	
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
phase(5), fact(['skos:broaderTransitive', X, Y],add,M1,U1), fact(['skos:broaderTransitive', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('skos:broaderTransitive',M1),('skos:broaderTransitive',M2)],M), fact(['skos:broaderTransitive', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['skos:closeMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:closeMatch', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:closeMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:closeMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:exactMatch', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', X, Y],add,M1,U1), fact(['skos:exactMatch', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('skos:exactMatch',M1),('skos:exactMatch',M2)],M), fact(['skos:exactMatch', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:topConceptOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['skos:hasTopConcept', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['skos:ConceptScheme', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', _, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:Concept', Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:inScheme', _, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:ConceptScheme', Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:mappingRelation', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:member', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['skos:Collection', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:memberList', X, Y],add,M1,U1), fact(['skos:memberList', X, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('skos:memberList',M1),('skos:memberList',M2)],M), fact(['owl:sameAs', Y, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['skos:memberList', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['skos:OrderedCollection', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowMatch', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:narrower', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrower', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:narrowerTransitive', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowerTransitive', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowerTransitive', X, Y],add,M1,U1), fact(['skos:narrowerTransitive', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('skos:narrowerTransitive',M1),('skos:narrowerTransitive',M2)],M), fact(['skos:narrowerTransitive', X, Z],add,M,U), applied_rules(1,ins).
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
% transform marked explicit add-facts into del-facts
finish_update \ fact([P|L],add,1,U) <=> 
	explicit(P) |
	fact([P|L],del,_,U),
	% marked_facts(1,add,[P|L]).
	marked_facts(1,negEx).
% ... and marked implicit add-facts into facts that need to be checked
finish_update \ fact(F,add,1,U) <=> 
	fact(F,chk,_,U),
	% marked_facts(1,add,F).
	marked_facts(1,negIm).

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
%marked_facts(N,add,[P|_]) <=> explicit(P) | marked_facts(N,negEx).	
	% implicit
%marked_facts(N,add,_) <=> marked_facts(N,negIm).

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
