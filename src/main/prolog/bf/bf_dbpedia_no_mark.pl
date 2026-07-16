/*
Backward/Forward (without Marking)
*/

:- use_module(library(chr)).
:- chr_constraint init/1, stream/1,
	read_stream/1, phase/1,
	available_input/1, extract_input/2,
	update/2, stream_end/0,
	fact/3, finish_update/0,
	check_done/0, no_del/0,
	num_updates/1,
	applied_rules/2, 	applied_rules_list/2, 
	applied_rules_init, applied_rules_list_init,
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
			applied_rules_init,
			applied_rules_list_init,
			read_stream(infinite),
			% indicate end of procesing
			writeln(Stream,"end"),
			flush_output(Stream),
			print
		),
		close(Stream)
	).		


% -- statistical information --
% count number of rule applications for each phase
applied_rules(N,P), applied_rules(M,P) <=>
	K is N + M,
	applied_rules(K,P).
	
% print out collected statistics
print, applied_rules_list(P,L) ==> writeln(applied_rules(P,L)).

% initialie lists to collect number of applied rules for each update
applied_rules_list_init <=>
	applied_rules_list(del,[]),
	applied_rules_list(bwd,[]),
	applied_rules_list(fwd,[]),
	applied_rules_list(ins,[]).
	
% introduce counter for each type of rules
applied_rules_init <=>
	applied_rules(0,del),
	applied_rules(0,bwd),
	applied_rules(0,fwd),	
	applied_rules(0,ins).		


% -- remove constraints for simpler output --
clean \ fact(_,_,_) <=> true.	
clean \ stream(_) <=> true.
clean \ phase(_) <=> true.	
		


%-------------------------------------------------	
% -- read input from stream --

% stop when stream finished
stream_end \ read_stream(_) <=> true.

% try to get next input from stream
stream(S) \ read_stream(WaitTime) <=> 
	wait_for_input([S],L,WaitTime),
	available_input(L).
	
% no input from stream available
available_input([]) <=> true.
% get input from stream
available_input([S]), num_updates(N) <=>
	M is N+1,
	num_updates(M),
	% read added and deleted facts from stream
	read_line_to_string(S,A),
	read_line_to_string(S,D),	
	extract_input(A,D).

% input indicates end of stream
extract_input("[]","[]") <=>	
	stream_end.

% input is an update
extract_input(X,Y) <=>	
	term_string(A,X),  
	term_string(D,Y),
	update(del,D),
	update(add,A).	


% start processing when every deleted fact has been inserted
update(del,[]) <=> phase(1).
% insert every deleted fact
update(del,[F|Fs]) <=>
	fact(F,del,_),
	update(del,Fs).
	
	
%-----------------
% no duplicates
fact(F,O,_) \ fact(F,O,_) <=> true.


%-------------------------------------------------
% -- deletions --
% remove deleted add-fact
fact(F,del,U) \ fact(F,add,U2) <=> U = U2.


% -- find every directly affected fact that needs to be checked --
phase(1), fact(['skos:OrderedCollection', X],O1,_) \ fact(['skos:Collection', X],add,U) <=> member(del,[O1]) | fact(['skos:Collection', X],chk,U), applied_rules(1,del).
phase(1), fact(['skos:broadMatch', X, Y],O1,_) \ fact(['skos:mappingRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:broadMatch', Y, X],O1,_) \ fact(['skos:narrowMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrowMatch', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', Y, X],O1,_) \ fact(['skos:broadMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:broadMatch', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:broader', X, Y],O1,_) \ fact(['skos:broaderTransitive', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:broader', Y, X],O1,_) \ fact(['skos:narrower', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrower', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', X, Y],O1,_) \ fact(['skos:semanticRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', Y, X],O1,_) \ fact(['skos:narrowerTransitive', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', Y, X],O1,_) \ fact(['skos:broaderTransitive', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', X, Y],O1,_), fact(['skos:broaderTransitive', Y, Z],O2,_) \ fact(['skos:broaderTransitive', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['skos:broaderTransitive', X, Z],chk,U), applied_rules(1,del).
phase(1), fact(['skos:closeMatch', X, Y],O1,_) \ fact(['skos:mappingRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:closeMatch', Y, X],O1,_) \ fact(['skos:closeMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:closeMatch', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', X, Y],O1,_) \ fact(['skos:closeMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:closeMatch', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', Y, X],O1,_) \ fact(['skos:exactMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:exactMatch', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', X, Y],O1,_), fact(['skos:exactMatch', Y, Z],O2,_) \ fact(['skos:exactMatch', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['skos:exactMatch', X, Z],chk,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', Y, X],O1,_) \ fact(['skos:topConceptOf', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:topConceptOf', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', Y, X],O1,_) \ fact(['skos:hasTopConcept', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:hasTopConcept', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', X, _],O1,_) \ fact(['skos:ConceptScheme', X],add,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', X],chk,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', _, Y],O1,_) \ fact(['skos:Concept', Y],add,U) <=> member(del,[O1]) | fact(['skos:Concept', Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:inScheme', _, Y],O1,_) \ fact(['skos:ConceptScheme', Y],add,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:mappingRelation', X, Y],O1,_) \ fact(['skos:semanticRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:member', X, _],O1,_) \ fact(['skos:Collection', X],add,U) <=> member(del,[O1]) | fact(['skos:Collection', X],chk,U), applied_rules(1,del).
phase(1), fact(['skos:memberList', X, Y],O1,_), fact(['skos:memberList', X, Z],O2,_) \ fact(['owl:sameAs', Y, Z],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y, Z],chk,U), applied_rules(1,del).
phase(1), fact(['skos:memberList', X, _],O1,_) \ fact(['skos:OrderedCollection', X],add,U) <=> member(del,[O1]) | fact(['skos:OrderedCollection', X],chk,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', X, Y],O1,_) \ fact(['skos:mappingRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', X, Y],O1,_) \ fact(['skos:narrower', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrower', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:narrower', X, Y],O1,_) \ fact(['skos:narrowerTransitive', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', X, Y],O1,_) \ fact(['skos:semanticRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', X, Y],O1,_), fact(['skos:narrowerTransitive', Y, Z],O2,_) \ fact(['skos:narrowerTransitive', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['skos:narrowerTransitive', X, Z],chk,U), applied_rules(1,del).
phase(1), fact(['skos:related', X, Y],O1,_) \ fact(['skos:semanticRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:related', Y, X],O1,_) \ fact(['skos:related', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:related', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', X, Y],O1,_) \ fact(['skos:mappingRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', X, Y],O1,_) \ fact(['skos:related', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:related', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', Y, X],O1,_) \ fact(['skos:relatedMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:relatedMatch', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:semanticRelation', X, _],O1,_) \ fact(['skos:Concept', X],add,U) <=> member(del,[O1]) | fact(['skos:Concept', X],chk,U), applied_rules(1,del).
phase(1), fact(['skos:semanticRelation', _, Y],O1,_) \ fact(['skos:Concept', Y],add,U) <=> member(del,[O1]) | fact(['skos:Concept', Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', X, Y],O1,_) \ fact(['skos:inScheme', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:inScheme', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', X, _],O1,_) \ fact(['skos:Concept', X],add,U) <=> member(del,[O1]) | fact(['skos:Concept', X],chk,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', _, Y],O1,_) \ fact(['skos:ConceptScheme', Y],add,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', Y],chk,U), applied_rules(1,del).

% -- delete already processed del-facts to avoid repetitions with new del-facts --
phase(1) <=> phase(2).
phase(2) \ fact(_,del,_) <=> true.
phase(2) <=> no_del, phase(3).


% prevent repeated checking
fact(F,chk1,_) \ fact(F,chk,_) <=> true.
fact(F,chk1,_) \ fact(F,add,_) <=> true.

% -- check facts for alternative derivation --
phase(3) \ fact(F,chk,U) <=> fact(F,chk1,U), check_done.

% fact can be proven
fact(F,prv,_) \ fact(F,_,_) <=> true.
fact([P|L],chk1,U) <=> explicit(P) | fact([P|L],prv,U).
	
% - forward -
fact(['skos:OrderedCollection', X],prv,_) \ fact(['skos:Collection', X],O,U) <=> member(O,[chk,chk1]) | fact(['skos:Collection', X],prv,U), applied_rules(1,fwd).
fact(['skos:broadMatch', X, Y],prv,_) \ fact(['skos:mappingRelation', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:mappingRelation', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:broadMatch', Y, X],prv,_) \ fact(['skos:narrowMatch', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:narrowMatch', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:narrowMatch', Y, X],prv,_) \ fact(['skos:broadMatch', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:broadMatch', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:broader', X, Y],prv,_) \ fact(['skos:broaderTransitive', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:broaderTransitive', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:broader', Y, X],prv,_) \ fact(['skos:narrower', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:narrower', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:broaderTransitive', X, Y],prv,_) \ fact(['skos:semanticRelation', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:semanticRelation', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:broaderTransitive', Y, X],prv,_) \ fact(['skos:narrowerTransitive', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:narrowerTransitive', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:narrowerTransitive', Y, X],prv,_) \ fact(['skos:broaderTransitive', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:broaderTransitive', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:broaderTransitive', X, Y],prv,_), fact(['skos:broaderTransitive', Y, Z],prv,_) \ fact(['skos:broaderTransitive', X, Z],O,U) <=> member(O,[chk,chk1]) | fact(['skos:broaderTransitive', X, Z],prv,U), applied_rules(1,fwd).
fact(['skos:closeMatch', X, Y],prv,_) \ fact(['skos:mappingRelation', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:mappingRelation', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:closeMatch', Y, X],prv,_) \ fact(['skos:closeMatch', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:closeMatch', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:exactMatch', X, Y],prv,_) \ fact(['skos:closeMatch', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:closeMatch', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:exactMatch', Y, X],prv,_) \ fact(['skos:exactMatch', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:exactMatch', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:exactMatch', X, Y],prv,_), fact(['skos:exactMatch', Y, Z],prv,_) \ fact(['skos:exactMatch', X, Z],O,U) <=> member(O,[chk,chk1]) | fact(['skos:exactMatch', X, Z],prv,U), applied_rules(1,fwd).
fact(['skos:hasTopConcept', Y, X],prv,_) \ fact(['skos:topConceptOf', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:topConceptOf', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:topConceptOf', Y, X],prv,_) \ fact(['skos:hasTopConcept', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:hasTopConcept', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:hasTopConcept', X, _],prv,_) \ fact(['skos:ConceptScheme', X],O,U) <=> member(O,[chk,chk1]) | fact(['skos:ConceptScheme', X],prv,U), applied_rules(1,fwd).
fact(['skos:hasTopConcept', _, Y],prv,_) \ fact(['skos:Concept', Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:Concept', Y],prv,U), applied_rules(1,fwd).
fact(['skos:inScheme', _, Y],prv,_) \ fact(['skos:ConceptScheme', Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:ConceptScheme', Y],prv,U), applied_rules(1,fwd).
fact(['skos:mappingRelation', X, Y],prv,_) \ fact(['skos:semanticRelation', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:semanticRelation', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:member', X, _],prv,_) \ fact(['skos:Collection', X],O,U) <=> member(O,[chk,chk1]) | fact(['skos:Collection', X],prv,U), applied_rules(1,fwd).
fact(['skos:memberList', X, Y],prv,_), fact(['skos:memberList', X, Z],prv,_) \ fact(['owl:sameAs', Y, Z],O,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', Y, Z],prv,U), applied_rules(1,fwd).
fact(['skos:memberList', X, _],prv,_) \ fact(['skos:OrderedCollection', X],O,U) <=> member(O,[chk,chk1]) | fact(['skos:OrderedCollection', X],prv,U), applied_rules(1,fwd).
fact(['skos:narrowMatch', X, Y],prv,_) \ fact(['skos:mappingRelation', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:mappingRelation', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:narrowMatch', X, Y],prv,_) \ fact(['skos:narrower', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:narrower', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:narrower', X, Y],prv,_) \ fact(['skos:narrowerTransitive', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:narrowerTransitive', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:narrowerTransitive', X, Y],prv,_) \ fact(['skos:semanticRelation', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:semanticRelation', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:narrowerTransitive', X, Y],prv,_), fact(['skos:narrowerTransitive', Y, Z],prv,_) \ fact(['skos:narrowerTransitive', X, Z],O,U) <=> member(O,[chk,chk1]) | fact(['skos:narrowerTransitive', X, Z],prv,U), applied_rules(1,fwd).
fact(['skos:related', X, Y],prv,_) \ fact(['skos:semanticRelation', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:semanticRelation', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:related', Y, X],prv,_) \ fact(['skos:related', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:related', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:relatedMatch', X, Y],prv,_) \ fact(['skos:mappingRelation', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:mappingRelation', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:relatedMatch', X, Y],prv,_) \ fact(['skos:related', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:related', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:relatedMatch', Y, X],prv,_) \ fact(['skos:relatedMatch', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:relatedMatch', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:semanticRelation', X, _],prv,_) \ fact(['skos:Concept', X],O,U) <=> member(O,[chk,chk1]) | fact(['skos:Concept', X],prv,U), applied_rules(1,fwd).
fact(['skos:semanticRelation', _, Y],prv,_) \ fact(['skos:Concept', Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:Concept', Y],prv,U), applied_rules(1,fwd).
fact(['skos:topConceptOf', X, Y],prv,_) \ fact(['skos:inScheme', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:inScheme', X, Y],prv,U), applied_rules(1,fwd).
fact(['skos:topConceptOf', X, _],prv,_) \ fact(['skos:Concept', X],O,U) <=> member(O,[chk,chk1]) | fact(['skos:Concept', X],prv,U), applied_rules(1,fwd).
fact(['skos:topConceptOf', _, Y],prv,_) \ fact(['skos:ConceptScheme', Y],O,U) <=> member(O,[chk,chk1]) | fact(['skos:ConceptScheme', Y],prv,U), applied_rules(1,fwd).


% - backward -
fact(['skos:Collection', X],chk1,_), fact(['skos:OrderedCollection', X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:OrderedCollection', X],chk1,U1), applied_rules(1,bwd).
fact(['skos:mappingRelation', X, Y],chk1,_), fact(['skos:broadMatch', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:broadMatch', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:narrowMatch', X, Y],chk1,_), fact(['skos:broadMatch', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:broadMatch', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:broadMatch', X, Y],chk1,_), fact(['skos:narrowMatch', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowMatch', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:broaderTransitive', X, Y],chk1,_), fact(['skos:broader', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:broader', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:narrower', X, Y],chk1,_), fact(['skos:broader', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:broader', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:semanticRelation', X, Y],chk1,_), fact(['skos:broaderTransitive', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:narrowerTransitive', X, Y],chk1,_), fact(['skos:broaderTransitive', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:broaderTransitive', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:broaderTransitive', X, Y],chk1,_), fact(['skos:narrowerTransitive', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowerTransitive', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:broaderTransitive', X, Z],chk1,_), fact(['skos:broaderTransitive', X, Y],O1,U1), fact(['skos:broaderTransitive', Y, Z],O2,U2) ==> \+member(del,[O1,O2]) | fact(['skos:broaderTransitive', X, Y],chk1,U1), fact(['skos:broaderTransitive', Y, Z],chk1,U2), applied_rules(1,bwd).
fact(['skos:mappingRelation', X, Y],chk1,_), fact(['skos:closeMatch', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:closeMatch', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:closeMatch', X, Y],chk1,_), fact(['skos:closeMatch', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:closeMatch', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:closeMatch', X, Y],chk1,_), fact(['skos:exactMatch', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:exactMatch', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:exactMatch', X, Y],chk1,_), fact(['skos:exactMatch', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:exactMatch', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:exactMatch', X, Z],chk1,_), fact(['skos:exactMatch', X, Y],O1,U1), fact(['skos:exactMatch', Y, Z],O2,U2) ==> \+member(del,[O1,O2]) | fact(['skos:exactMatch', X, Y],chk1,U1), fact(['skos:exactMatch', Y, Z],chk1,U2), applied_rules(1,bwd).
fact(['skos:topConceptOf', X, Y],chk1,_), fact(['skos:hasTopConcept', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:hasTopConcept', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:hasTopConcept', X, Y],chk1,_), fact(['skos:topConceptOf', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:topConceptOf', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:ConceptScheme', X],chk1,_), fact(['skos:hasTopConcept', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['skos:hasTopConcept', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['skos:Concept', Y],chk1,_), fact(['skos:hasTopConcept', Anon0, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:hasTopConcept', Anon0, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:ConceptScheme', Y],chk1,_), fact(['skos:inScheme', Anon0, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:inScheme', Anon0, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:semanticRelation', X, Y],chk1,_), fact(['skos:mappingRelation', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:mappingRelation', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:Collection', X],chk1,_), fact(['skos:member', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['skos:member', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y, Z],chk1,_), fact(['skos:memberList', X, Y],O1,U1), fact(['skos:memberList', X, Z],O2,U2) ==> \+member(del,[O1,O2]) | fact(['skos:memberList', X, Y],chk1,U1), fact(['skos:memberList', X, Z],chk1,U2), applied_rules(1,bwd).
fact(['skos:OrderedCollection', X],chk1,_), fact(['skos:memberList', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['skos:memberList', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['skos:mappingRelation', X, Y],chk1,_), fact(['skos:narrowMatch', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowMatch', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:narrower', X, Y],chk1,_), fact(['skos:narrowMatch', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowMatch', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:narrowerTransitive', X, Y],chk1,_), fact(['skos:narrower', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:narrower', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:semanticRelation', X, Y],chk1,_), fact(['skos:narrowerTransitive', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:narrowerTransitive', X, Z],chk1,_), fact(['skos:narrowerTransitive', X, Y],O1,U1), fact(['skos:narrowerTransitive', Y, Z],O2,U2) ==> \+member(del,[O1,O2]) | fact(['skos:narrowerTransitive', X, Y],chk1,U1), fact(['skos:narrowerTransitive', Y, Z],chk1,U2), applied_rules(1,bwd).
fact(['skos:semanticRelation', X, Y],chk1,_), fact(['skos:related', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:related', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:related', X, Y],chk1,_), fact(['skos:related', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:related', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:mappingRelation', X, Y],chk1,_), fact(['skos:relatedMatch', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:relatedMatch', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:related', X, Y],chk1,_), fact(['skos:relatedMatch', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:relatedMatch', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:relatedMatch', X, Y],chk1,_), fact(['skos:relatedMatch', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['skos:relatedMatch', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['skos:Concept', X],chk1,_), fact(['skos:semanticRelation', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['skos:semanticRelation', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['skos:Concept', Y],chk1,_), fact(['skos:semanticRelation', Anon0, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:semanticRelation', Anon0, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:inScheme', X, Y],chk1,_), fact(['skos:topConceptOf', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:topConceptOf', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['skos:Concept', X],chk1,_), fact(['skos:topConceptOf', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['skos:topConceptOf', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['skos:ConceptScheme', Y],chk1,_), fact(['skos:topConceptOf', Anon0, Y],O1,U1) ==> \+member(del,[O1]) | fact(['skos:topConceptOf', Anon0, Y],chk1,U1), applied_rules(1,bwd).

	
% turn facts without proof into del-facts
check_done \ fact(F,chk1,U) <=> fact(F,del,U).
check_done <=> true.


% -- repeat above steps iff new del-facts given --
fact(_,del,_) \ no_del <=> true.
phase(3), no_del  <=> phase(4). % move to insertion phase
phase(3) <=> phase(1).


% -- reset deletion phase --
phase(4) \ fact(F,prv,U) <=> fact(F,add,U).
phase(4) <=> true.


%-------------------------------------------------
% -- insertions --

% finish processing when every new fact has been inserted
update(add,[]) <=> phase(5), finish_update.
% insert every new fact
num_updates(U) \ update(add,[F|Fs]) <=>
	fact(F,add,U),
	update(add,Fs).
	
% -- compute new derivable facts	--
phase(5), fact(['skos:OrderedCollection', X],add,U1) ==> member(U,[U1]) | fact(['skos:Collection', X],add,U), applied_rules(1,ins).
phase(5), fact(['skos:broadMatch', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:broadMatch', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:narrowMatch', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowMatch', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:broadMatch', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:broader', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:broaderTransitive', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:broader', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:narrower', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:broaderTransitive', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:broaderTransitive', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:narrowerTransitive', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowerTransitive', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:broaderTransitive', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:broaderTransitive', X, Y],add,U1), fact(['skos:broaderTransitive', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['skos:broaderTransitive', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['skos:closeMatch', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:closeMatch', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:closeMatch', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:closeMatch', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:exactMatch', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:exactMatch', X, Y],add,U1), fact(['skos:exactMatch', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['skos:exactMatch', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:topConceptOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:hasTopConcept', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', X, _],add,U1) ==> member(U,[U1]) | fact(['skos:ConceptScheme', X],add,U), applied_rules(1,ins).
phase(5), fact(['skos:hasTopConcept', _, Y],add,U1) ==> member(U,[U1]) | fact(['skos:Concept', Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:inScheme', _, Y],add,U1) ==> member(U,[U1]) | fact(['skos:ConceptScheme', Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:mappingRelation', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:member', X, _],add,U1) ==> member(U,[U1]) | fact(['skos:Collection', X],add,U), applied_rules(1,ins).
phase(5), fact(['skos:memberList', X, Y],add,U1), fact(['skos:memberList', X, Z],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y, Z],add,U), applied_rules(1,ins).
phase(5), fact(['skos:memberList', X, _],add,U1) ==> member(U,[U1]) | fact(['skos:OrderedCollection', X],add,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowMatch', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowMatch', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:narrower', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:narrower', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:narrowerTransitive', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowerTransitive', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:narrowerTransitive', X, Y],add,U1), fact(['skos:narrowerTransitive', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['skos:narrowerTransitive', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['skos:related', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:semanticRelation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:related', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:related', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:relatedMatch', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:mappingRelation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:relatedMatch', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:related', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:relatedMatch', Y, X],add,U1) ==> member(U,[U1]) | fact(['skos:relatedMatch', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:semanticRelation', X, _],add,U1) ==> member(U,[U1]) | fact(['skos:Concept', X],add,U), applied_rules(1,ins).
phase(5), fact(['skos:semanticRelation', _, Y],add,U1) ==> member(U,[U1]) | fact(['skos:Concept', Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['skos:inScheme', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', X, _],add,U1) ==> member(U,[U1]) | fact(['skos:Concept', X],add,U), applied_rules(1,ins).
phase(5), fact(['skos:topConceptOf', _, Y],add,U1) ==> member(U,[U1]) | fact(['skos:ConceptScheme', Y],add,U), applied_rules(1,ins).

%----------------
% -- write materialization to stream --
finish_update, stream(S), num_updates(N) ==> writeln(S, materialization(N)). 	
finish_update, stream(S), fact(F,add,_) ==> writeln(S,F).	
finish_update, stream(S) ==> writeln(S,""), flush_output(S).

% collect numbers of applied rules
finish_update \ applied_rules(N,P), applied_rules_list(P,L) <=>
	append(L,[N],K),
	applied_rules_list(P,K).

% -- move on to next update --
finish_update, phase(5) <=> 
	applied_rules_init,
	read_stream(infinite).

% -- predicates for explicit facts --
explicit('skos:broader').
explicit('skos:member').
explicit('skos:memberList').
