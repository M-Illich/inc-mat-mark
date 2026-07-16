/*
Delete/Rederive (without Marking)
*/

:- use_module(library(chr)).
:- chr_constraint init/1, stream/1,
	read_stream/1, phase/1,
	available_input/1, extract_input/2,
	update/2, stream_end/0,
	fact/3, finish_update/0,
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
	applied_rules_list(red,[]),
	applied_rules_list(ins,[]).
	
% introduce counter for each type of rules
applied_rules_init <=>
	applied_rules(0,del),
	applied_rules(0,red),
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

% -- delete every fact that depends on a deleted fact --
phase(1), fact(['skos:OrderedCollection', X],O1,_) \ fact(['skos:Collection', X],add,U) <=> member(del,[O1]) | fact(['skos:Collection', X],del,U), applied_rules(1,del).
phase(1), fact(['skos:broadMatch', X, Y],O1,_) \ fact(['skos:mappingRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:broadMatch', Y, X],O1,_) \ fact(['skos:narrowMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrowMatch', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', Y, X],O1,_) \ fact(['skos:broadMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:broadMatch', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:broader', X, Y],O1,_) \ fact(['skos:broaderTransitive', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:broader', Y, X],O1,_) \ fact(['skos:narrower', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrower', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', X, Y],O1,_) \ fact(['skos:semanticRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', Y, X],O1,_) \ fact(['skos:narrowerTransitive', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', Y, X],O1,_) \ fact(['skos:broaderTransitive', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:broaderTransitive', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:broaderTransitive', X, Y],O1,_), fact(['skos:broaderTransitive', Y, Z],O2,_) \ fact(['skos:broaderTransitive', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['skos:broaderTransitive', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['skos:closeMatch', X, Y],O1,_) \ fact(['skos:mappingRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:closeMatch', Y, X],O1,_) \ fact(['skos:closeMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:closeMatch', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', X, Y],O1,_) \ fact(['skos:closeMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:closeMatch', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', Y, X],O1,_) \ fact(['skos:exactMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:exactMatch', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:exactMatch', X, Y],O1,_), fact(['skos:exactMatch', Y, Z],O2,_) \ fact(['skos:exactMatch', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['skos:exactMatch', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', Y, X],O1,_) \ fact(['skos:topConceptOf', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:topConceptOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', Y, X],O1,_) \ fact(['skos:hasTopConcept', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:hasTopConcept', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', X, _],O1,_) \ fact(['skos:ConceptScheme', X],add,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', X],del,U), applied_rules(1,del).
phase(1), fact(['skos:hasTopConcept', _, Y],O1,_) \ fact(['skos:Concept', Y],add,U) <=> member(del,[O1]) | fact(['skos:Concept', Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:inScheme', _, Y],O1,_) \ fact(['skos:ConceptScheme', Y],add,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:mappingRelation', X, Y],O1,_) \ fact(['skos:semanticRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:member', X, _],O1,_) \ fact(['skos:Collection', X],add,U) <=> member(del,[O1]) | fact(['skos:Collection', X],del,U), applied_rules(1,del).
phase(1), fact(['skos:memberList', X, Y],O1,_), fact(['skos:memberList', X, Z],O2,_) \ fact(['owl:sameAs', Y, Z],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y, Z],del,U), applied_rules(1,del).
phase(1), fact(['skos:memberList', X, _],O1,_) \ fact(['skos:OrderedCollection', X],add,U) <=> member(del,[O1]) | fact(['skos:OrderedCollection', X],del,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', X, Y],O1,_) \ fact(['skos:mappingRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:narrowMatch', X, Y],O1,_) \ fact(['skos:narrower', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrower', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:narrower', X, Y],O1,_) \ fact(['skos:narrowerTransitive', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:narrowerTransitive', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', X, Y],O1,_) \ fact(['skos:semanticRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:narrowerTransitive', X, Y],O1,_), fact(['skos:narrowerTransitive', Y, Z],O2,_) \ fact(['skos:narrowerTransitive', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['skos:narrowerTransitive', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['skos:related', X, Y],O1,_) \ fact(['skos:semanticRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:semanticRelation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:related', Y, X],O1,_) \ fact(['skos:related', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:related', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', X, Y],O1,_) \ fact(['skos:mappingRelation', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:mappingRelation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', X, Y],O1,_) \ fact(['skos:related', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:related', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:relatedMatch', Y, X],O1,_) \ fact(['skos:relatedMatch', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:relatedMatch', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:semanticRelation', X, _],O1,_) \ fact(['skos:Concept', X],add,U) <=> member(del,[O1]) | fact(['skos:Concept', X],del,U), applied_rules(1,del).
phase(1), fact(['skos:semanticRelation', _, Y],O1,_) \ fact(['skos:Concept', Y],add,U) <=> member(del,[O1]) | fact(['skos:Concept', Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', X, Y],O1,_) \ fact(['skos:inScheme', X, Y],add,U) <=> member(del,[O1]) | fact(['skos:inScheme', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', X, _],O1,_) \ fact(['skos:Concept', X],add,U) <=> member(del,[O1]) | fact(['skos:Concept', X],del,U), applied_rules(1,del).
phase(1), fact(['skos:topConceptOf', _, Y],O1,_) \ fact(['skos:ConceptScheme', Y],add,U) <=> member(del,[O1]) | fact(['skos:ConceptScheme', Y],del,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact(['skos:OrderedCollection', X],add,_) \ fact(['skos:Collection', X],del,U) <=> true | fact(['skos:Collection', X],add,U), applied_rules(1,red).
phase(2), fact(['skos:broadMatch', X, Y],add,_) \ fact(['skos:mappingRelation', X, Y],del,U) <=> true | fact(['skos:mappingRelation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:broadMatch', Y, X],add,_) \ fact(['skos:narrowMatch', X, Y],del,U) <=> true | fact(['skos:narrowMatch', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:narrowMatch', Y, X],add,_) \ fact(['skos:broadMatch', X, Y],del,U) <=> true | fact(['skos:broadMatch', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:broader', X, Y],add,_) \ fact(['skos:broaderTransitive', X, Y],del,U) <=> true | fact(['skos:broaderTransitive', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:broader', Y, X],add,_) \ fact(['skos:narrower', X, Y],del,U) <=> true | fact(['skos:narrower', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:broaderTransitive', X, Y],add,_) \ fact(['skos:semanticRelation', X, Y],del,U) <=> true | fact(['skos:semanticRelation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:broaderTransitive', Y, X],add,_) \ fact(['skos:narrowerTransitive', X, Y],del,U) <=> true | fact(['skos:narrowerTransitive', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:narrowerTransitive', Y, X],add,_) \ fact(['skos:broaderTransitive', X, Y],del,U) <=> true | fact(['skos:broaderTransitive', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:broaderTransitive', X, Y],add,_), fact(['skos:broaderTransitive', Y, Z],add,_) \ fact(['skos:broaderTransitive', X, Z],del,U) <=> true | fact(['skos:broaderTransitive', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['skos:closeMatch', X, Y],add,_) \ fact(['skos:mappingRelation', X, Y],del,U) <=> true | fact(['skos:mappingRelation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:closeMatch', Y, X],add,_) \ fact(['skos:closeMatch', X, Y],del,U) <=> true | fact(['skos:closeMatch', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:exactMatch', X, Y],add,_) \ fact(['skos:closeMatch', X, Y],del,U) <=> true | fact(['skos:closeMatch', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:exactMatch', Y, X],add,_) \ fact(['skos:exactMatch', X, Y],del,U) <=> true | fact(['skos:exactMatch', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:exactMatch', X, Y],add,_), fact(['skos:exactMatch', Y, Z],add,_) \ fact(['skos:exactMatch', X, Z],del,U) <=> true | fact(['skos:exactMatch', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['skos:hasTopConcept', Y, X],add,_) \ fact(['skos:topConceptOf', X, Y],del,U) <=> true | fact(['skos:topConceptOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:topConceptOf', Y, X],add,_) \ fact(['skos:hasTopConcept', X, Y],del,U) <=> true | fact(['skos:hasTopConcept', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:hasTopConcept', X, _],add,_) \ fact(['skos:ConceptScheme', X],del,U) <=> true | fact(['skos:ConceptScheme', X],add,U), applied_rules(1,red).
phase(2), fact(['skos:hasTopConcept', _, Y],add,_) \ fact(['skos:Concept', Y],del,U) <=> true | fact(['skos:Concept', Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:inScheme', _, Y],add,_) \ fact(['skos:ConceptScheme', Y],del,U) <=> true | fact(['skos:ConceptScheme', Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:mappingRelation', X, Y],add,_) \ fact(['skos:semanticRelation', X, Y],del,U) <=> true | fact(['skos:semanticRelation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:member', X, _],add,_) \ fact(['skos:Collection', X],del,U) <=> true | fact(['skos:Collection', X],add,U), applied_rules(1,red).
phase(2), fact(['skos:memberList', X, Y],add,_), fact(['skos:memberList', X, Z],add,_) \ fact(['owl:sameAs', Y, Z],del,U) <=> true | fact(['owl:sameAs', Y, Z],add,U), applied_rules(1,red).
phase(2), fact(['skos:memberList', X, _],add,_) \ fact(['skos:OrderedCollection', X],del,U) <=> true | fact(['skos:OrderedCollection', X],add,U), applied_rules(1,red).
phase(2), fact(['skos:narrowMatch', X, Y],add,_) \ fact(['skos:mappingRelation', X, Y],del,U) <=> true | fact(['skos:mappingRelation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:narrowMatch', X, Y],add,_) \ fact(['skos:narrower', X, Y],del,U) <=> true | fact(['skos:narrower', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:narrower', X, Y],add,_) \ fact(['skos:narrowerTransitive', X, Y],del,U) <=> true | fact(['skos:narrowerTransitive', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:narrowerTransitive', X, Y],add,_) \ fact(['skos:semanticRelation', X, Y],del,U) <=> true | fact(['skos:semanticRelation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:narrowerTransitive', X, Y],add,_), fact(['skos:narrowerTransitive', Y, Z],add,_) \ fact(['skos:narrowerTransitive', X, Z],del,U) <=> true | fact(['skos:narrowerTransitive', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['skos:related', X, Y],add,_) \ fact(['skos:semanticRelation', X, Y],del,U) <=> true | fact(['skos:semanticRelation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:related', Y, X],add,_) \ fact(['skos:related', X, Y],del,U) <=> true | fact(['skos:related', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:relatedMatch', X, Y],add,_) \ fact(['skos:mappingRelation', X, Y],del,U) <=> true | fact(['skos:mappingRelation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:relatedMatch', X, Y],add,_) \ fact(['skos:related', X, Y],del,U) <=> true | fact(['skos:related', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:relatedMatch', Y, X],add,_) \ fact(['skos:relatedMatch', X, Y],del,U) <=> true | fact(['skos:relatedMatch', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:semanticRelation', X, _],add,_) \ fact(['skos:Concept', X],del,U) <=> true | fact(['skos:Concept', X],add,U), applied_rules(1,red).
phase(2), fact(['skos:semanticRelation', _, Y],add,_) \ fact(['skos:Concept', Y],del,U) <=> true | fact(['skos:Concept', Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:topConceptOf', X, Y],add,_) \ fact(['skos:inScheme', X, Y],del,U) <=> true | fact(['skos:inScheme', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['skos:topConceptOf', X, _],add,_) \ fact(['skos:Concept', X],del,U) <=> true | fact(['skos:Concept', X],add,U), applied_rules(1,red).
phase(2), fact(['skos:topConceptOf', _, Y],add,_) \ fact(['skos:ConceptScheme', Y],del,U) <=> true | fact(['skos:ConceptScheme', Y],add,U), applied_rules(1,red).

phase(2) <=> phase(3).


% -- remove facts that cannot be rederived --
phase(3) \ fact(_,del,_) <=> true.
phase(3) <=> true.


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
finish_update, stream(S), num_updates(N) ==> writeln(S,materialization(N)). 	
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
