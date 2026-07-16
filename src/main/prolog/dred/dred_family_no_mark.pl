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
phase(1), fact(['p:hasParent', X, Y],O1,_), fact(['p:maleInFamilinx', Y],O2,_) \ fact(['p:hasFather', X, Y],add,U) <=> member(del,[O1,O2]) | fact(['p:hasFather', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, Y],O1,_), fact(['p:femaleInFamilinx', Y],O2,_) \ fact(['p:hasMother', X, Y],add,U) <=> member(del,[O1,O2]) | fact(['p:hasMother', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', X, Y],O1,_) \ fact(['p:hasChild', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isWifeOf', X0, X1],O1,_), fact(['p:brotherOf', X1, X2],O2,_), fact(['p:isParentOf', X2, X3],O3,_) \ fact(['p:isAuntInLawOf', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:isAuntInLawOf', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', X, Y],O1,_) \ fact(['p:hasChild', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', Y, X],O1,_) \ fact(['p:hasGreatUncle', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGreatUncle', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', Y, X],O1,_) \ fact(['p:isGreatUncleOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isGreatUncleOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X0, X1],O1,_), fact(['p:isSiblingOf', X1, X2],O2,_), fact(['p:grandParentOf', X2, X3],O3,_) \ fact(['p:isSecondCousinOf', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:isSecondCousinOf', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', X, Y],O1,_) \ fact(['p:hasGrandParent', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:alsoKnownAs', X, Y],O1,_) \ fact(['p:knownAs', X, Y],add,U) <=> member(del,[O1]) | fact(['p:knownAs', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', Y, X],O1,_) \ fact(['p:directSiblingOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasBirthYear', X, Y1],O1,_), fact(['p:hasBirthYear', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', X, Y],O1,_) \ fact(['p:isRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isChildOf', Y, X],O1,_) \ fact(['p:hasChild', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', Y, X],O1,_) \ fact(['p:isChildOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isChildOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParentInLaw', Y, X],O1,_) \ fact(['p:isParentInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isParentInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', Y, X],O1,_) \ fact(['p:hasParentInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', X, Y],O1,_), fact(['p:isForefatherOf', Y, Z],O2,_) \ fact(['p:isForefatherOf', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['p:isForefatherOf', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasDeathYear', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', X, Y],O1,_) \ fact(['p:hasParentInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', X, Y],O1,_) \ fact(['p:isInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,_), fact(['p:hasFather', X1, X2],O2,_) \ fact(['p:hasFatherInLaw', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:hasFatherInLaw', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, Y],O1,_) \ fact(['p:hasAncestor', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, Y1],O1,_), fact(['p:hasMother', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAuntInLaw', Y, X],O1,_) \ fact(['p:hasAuntInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAuntInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAuntInLaw', Y, X],O1,_) \ fact(['p:hasAuntInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAuntInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Grandparent', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isParentOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_) \ fact(['p:Grandparent', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Grandparent', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', X, _],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:alsoKnownAs', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:GreatUncle', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:brotherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_), fact(['p:isParentOf', X2, X3],O6,_), fact(['p:Person', X3],O7,_) \ fact(['p:GreatUncle', X],add,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:GreatUncle', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', X, _],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,_) \ fact(['p:DomainEntity', X],add,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X0, X1],O1,_), fact(['p:isParentOf', X1, X2],O2,_) \ fact(['p:isUncleOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isUncleOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', _, X1],O1,_) \ fact(['p:Marriage', X1],add,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandmotherOf', Y, X],O1,_) \ fact(['p:hasGreatGrandmother', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandmother', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', Y, X],O1,_) \ fact(['p:isGreatGrandmotherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isGreatGrandmotherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasBirthYear', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:MotherInLaw', X],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_), fact(['p:isMotherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isSpouseOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_) \ fact(['p:MotherInLaw', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:MotherInLaw', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMalePartner', Y, X],O1,_) \ fact(['p:isMalePartnerIn', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isMalePartnerIn', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', Y, X],O1,_) \ fact(['p:hasMalePartner', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasMalePartner', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X, _],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', X, Y],O1,_) \ fact(['p:isAncestorOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Grandfather', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isFatherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_) \ fact(['p:Grandfather', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Grandfather', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Female', X],O1,_) \ fact(['p:Sex', X],add,U) <=> member(del,[O1]) | fact(['p:Sex', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:Uncle', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:brotherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_) \ fact(['p:Uncle', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Uncle', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', X, Y],O1,_), fact(['p:isRelationOf', Y, Z],O2,_) \ fact(['p:isRelationOf', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['p:isRelationOf', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X, _],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasSister', Y, X],O1,_) \ fact(['p:sisterOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:sisterOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', Y, X],O1,_) \ fact(['p:hasSister', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasSister', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', _, X1],O1,_) \ fact(['p:Sex', X1],add,U) <=> member(del,[O1]) | fact(['p:Sex', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isDaughterOf', Y, X],O1,_) \ fact(['p:hasDaughter', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasDaughter', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', Y, X],O1,_) \ fact(['p:isDaughterOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isDaughterOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isSonOf', Y, X],O1,_) \ fact(['p:hasSon', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasSon', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', Y, X],O1,_) \ fact(['p:isSonOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSonOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Sex', X],O1,_) \ fact(['p:DomainEntity', X],add,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isHusbandOf', Y, X],O1,_) \ fact(['p:hasHusband', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasHusband', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', Y, X],O1,_) \ fact(['p:isHusbandOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isHusbandOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', X, Y],O1,_) \ fact(['p:isInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isParentOf', X0, X1],O1,_), fact(['p:isSpouseOf', X1, X2],O2,_) \ fact(['p:isParentInLawOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isParentInLawOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', X, _],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X0, X1],O1,_), fact(['p:hasBrother', X1, X2],O2,_) \ fact(['p:isBrotherInLawOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isBrotherInLawOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:BloodRelation', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isBloodRelationOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:BloodRelation', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:BloodRelation', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,_), fact(['p:Sex', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isParentOf', X, Y],O1,_) \ fact(['p:hasChild', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', X, Y],O1,_) \ fact(['p:isParentOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isParentOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X, Y],O1,_) \ fact(['p:directSiblingOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', X, Y],O1,_) \ fact(['p:hasGrandParent', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, Y],O1,_) \ fact(['p:hasForeMother', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasForeMother', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_), fact(['p:hasMother', X1, X2],O2,_) \ fact(['p:hasGrandmother', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:hasGrandmother', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X0, X1],O1,_), fact(['p:hasBrother', X1, X2],O2,_) \ fact(['p:isSisterInLawOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isSisterInLawOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:Wife', X],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_), fact(['p:isFemalePartnerIn', X, X1],O2,_), fact(['p:Marriage', X1],O3,_), fact(['p:hasMalePartner', X1, X2],O4,_), fact(['p:Man', X2],O5,_) \ fact(['p:Wife', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Wife', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasDeathYear', X, Y1],O1,_), fact(['p:hasDeathYear', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['p:hasPartner', Y, X],O1,_) \ fact(['p:isPartnerIn', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', Y, X],O1,_) \ fact(['p:hasPartner', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasPartner', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X, Y],O1,_) \ fact(['p:directSiblingOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', Y, X],O1,_) \ fact(['p:hasForeFather', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasForeFather', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', Y, X],O1,_) \ fact(['p:isForefatherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isForefatherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isFatherOf', Y, X],O1,_) \ fact(['p:hasFather', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasFather', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', Y, X],O1,_) \ fact(['p:isFatherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isFatherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isHusbandOf', X0, X1],O1,_), fact(['p:sisterOf', X1, X2],O2,_), fact(['p:isParentOf', X2, X3],O3,_) \ fact(['p:isUncleInLawOf', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:isUncleInLawOf', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:ThirdCousin', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:hasParent', X, X1],O2,_), fact(['p:hasParent', X1, X2],O3,_), fact(['p:Person', X2],O4,_), fact(['p:hasParent', X2, X3],O5,_), fact(['p:Person', X3],O6,_), fact(['p:isSiblingOf', X3, X4],O7,_), fact(['p:Person', X4],O8,_), fact(['p:isParentOf', X4, X5],O9,_), fact(['p:Person', X5],O10,_), fact(['p:isParentOf', X5, X6],O11,_), fact(['p:Person', X6],O12,_), fact(['p:isParentOf', X6, X7],O13,_), fact(['p:Person', X7],O14,_) \ fact(['p:ThirdCousin', X],add,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14]) | fact(['p:ThirdCousin', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:hasGender', X, X1],O2,_), fact(['p:Female', X1],O3,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_), fact(['p:isSiblingOf', X1, X2],O2,_), fact(['p:isParentOf', X2, X3],O3,_) \ fact(['p:isFirstCousinOf', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:isFirstCousinOf', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, Y],O1,_) \ fact(['p:hasAncestor', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', Y, X],O1,_) \ fact(['p:isSpouseOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X0, X1],O1,_), fact(['p:isParentOf', X1, X2],O2,_) \ fact(['p:isAuntOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isAuntOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X, Y],O1,_) \ fact(['p:hasAncestor', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', X, Y],O1,_) \ fact(['p:isSiblingInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', Y, X],O1,_) \ fact(['p:hasGreatAunt', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGreatAunt', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', Y, X],O1,_) \ fact(['p:isGreatAuntOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isGreatAuntOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Spouse', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isSpouseOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Spouse', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Spouse', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', _, X1],O1,_) \ fact(['p:Marriage', X1],add,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:Mother', X],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_), fact(['p:isMotherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Mother', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Mother', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:FirstCousin', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:hasParent', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isSiblingOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_), fact(['p:isParentOf', X2, X3],O6,_), fact(['p:Person', X3],O7,_) \ fact(['p:FirstCousin', X],add,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:FirstCousin', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isMotherInLawOf', Y, X],O1,_) \ fact(['p:hasMotherInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasMotherInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', Y, X],O1,_) \ fact(['p:isMotherInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isMotherInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFamilyName', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_), fact(['p:hasFather', X1, X2],O2,_) \ fact(['p:hasGrandfather', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:hasGrandfather', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:Son', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isSonOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Son', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Son', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X0, X1],O1,_), fact(['p:isSiblingOf', X1, X2],O2,_), fact(['p:isGreatGrandParentOf', X2, X3],O3,_) \ fact(['p:isThirdCousinOf', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:isThirdCousinOf', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['p:isGrandfatherOf', Y, X],O1,_) \ fact(['p:hasGrandfather', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGrandfather', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', Y, X],O1,_) \ fact(['p:isGrandfatherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isGrandfatherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X, Y],O1,_) \ fact(['p:isSpouseOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Daughter', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isDaughterOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Daughter', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Daughter', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', X, Y],O1,_) \ fact(['p:hasParentInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:MaleAncestor', X],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_), fact(['p:isAncestorOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:MaleAncestor', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:MaleAncestor', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isFatherInLawOf', Y, X],O1,_) \ fact(['p:hasFatherInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasFatherInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', Y, X],O1,_) \ fact(['p:isFatherInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isFatherInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, Y1],O1,_), fact(['p:hasFather', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X, Y],O1,_) \ fact(['p:isInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', Y, X],O1,_) \ fact(['p:brotherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:brotherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', Y, X],O1,_) \ fact(['p:hasBrother', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasBrother', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X, _],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Parent', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isParentOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Parent', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Parent', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X, _],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', X, _],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', X, _],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Forefather', X],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_), fact(['p:isForefatherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Forefather', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Forefather', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', X, _],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:SecondCousin', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:hasParent', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:hasParent', X1, X2],O4,_), fact(['p:Person', X2],O5,_), fact(['p:isSiblingOf', X2, X3],O6,_), fact(['p:Person', X3],O7,_), fact(['p:isParentOf', X3, X4],O8,_), fact(['p:Person', X4],O9,_), fact(['p:isParentOf', X4, X5],O10,_), fact(['p:Person', X5],O11,_) \ fact(['p:SecondCousin', X],add,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11]) | fact(['p:SecondCousin', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', Y, X],O1,_) \ fact(['p:isRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', Y, X],O1,_) \ fact(['p:isSecondCousinOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSecondCousinOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isGrandmotherOf', Y, X],O1,_) \ fact(['p:hasGrandmother', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGrandmother', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', Y, X],O1,_) \ fact(['p:isGrandmotherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isGrandmotherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', X, Y],O1,_) \ fact(['p:isInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Ancestor', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isAncestorOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Ancestor', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Ancestor', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', Y, X],O1,_) \ fact(['p:isSiblingOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSiblingOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', X, Y],O1,_) \ fact(['p:isAncestorOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', X, Y],O1,_), fact(['p:isForemotherOf', Y, Z],O2,_) \ fact(['p:isForemotherOf', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['p:isForemotherOf', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, Y],O1,_), fact(['p:hasForeFather', Y, Z],O2,_) \ fact(['p:hasForeFather', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['p:hasForeFather', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', X, Y],O1,_) \ fact(['p:isSpouseOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:knownAs', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X0, X1],O1,_), fact(['p:hasFemalePartner', X1, X2],O2,_) \ fact(['p:hasWife', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:hasWife', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X0, X1],O1,_), fact(['p:hasMalePartner', X1, X2],O2,_) \ fact(['p:hasHusband', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:hasHusband', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', X, Y],O1,_) \ fact(['p:isSiblingOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSiblingOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', Y, X],O1,_) \ fact(['p:isParentOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isParentOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:ParentInLaw', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isParentOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isSpouseOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_) \ fact(['p:ParentInLaw', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:ParentInLaw', X],del,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:formerlyKnownAs', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, Y],O1,_) \ fact(['p:hasAncestor', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Cousin', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:hasAncestor', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isSiblingOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_), fact(['p:isParentOf', X2, X3],O6,_), fact(['p:Person', X3],O7,_) \ fact(['p:Cousin', X],add,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:Cousin', X],del,U), applied_rules(1,del).
phase(1), fact(['p:GreatGrandparent', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isParentOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_), fact(['p:isParentOf', X2, X3],O6,_), fact(['p:Person', X3],O7,_) \ fact(['p:GreatGrandparent', X],add,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:GreatGrandparent', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', Y, X],O1,_) \ fact(['p:hasUncle', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasUncle', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', Y, X],O1,_) \ fact(['p:isUncleOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isUncleOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', X, _],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:formerlyKnownAs', X, Y],O1,_) \ fact(['p:knownAs', X, Y],add,U) <=> member(del,[O1]) | fact(['p:knownAs', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', Y, X],O1,_) \ fact(['p:isFirstCousinOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isFirstCousinOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, Y],O1,_), fact(['p:hasForeMother', Y, Z],O2,_) \ fact(['p:hasForeMother', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['p:hasForeMother', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', Y, X],O1,_) \ fact(['p:hasAunt', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAunt', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', Y, X],O1,_) \ fact(['p:isAuntOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isAuntOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', X, _],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, Y],O1,_) \ fact(['p:hasForeFather', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasForeFather', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_) \ fact(['p:DomainEntity', X],add,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:FemaleDescendent', X],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_), fact(['p:hasAncestor', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:FemaleDescendent', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:FemaleDescendent', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasUncleInLaw', Y, X],O1,_) \ fact(['p:isUncleInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isUncleInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', Y, X],O1,_) \ fact(['p:hasUncleInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasUncleInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:FemaleAncestor', X],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_), fact(['p:isAncestorOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:FemaleAncestor', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:FemaleAncestor', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', _, X1],O1,_) \ fact(['p:Marriage', X1],add,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', X, Y1],O1,_), fact(['p:hasGender', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, Y],O1,_), fact(['p:hasAncestor', Y, Z],O2,_) \ fact(['p:hasAncestor', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['p:hasAncestor', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['p:Foremother', X],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_), fact(['p:isForemotherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Foremother', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Foremother', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', Y, X],O1,_) \ fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', Y, X],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isAncestorOf', Y, X],O1,_) \ fact(['p:hasAncestor', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', Y, X],O1,_) \ fact(['p:isAncestorOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X, Y],O1,_) \ fact(['p:hasAncestor', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X0, X1],O1,_), fact(['p:grandParentOf', X1, X2],O2,_) \ fact(['p:isGreatUncleOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isGreatUncleOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_), fact(['p:hasGrandfather', X1, X2],O2,_) \ fact(['p:hasGreatGrandfather', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:hasGreatGrandfather', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:Male', X],O1,_) \ fact(['p:Sex', X],add,U) <=> member(del,[O1]) | fact(['p:Sex', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:Female', X],O1,_), fact(['p:Male', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:Sex', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasBrotherInLaw', Y, X],O1,_) \ fact(['p:isSisterInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSisterInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', Y, X],O1,_) \ fact(['p:hasBrotherInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasBrotherInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,_), fact(['p:isSiblingOf', X1, X2],O2,_) \ fact(['p:isSiblingInLawOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isSiblingInLawOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:hasGender', X, X1],O2,_), fact(['p:Male', X1],O3,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandParentOf', Y, X],O1,_) \ fact(['p:hasGreatGrandParent', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', Y, X],O1,_) \ fact(['p:isGreatGrandParentOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isGreatGrandParentOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', X, _],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Father', X],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_), fact(['p:isFatherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Father', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Father', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:marriageYear', X, _],O1,_) \ fact(['p:Marriage', X],add,U) <=> member(del,[O1]) | fact(['p:Marriage', X],del,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X, _],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X0, X1],O1,_), fact(['p:isParentOf', X1, X2],O2,_) \ fact(['p:isFirstCousinOnceRemovedOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isFirstCousinOnceRemovedOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:FatherInLaw', X],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_), fact(['p:isFatherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isSpouseOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_) \ fact(['p:FatherInLaw', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:FatherInLaw', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandfatherOf', Y, X],O1,_) \ fact(['p:hasGreatGrandfather', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandfather', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', Y, X],O1,_) \ fact(['p:isGreatGrandfatherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isGreatGrandfatherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, Y],O1,_), fact(['p:isBloodRelationOf', Y, Z],O2,_) \ fact(['p:isBloodRelationOf', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['p:isBloodRelationOf', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['p:GreatGrandfather', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isFatherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_), fact(['p:isParentOf', X2, X3],O6,_), fact(['p:Person', X3],O7,_) \ fact(['p:GreatGrandfather', X],add,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:GreatGrandfather', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X, Y],O1,_) \ fact(['p:isPartnerIn', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', X, Y],O1,_) \ fact(['p:hasGreatGrandParent', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasBrotherInLaw', Y, X],O1,_) \ fact(['p:isBrotherInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBrotherInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', Y, X],O1,_) \ fact(['p:hasBrotherInLaw', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasBrotherInLaw', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Grandmother', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isMotherOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_) \ fact(['p:Grandmother', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Grandmother', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,_), fact(['p:hasMother', X1, X2],O2,_) \ fact(['p:hasMotherInLaw', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:hasMotherInLaw', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:Husband', X],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_), fact(['p:isMalePartnerIn', X, X1],O2,_), fact(['p:Marriage', X1],O3,_), fact(['p:hasFemalePartner', X1, X2],O4,_), fact(['p:Woman', X2],O5,_) \ fact(['p:Husband', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Husband', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFemalePartner', Y, X],O1,_) \ fact(['p:isFemalePartnerIn', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isFemalePartnerIn', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', Y, X],O1,_) \ fact(['p:hasFemalePartner', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasFemalePartner', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:InLaw', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isInLawOf', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:InLaw', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:InLaw', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', Y, X],O1,_) \ fact(['p:isSiblingInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Descendent', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:hasAncestor', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:Descendent', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:Descendent', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', X, Y],O1,_) \ fact(['p:isInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,_), fact(['p:Person', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', X, Y],O1,_) \ fact(['p:isBloodRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, Y],O1,_) \ fact(['p:isRelationOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:PersonWithManySibling', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', _, X1],O1,_) \ fact(['p:Man', X1],add,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:grandParentOf', Y, X],O1,_) \ fact(['p:hasGrandParent', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', Y, X],O1,_) \ fact(['p:grandParentOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:grandParentOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:MaleDescendent', X],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_), fact(['p:hasAncestor', X, X1],O2,_), fact(['p:Person', X1],O3,_) \ fact(['p:MaleDescendent', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['p:MaleDescendent', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isSonOf', X0, X1],O1,_), fact(['p:isSiblingOf', X1, X2],O2,_) \ fact(['p:isNephewOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isNephewOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', Y, X],O1,_) \ fact(['p:isInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_), fact(['p:hasGrandmother', X1, X2],O2,_) \ fact(['p:hasGreatGrandmother', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:hasGreatGrandmother', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', Y, X],O1,_) \ fact(['p:hasForeMother', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasForeMother', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', Y, X],O1,_) \ fact(['p:isForemotherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isForemotherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', _, X1],O1,_) \ fact(['p:Woman', X1],add,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', X, Y],O1,_) \ fact(['p:isSiblingInLawOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:ParentOfSmallFamily', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:ParentOfLargeFamily', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Aunt', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:sisterOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_) \ fact(['p:Aunt', X],add,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Aunt', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isMotherOf', Y, X],O1,_) \ fact(['p:hasMother', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasMother', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', Y, X],O1,_) \ fact(['p:isMotherOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isMotherOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', Y, X],O1,_) \ fact(['p:isThirdCousinOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isThirdCousinOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isWifeOf', Y, X],O1,_) \ fact(['p:hasWife', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasWife', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', Y, X],O1,_) \ fact(['p:isWifeOf', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isWifeOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', X, _],O1,_) \ fact(['p:Woman', X],add,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', X, _],O1,_) \ fact(['p:Man', X],add,U) <=> member(del,[O1]) | fact(['p:Man', X],del,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X, Y],O1,_) \ fact(['p:isPartnerIn', X, Y],add,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:isDaughterOf', X0, X1],O1,_), fact(['p:isSiblingOf', X1, X2],O2,_) \ fact(['p:isNieceOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isNieceOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X0, X1],O1,_), fact(['p:grandParentOf', X1, X2],O2,_) \ fact(['p:isGreatAuntOf', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['p:isGreatAuntOf', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', _, X1],O1,_) \ fact(['p:Person', X1],add,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:GreatGreatGrandparent', X],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_), fact(['p:isParentOf', X, X1],O2,_), fact(['p:Person', X1],O3,_), fact(['p:isParentOf', X1, X2],O4,_), fact(['p:Person', X2],O5,_), fact(['p:isParentOf', X2, X3],O6,_), fact(['p:Person', X3],O7,_), fact(['p:isParentOf', X3, X4],O8,_), fact(['p:Person', X4],O9,_) \ fact(['p:GreatGreatGrandparent', X],add,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9]) | fact(['p:GreatGreatGrandparent', X],del,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', X, Y],O1,_) \ fact(['p:hasGreatGrandParent', X, Y],add,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, Y],O1,_), fact(['p:isSiblingOf', Y, Z],O2,_) \ fact(['p:isSiblingOf', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['p:isSiblingOf', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', X, _],O1,_) \ fact(['p:Person', X],add,U) <=> member(del,[O1]) | fact(['p:Person', X],del,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact(['p:hasParent', X, Y],add,_), fact(['p:maleInFamilinx', Y],add,_) \ fact(['p:hasFather', X, Y],del,U) <=> true | fact(['p:hasFather', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X, Y],add,_), fact(['p:femaleInFamilinx', Y],add,_) \ fact(['p:hasMother', X, Y],del,U) <=> true | fact(['p:hasMother', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasSon', X, Y],add,_) \ fact(['p:hasChild', X, Y],del,U) <=> true | fact(['p:hasChild', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isWifeOf', X0, X1],add,_), fact(['p:brotherOf', X1, X2],add,_), fact(['p:isParentOf', X2, X3],add,_) \ fact(['p:isAuntInLawOf', X0, X3],del,U) <=> true | fact(['p:isAuntInLawOf', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['p:hasDaughter', X, Y],add,_) \ fact(['p:hasChild', X, Y],del,U) <=> true | fact(['p:hasChild', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatUncleOf', Y, X],add,_) \ fact(['p:hasGreatUncle', X, Y],del,U) <=> true | fact(['p:hasGreatUncle', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatUncle', Y, X],add,_) \ fact(['p:isGreatUncleOf', X, Y],del,U) <=> true | fact(['p:isGreatUncleOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', X0, X1],add,_), fact(['p:isSiblingOf', X1, X2],add,_), fact(['p:grandParentOf', X2, X3],add,_) \ fact(['p:isSecondCousinOf', X0, X3],del,U) <=> true | fact(['p:isSecondCousinOf', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandmother', X, Y],add,_) \ fact(['p:hasGrandParent', X, Y],del,U) <=> true | fact(['p:hasGrandParent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:alsoKnownAs', X, Y],add,_) \ fact(['p:knownAs', X, Y],del,U) <=> true | fact(['p:knownAs', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:directSiblingOf', Y, X],add,_) \ fact(['p:directSiblingOf', X, Y],del,U) <=> true | fact(['p:directSiblingOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasBirthYear', X, Y1],add,_), fact(['p:hasBirthYear', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['p:hasHusband', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isInLawOf', X, Y],add,_) \ fact(['p:isRelationOf', X, Y],del,U) <=> true | fact(['p:isRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isChildOf', Y, X],add,_) \ fact(['p:hasChild', X, Y],del,U) <=> true | fact(['p:hasChild', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasChild', Y, X],add,_) \ fact(['p:isChildOf', X, Y],del,U) <=> true | fact(['p:isChildOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParentInLaw', Y, X],add,_) \ fact(['p:isParentInLawOf', X, Y],del,U) <=> true | fact(['p:isParentInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isParentInLawOf', Y, X],add,_) \ fact(['p:hasParentInLaw', X, Y],del,U) <=> true | fact(['p:hasParentInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isForefatherOf', X, Y],add,_), fact(['p:isForefatherOf', Y, Z],add,_) \ fact(['p:isForefatherOf', X, Z],del,U) <=> true | fact(['p:isForefatherOf', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAunt', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatUncle', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasDeathYear', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMotherInLaw', X, Y],add,_) \ fact(['p:hasParentInLaw', X, Y],del,U) <=> true | fact(['p:hasParentInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isAuntInLawOf', X, Y],add,_) \ fact(['p:isInLawOf', X, Y],del,U) <=> true | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X0, X1],add,_), fact(['p:hasFather', X1, X2],add,_) \ fact(['p:hasFatherInLaw', X0, X2],del,U) <=> true | fact(['p:hasFatherInLaw', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', X, Y],add,_) \ fact(['p:hasAncestor', X, Y],del,U) <=> true | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', X, Y1],add,_), fact(['p:hasMother', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAuntInLaw', Y, X],add,_) \ fact(['p:hasAuntInLaw', X, Y],del,U) <=> true | fact(['p:hasAuntInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAuntInLaw', Y, X],add,_) \ fact(['p:hasAuntInLaw', X, Y],del,U) <=> true | fact(['p:hasAuntInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Grandparent', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isParentOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_) \ fact(['p:Grandparent', X],del,U) <=> true | fact(['p:Grandparent', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isAuntInLawOf', X, _],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasUncle', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:alsoKnownAs', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:GreatUncle', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:brotherOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_), fact(['p:isParentOf', X2, X3],add,_), fact(['p:Person', X3],add,_) \ fact(['p:GreatUncle', X],del,U) <=> true | fact(['p:GreatUncle', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOnceRemovedOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isAuntOf', X, _],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasSon', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Marriage', X],add,_) \ fact(['p:DomainEntity', X],del,U) <=> true | fact(['p:DomainEntity', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAunt', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', X0, X1],add,_), fact(['p:isParentOf', X1, X2],add,_) \ fact(['p:isUncleOf', X0, X2],del,U) <=> true | fact(['p:isUncleOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:isPartnerIn', _, X1],add,_) \ fact(['p:Marriage', X1],del,U) <=> true | fact(['p:Marriage', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatGrandmotherOf', Y, X],add,_) \ fact(['p:hasGreatGrandmother', X, Y],del,U) <=> true | fact(['p:hasGreatGrandmother', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandmother', Y, X],add,_) \ fact(['p:isGreatGrandmotherOf', X, Y],del,U) <=> true | fact(['p:isGreatGrandmotherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasBirthYear', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:MotherInLaw', X],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,_), fact(['p:isMotherOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isSpouseOf', X1, X2],add,_), fact(['p:Person', X2],add,_) \ fact(['p:MotherInLaw', X],del,U) <=> true | fact(['p:MotherInLaw', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMalePartner', Y, X],add,_) \ fact(['p:isMalePartnerIn', X, Y],del,U) <=> true | fact(['p:isMalePartnerIn', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', Y, X],add,_) \ fact(['p:hasMalePartner', X, Y],del,U) <=> true | fact(['p:hasMalePartner', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', X, _],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isForefatherOf', X, Y],add,_) \ fact(['p:isAncestorOf', X, Y],del,U) <=> true | fact(['p:isAncestorOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Grandfather', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isFatherOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_) \ fact(['p:Grandfather', X],del,U) <=> true | fact(['p:Grandfather', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Female', X],add,_) \ fact(['p:Sex', X],del,U) <=> true | fact(['p:Sex', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:Uncle', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:brotherOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_) \ fact(['p:Uncle', X],del,U) <=> true | fact(['p:Uncle', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isNephewOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isRelationOf', X, Y],add,_), fact(['p:isRelationOf', Y, Z],add,_) \ fact(['p:isRelationOf', X, Z],del,U) <=> true | fact(['p:isRelationOf', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandmother', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isRelationOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', X, _],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasSister', Y, X],add,_) \ fact(['p:sisterOf', X, Y],del,U) <=> true | fact(['p:sisterOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', Y, X],add,_) \ fact(['p:hasSister', X, Y],del,U) <=> true | fact(['p:hasSister', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:directSiblingOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isThirdCousinOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGender', _, X1],add,_) \ fact(['p:Sex', X1],del,U) <=> true | fact(['p:Sex', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isDaughterOf', Y, X],add,_) \ fact(['p:hasDaughter', X, Y],del,U) <=> true | fact(['p:hasDaughter', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasDaughter', Y, X],add,_) \ fact(['p:isDaughterOf', X, Y],del,U) <=> true | fact(['p:isDaughterOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandfather', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingInLawOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isSonOf', Y, X],add,_) \ fact(['p:hasSon', X, Y],del,U) <=> true | fact(['p:hasSon', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasSon', Y, X],add,_) \ fact(['p:isSonOf', X, Y],del,U) <=> true | fact(['p:isSonOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Sex', X],add,_) \ fact(['p:DomainEntity', X],del,U) <=> true | fact(['p:DomainEntity', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isHusbandOf', Y, X],add,_) \ fact(['p:hasHusband', X, Y],del,U) <=> true | fact(['p:hasHusband', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasHusband', Y, X],add,_) \ fact(['p:isHusbandOf', X, Y],del,U) <=> true | fact(['p:isHusbandOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isUncleInLawOf', X, Y],add,_) \ fact(['p:isInLawOf', X, Y],del,U) <=> true | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isParentOf', X0, X1],add,_), fact(['p:isSpouseOf', X1, X2],add,_) \ fact(['p:isParentInLawOf', X0, X2],del,U) <=> true | fact(['p:isParentInLawOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:isBrotherInLawOf', X, _],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', X0, X1],add,_), fact(['p:hasBrother', X1, X2],add,_) \ fact(['p:isBrotherInLawOf', X0, X2],del,U) <=> true | fact(['p:isBrotherInLawOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:BloodRelation', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isBloodRelationOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:BloodRelation', X],del,U) <=> true | fact(['p:BloodRelation', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Marriage', X],add,_), fact(['p:Sex', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFatherInLaw', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isParentOf', X, Y],add,_) \ fact(['p:hasChild', X, Y],del,U) <=> true | fact(['p:hasChild', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasChild', X, Y],add,_) \ fact(['p:isParentOf', X, Y],del,U) <=> true | fact(['p:isParentOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', X, Y],add,_) \ fact(['p:directSiblingOf', X, Y],del,U) <=> true | fact(['p:directSiblingOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandfather', X, Y],add,_) \ fact(['p:hasGrandParent', X, Y],del,U) <=> true | fact(['p:hasGrandParent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasUncle', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', X, Y],add,_) \ fact(['p:hasForeMother', X, Y],del,U) <=> true | fact(['p:hasForeMother', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,_), fact(['p:hasMother', X1, X2],add,_) \ fact(['p:hasGrandmother', X0, X2],del,U) <=> true | fact(['p:hasGrandmother', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', X0, X1],add,_), fact(['p:hasBrother', X1, X2],add,_) \ fact(['p:isSisterInLawOf', X0, X2],del,U) <=> true | fact(['p:isSisterInLawOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:isAuntInLawOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:Wife', X],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,_), fact(['p:isFemalePartnerIn', X, X1],add,_), fact(['p:Marriage', X1],add,_), fact(['p:hasMalePartner', X1, X2],add,_), fact(['p:Man', X2],add,_) \ fact(['p:Wife', X],del,U) <=> true | fact(['p:Wife', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasDeathYear', X, Y1],add,_), fact(['p:hasDeathYear', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['p:hasPartner', Y, X],add,_) \ fact(['p:isPartnerIn', X, Y],del,U) <=> true | fact(['p:isPartnerIn', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isPartnerIn', Y, X],add,_) \ fact(['p:hasPartner', X, Y],del,U) <=> true | fact(['p:hasPartner', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', X, Y],add,_) \ fact(['p:directSiblingOf', X, Y],del,U) <=> true | fact(['p:directSiblingOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isForefatherOf', Y, X],add,_) \ fact(['p:hasForeFather', X, Y],del,U) <=> true | fact(['p:hasForeFather', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', Y, X],add,_) \ fact(['p:isForefatherOf', X, Y],del,U) <=> true | fact(['p:isForefatherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isFatherOf', Y, X],add,_) \ fact(['p:hasFather', X, Y],del,U) <=> true | fact(['p:hasFather', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', Y, X],add,_) \ fact(['p:isFatherOf', X, Y],del,U) <=> true | fact(['p:isFatherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isHusbandOf', X0, X1],add,_), fact(['p:sisterOf', X1, X2],add,_), fact(['p:isParentOf', X2, X3],add,_) \ fact(['p:isUncleInLawOf', X0, X3],del,U) <=> true | fact(['p:isUncleInLawOf', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:ThirdCousin', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:hasParent', X, X1],add,_), fact(['p:hasParent', X1, X2],add,_), fact(['p:Person', X2],add,_), fact(['p:hasParent', X2, X3],add,_), fact(['p:Person', X3],add,_), fact(['p:isSiblingOf', X3, X4],add,_), fact(['p:Person', X4],add,_), fact(['p:isParentOf', X4, X5],add,_), fact(['p:Person', X5],add,_), fact(['p:isParentOf', X5, X6],add,_), fact(['p:Person', X6],add,_), fact(['p:isParentOf', X6, X7],add,_), fact(['p:Person', X7],add,_) \ fact(['p:ThirdCousin', X],del,U) <=> true | fact(['p:ThirdCousin', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:hasGender', X, X1],add,_), fact(['p:Female', X1],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,_), fact(['p:isSiblingOf', X1, X2],add,_), fact(['p:isParentOf', X2, X3],add,_) \ fact(['p:isFirstCousinOf', X0, X3],del,U) <=> true | fact(['p:isFirstCousinOf', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', X, Y],add,_) \ fact(['p:hasAncestor', X, Y],del,U) <=> true | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', Y, X],add,_) \ fact(['p:isSpouseOf', X, Y],del,U) <=> true | fact(['p:isSpouseOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', X0, X1],add,_), fact(['p:isParentOf', X1, X2],add,_) \ fact(['p:isAuntOf', X0, X2],del,U) <=> true | fact(['p:isAuntOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', X, Y],add,_) \ fact(['p:hasAncestor', X, Y],del,U) <=> true | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSisterInLawOf', X, Y],add,_) \ fact(['p:isSiblingInLawOf', X, Y],del,U) <=> true | fact(['p:isSiblingInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatAuntOf', Y, X],add,_) \ fact(['p:hasGreatAunt', X, Y],del,U) <=> true | fact(['p:hasGreatAunt', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatAunt', Y, X],add,_) \ fact(['p:isGreatAuntOf', X, Y],del,U) <=> true | fact(['p:isGreatAuntOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Spouse', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isSpouseOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Spouse', X],del,U) <=> true | fact(['p:Spouse', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', _, X1],add,_) \ fact(['p:Marriage', X1],del,U) <=> true | fact(['p:Marriage', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isBrotherInLawOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:Mother', X],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,_), fact(['p:isMotherOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Mother', X],del,U) <=> true | fact(['p:Mother', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasDaughter', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isUncleOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:FirstCousin', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:hasParent', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isSiblingOf', X1, X2],add,_), fact(['p:Person', X2],add,_), fact(['p:isParentOf', X2, X3],add,_), fact(['p:Person', X3],add,_) \ fact(['p:FirstCousin', X],del,U) <=> true | fact(['p:FirstCousin', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isMotherInLawOf', Y, X],add,_) \ fact(['p:hasMotherInLaw', X, Y],del,U) <=> true | fact(['p:hasMotherInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMotherInLaw', Y, X],add,_) \ fact(['p:isMotherInLawOf', X, Y],del,U) <=> true | fact(['p:isMotherInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatAuntOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFamilyName', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,_), fact(['p:hasFather', X1, X2],add,_) \ fact(['p:hasGrandfather', X0, X2],del,U) <=> true | fact(['p:hasGrandfather', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:Son', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isSonOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Son', X],del,U) <=> true | fact(['p:Son', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', X0, X1],add,_), fact(['p:isSiblingOf', X1, X2],add,_), fact(['p:isGreatGrandParentOf', X2, X3],add,_) \ fact(['p:isThirdCousinOf', X0, X3],del,U) <=> true | fact(['p:isThirdCousinOf', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['p:isGrandfatherOf', Y, X],add,_) \ fact(['p:hasGrandfather', X, Y],del,U) <=> true | fact(['p:hasGrandfather', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandfather', Y, X],add,_) \ fact(['p:isGrandfatherOf', X, Y],del,U) <=> true | fact(['p:isGrandfatherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', X, Y],add,_) \ fact(['p:isSpouseOf', X, Y],del,U) <=> true | fact(['p:isSpouseOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Daughter', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isDaughterOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Daughter', X],del,U) <=> true | fact(['p:Daughter', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFatherInLaw', X, Y],add,_) \ fact(['p:hasParentInLaw', X, Y],del,U) <=> true | fact(['p:hasParentInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:MaleAncestor', X],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,_), fact(['p:isAncestorOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:MaleAncestor', X],del,U) <=> true | fact(['p:MaleAncestor', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isFatherInLawOf', Y, X],add,_) \ fact(['p:hasFatherInLaw', X, Y],del,U) <=> true | fact(['p:hasFatherInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFatherInLaw', Y, X],add,_) \ fact(['p:isFatherInLawOf', X, Y],del,U) <=> true | fact(['p:isFatherInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasDaughter', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', X, Y1],add,_), fact(['p:hasFather', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X, Y],add,_) \ fact(['p:isInLawOf', X, Y],del,U) <=> true | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasBrother', Y, X],add,_) \ fact(['p:brotherOf', X, Y],del,U) <=> true | fact(['p:brotherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', Y, X],add,_) \ fact(['p:hasBrother', X, Y],del,U) <=> true | fact(['p:hasBrother', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', X, _],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Parent', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isParentOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Parent', X],del,U) <=> true | fact(['p:Parent', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', X, _],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasSon', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatAuntOf', X, _],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isNephewOf', X, _],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Forefather', X],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,_), fact(['p:isForefatherOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Forefather', X],del,U) <=> true | fact(['p:Forefather', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isNieceOf', X, _],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isInLawOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:SecondCousin', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:hasParent', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:hasParent', X1, X2],add,_), fact(['p:Person', X2],add,_), fact(['p:isSiblingOf', X2, X3],add,_), fact(['p:Person', X3],add,_), fact(['p:isParentOf', X3, X4],add,_), fact(['p:Person', X4],add,_), fact(['p:isParentOf', X4, X5],add,_), fact(['p:Person', X5],add,_) \ fact(['p:SecondCousin', X],del,U) <=> true | fact(['p:SecondCousin', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasChild', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isRelationOf', Y, X],add,_) \ fact(['p:isRelationOf', X, Y],del,U) <=> true | fact(['p:isRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSecondCousinOf', Y, X],add,_) \ fact(['p:isSecondCousinOf', X, Y],del,U) <=> true | fact(['p:isSecondCousinOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isNieceOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isGrandmotherOf', Y, X],add,_) \ fact(['p:hasGrandmother', X, Y],del,U) <=> true | fact(['p:hasGrandmother', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandmother', Y, X],add,_) \ fact(['p:isGrandmotherOf', X, Y],del,U) <=> true | fact(['p:isGrandmotherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingInLawOf', X, Y],add,_) \ fact(['p:isInLawOf', X, Y],del,U) <=> true | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Ancestor', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isAncestorOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Ancestor', X],del,U) <=> true | fact(['p:Ancestor', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatAunt', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', Y, X],add,_) \ fact(['p:isSiblingOf', X, Y],del,U) <=> true | fact(['p:isSiblingOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isForemotherOf', X, Y],add,_) \ fact(['p:isAncestorOf', X, Y],del,U) <=> true | fact(['p:isAncestorOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isForemotherOf', X, Y],add,_), fact(['p:isForemotherOf', Y, Z],add,_) \ fact(['p:isForemotherOf', X, Z],del,U) <=> true | fact(['p:isForemotherOf', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', X, Y],add,_), fact(['p:hasForeFather', Y, Z],add,_) \ fact(['p:hasForeFather', X, Z],del,U) <=> true | fact(['p:hasForeFather', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['p:hasHusband', X, Y],add,_) \ fact(['p:isSpouseOf', X, Y],del,U) <=> true | fact(['p:isSpouseOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isParentInLawOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:knownAs', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasBrother', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatUncleOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', X0, X1],add,_), fact(['p:hasFemalePartner', X1, X2],add,_) \ fact(['p:hasWife', X0, X2],del,U) <=> true | fact(['p:hasWife', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', X0, X1],add,_), fact(['p:hasMalePartner', X1, X2],add,_) \ fact(['p:hasHusband', X0, X2],del,U) <=> true | fact(['p:hasHusband', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:directSiblingOf', X, Y],add,_) \ fact(['p:isSiblingOf', X, Y],del,U) <=> true | fact(['p:isSiblingOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMotherInLaw', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', Y, X],add,_) \ fact(['p:isParentOf', X, Y],del,U) <=> true | fact(['p:isParentOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:ParentInLaw', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isParentOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isSpouseOf', X1, X2],add,_), fact(['p:Person', X2],add,_) \ fact(['p:ParentInLaw', X],del,U) <=> true | fact(['p:ParentInLaw', X],add,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:formerlyKnownAs', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X, Y],add,_) \ fact(['p:hasAncestor', X, Y],del,U) <=> true | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Cousin', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:hasAncestor', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isSiblingOf', X1, X2],add,_), fact(['p:Person', X2],add,_), fact(['p:isParentOf', X2, X3],add,_), fact(['p:Person', X3],add,_) \ fact(['p:Cousin', X],del,U) <=> true | fact(['p:Cousin', X],add,U), applied_rules(1,red).
phase(2), fact(['p:GreatGrandparent', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isParentOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_), fact(['p:isParentOf', X2, X3],add,_), fact(['p:Person', X3],add,_) \ fact(['p:GreatGrandparent', X],del,U) <=> true | fact(['p:GreatGrandparent', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isUncleOf', Y, X],add,_) \ fact(['p:hasUncle', X, Y],del,U) <=> true | fact(['p:hasUncle', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasUncle', Y, X],add,_) \ fact(['p:isUncleOf', X, Y],del,U) <=> true | fact(['p:isUncleOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasHusband', X, _],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:formerlyKnownAs', X, Y],add,_) \ fact(['p:knownAs', X, Y],del,U) <=> true | fact(['p:knownAs', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', Y, X],add,_) \ fact(['p:isFirstCousinOf', X, Y],del,U) <=> true | fact(['p:isFirstCousinOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOnceRemovedOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandfather', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', X, Y],add,_), fact(['p:hasForeMother', Y, Z],add,_) \ fact(['p:hasForeMother', X, Z],del,U) <=> true | fact(['p:hasForeMother', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['p:isAuntOf', Y, X],add,_) \ fact(['p:hasAunt', X, Y],del,U) <=> true | fact(['p:hasAunt', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAunt', Y, X],add,_) \ fact(['p:isAuntOf', X, Y],del,U) <=> true | fact(['p:isAuntOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isUncleOf', X, _],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', X, Y],add,_) \ fact(['p:hasForeFather', X, Y],del,U) <=> true | fact(['p:hasForeFather', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_) \ fact(['p:DomainEntity', X],del,U) <=> true | fact(['p:DomainEntity', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatUncle', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isUncleInLawOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:FemaleDescendent', X],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,_), fact(['p:hasAncestor', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:FemaleDescendent', X],del,U) <=> true | fact(['p:FemaleDescendent', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandmother', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isPartnerIn', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasUncleInLaw', Y, X],add,_) \ fact(['p:isUncleInLawOf', X, Y],del,U) <=> true | fact(['p:isUncleInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isUncleInLawOf', Y, X],add,_) \ fact(['p:hasUncleInLaw', X, Y],del,U) <=> true | fact(['p:hasUncleInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:FemaleAncestor', X],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,_), fact(['p:isAncestorOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:FemaleAncestor', X],del,U) <=> true | fact(['p:FemaleAncestor', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isNieceOf', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', _, X1],add,_) \ fact(['p:Marriage', X1],del,U) <=> true | fact(['p:Marriage', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGender', X, Y1],add,_), fact(['p:hasGender', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['p:hasBrother', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', X, Y],add,_), fact(['p:hasAncestor', Y, Z],add,_) \ fact(['p:hasAncestor', X, Z],del,U) <=> true | fact(['p:hasAncestor', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['p:Foremother', X],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,_), fact(['p:isForemotherOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Foremother', X],del,U) <=> true | fact(['p:Foremother', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOnceRemovedOf', Y, X],add,_) \ fact(['p:isFirstCousinOnceRemovedOf', X, Y],del,U) <=> true | fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:directSiblingOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', Y, X],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isAncestorOf', Y, X],add,_) \ fact(['p:hasAncestor', X, Y],del,U) <=> true | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', Y, X],add,_) \ fact(['p:isAncestorOf', X, Y],del,U) <=> true | fact(['p:isAncestorOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasUncle', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', X, Y],add,_) \ fact(['p:hasAncestor', X, Y],del,U) <=> true | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', X0, X1],add,_), fact(['p:grandParentOf', X1, X2],add,_) \ fact(['p:isGreatUncleOf', X0, X2],del,U) <=> true | fact(['p:isGreatUncleOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,_), fact(['p:hasGrandfather', X1, X2],add,_) \ fact(['p:hasGreatGrandfather', X0, X2],del,U) <=> true | fact(['p:hasGreatGrandfather', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:Male', X],add,_) \ fact(['p:Sex', X],del,U) <=> true | fact(['p:Sex', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:Female', X],add,_), fact(['p:Male', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMotherInLaw', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatAunt', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:Sex', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isRelationOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isSecondCousinOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasBrotherInLaw', Y, X],add,_) \ fact(['p:isSisterInLawOf', X, Y],del,U) <=> true | fact(['p:isSisterInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSisterInLawOf', Y, X],add,_) \ fact(['p:hasBrotherInLaw', X, Y],del,U) <=> true | fact(['p:hasBrotherInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X0, X1],add,_), fact(['p:isSiblingOf', X1, X2],add,_) \ fact(['p:isSiblingInLawOf', X0, X2],del,U) <=> true | fact(['p:isSiblingInLawOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:hasGender', X, X1],add,_), fact(['p:Male', X1],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatGrandParentOf', Y, X],add,_) \ fact(['p:hasGreatGrandParent', X, Y],del,U) <=> true | fact(['p:hasGreatGrandParent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', Y, X],add,_) \ fact(['p:isGreatGrandParentOf', X, Y],del,U) <=> true | fact(['p:isGreatGrandParentOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatAunt', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isUncleInLawOf', X, _],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isThirdCousinOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Father', X],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,_), fact(['p:isFatherOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Father', X],del,U) <=> true | fact(['p:Father', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isNephewOf', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAunt', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingInLawOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:marriageYear', X, _],add,_) \ fact(['p:Marriage', X],del,U) <=> true | fact(['p:Marriage', X],add,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', X, _],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', X0, X1],add,_), fact(['p:isParentOf', X1, X2],add,_) \ fact(['p:isFirstCousinOnceRemovedOf', X0, X2],del,U) <=> true | fact(['p:isFirstCousinOnceRemovedOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:FatherInLaw', X],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,_), fact(['p:isFatherOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isSpouseOf', X1, X2],add,_), fact(['p:Person', X2],add,_) \ fact(['p:FatherInLaw', X],del,U) <=> true | fact(['p:FatherInLaw', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatGrandfatherOf', Y, X],add,_) \ fact(['p:hasGreatGrandfather', X, Y],del,U) <=> true | fact(['p:hasGreatGrandfather', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandfather', Y, X],add,_) \ fact(['p:isGreatGrandfatherOf', X, Y],del,U) <=> true | fact(['p:isGreatGrandfatherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isUncleOf', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isInLawOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatUncle', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', X, Y],add,_), fact(['p:isBloodRelationOf', Y, Z],add,_) \ fact(['p:isBloodRelationOf', X, Z],del,U) <=> true | fact(['p:isBloodRelationOf', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['p:GreatGrandfather', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isFatherOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_), fact(['p:isParentOf', X2, X3],add,_), fact(['p:Person', X3],add,_) \ fact(['p:GreatGrandfather', X],del,U) <=> true | fact(['p:GreatGrandfather', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', X, Y],add,_) \ fact(['p:isPartnerIn', X, Y],del,U) <=> true | fact(['p:isPartnerIn', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSecondCousinOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandmother', X, Y],add,_) \ fact(['p:hasGreatGrandParent', X, Y],del,U) <=> true | fact(['p:hasGreatGrandParent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasBrotherInLaw', Y, X],add,_) \ fact(['p:isBrotherInLawOf', X, Y],del,U) <=> true | fact(['p:isBrotherInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isBrotherInLawOf', Y, X],add,_) \ fact(['p:hasBrotherInLaw', X, Y],del,U) <=> true | fact(['p:hasBrotherInLaw', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Grandmother', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isMotherOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_) \ fact(['p:Grandmother', X],del,U) <=> true | fact(['p:Grandmother', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X0, X1],add,_), fact(['p:hasMother', X1, X2],add,_) \ fact(['p:hasMotherInLaw', X0, X2],del,U) <=> true | fact(['p:hasMotherInLaw', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:Husband', X],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,_), fact(['p:isMalePartnerIn', X, X1],add,_), fact(['p:Marriage', X1],add,_), fact(['p:hasFemalePartner', X1, X2],add,_), fact(['p:Woman', X2],add,_) \ fact(['p:Husband', X],del,U) <=> true | fact(['p:Husband', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandmother', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isThirdCousinOf', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGender', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFemalePartner', Y, X],add,_) \ fact(['p:isFemalePartnerIn', X, Y],del,U) <=> true | fact(['p:isFemalePartnerIn', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', Y, X],add,_) \ fact(['p:hasFemalePartner', X, Y],del,U) <=> true | fact(['p:hasFemalePartner', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:InLaw', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isInLawOf', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:InLaw', X],del,U) <=> true | fact(['p:InLaw', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingInLawOf', Y, X],add,_) \ fact(['p:isSiblingInLawOf', X, Y],del,U) <=> true | fact(['p:isSiblingInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Descendent', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:hasAncestor', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:Descendent', X],del,U) <=> true | fact(['p:Descendent', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isParentInLawOf', X, Y],add,_) \ fact(['p:isInLawOf', X, Y],del,U) <=> true | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:Marriage', X],add,_), fact(['p:Person', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isSecondCousinOf', X, Y],add,_) \ fact(['p:isBloodRelationOf', X, Y],del,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandfather', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', X, Y],add,_) \ fact(['p:isRelationOf', X, Y],del,U) <=> true | fact(['p:isRelationOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:PersonWithManySibling', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', _, X1],add,_) \ fact(['p:Man', X1],del,U) <=> true | fact(['p:Man', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:grandParentOf', Y, X],add,_) \ fact(['p:hasGrandParent', X, Y],del,U) <=> true | fact(['p:hasGrandParent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', Y, X],add,_) \ fact(['p:grandParentOf', X, Y],del,U) <=> true | fact(['p:grandParentOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:MaleDescendent', X],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,_), fact(['p:hasAncestor', X, X1],add,_), fact(['p:Person', X1],add,_) \ fact(['p:MaleDescendent', X],del,U) <=> true | fact(['p:MaleDescendent', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isSonOf', X0, X1],add,_), fact(['p:isSiblingOf', X1, X2],add,_) \ fact(['p:isNephewOf', X0, X2],del,U) <=> true | fact(['p:isNephewOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:isInLawOf', Y, X],add,_) \ fact(['p:isInLawOf', X, Y],del,U) <=> true | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,_), fact(['p:hasGrandmother', X1, X2],add,_) \ fact(['p:hasGreatGrandmother', X0, X2],del,U) <=> true | fact(['p:hasGreatGrandmother', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:isForemotherOf', Y, X],add,_) \ fact(['p:hasForeMother', X, Y],del,U) <=> true | fact(['p:hasForeMother', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', Y, X],add,_) \ fact(['p:isForemotherOf', X, Y],del,U) <=> true | fact(['p:isForemotherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandmother', _, X1],add,_) \ fact(['p:Woman', X1],del,U) <=> true | fact(['p:Woman', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isBrotherInLawOf', X, Y],add,_) \ fact(['p:isSiblingInLawOf', X, Y],del,U) <=> true | fact(['p:isSiblingInLawOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:ParentOfSmallFamily', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:ParentOfLargeFamily', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Aunt', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:sisterOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_) \ fact(['p:Aunt', X],del,U) <=> true | fact(['p:Aunt', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isMotherOf', Y, X],add,_) \ fact(['p:hasMother', X, Y],del,U) <=> true | fact(['p:hasMother', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', Y, X],add,_) \ fact(['p:isMotherOf', X, Y],del,U) <=> true | fact(['p:isMotherOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandfather', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isThirdCousinOf', Y, X],add,_) \ fact(['p:isThirdCousinOf', X, Y],del,U) <=> true | fact(['p:isThirdCousinOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSisterInLawOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isWifeOf', Y, X],add,_) \ fact(['p:hasWife', X, Y],del,U) <=> true | fact(['p:hasWife', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', Y, X],add,_) \ fact(['p:isWifeOf', X, Y],del,U) <=> true | fact(['p:isWifeOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSisterInLawOf', X, _],add,_) \ fact(['p:Woman', X],del,U) <=> true | fact(['p:Woman', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasFatherInLaw', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isGreatUncleOf', X, _],add,_) \ fact(['p:Man', X],del,U) <=> true | fact(['p:Man', X],add,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', X, Y],add,_) \ fact(['p:isPartnerIn', X, Y],del,U) <=> true | fact(['p:isPartnerIn', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isAuntOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:isDaughterOf', X0, X1],add,_), fact(['p:isSiblingOf', X1, X2],add,_) \ fact(['p:isNieceOf', X0, X2],del,U) <=> true | fact(['p:isNieceOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', X0, X1],add,_), fact(['p:grandParentOf', X1, X2],add,_) \ fact(['p:isGreatAuntOf', X0, X2],del,U) <=> true | fact(['p:isGreatAuntOf', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', _, X1],add,_) \ fact(['p:Person', X1],del,U) <=> true | fact(['p:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['p:hasChild', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:GreatGreatGrandparent', X],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,_), fact(['p:isParentOf', X, X1],add,_), fact(['p:Person', X1],add,_), fact(['p:isParentOf', X1, X2],add,_), fact(['p:Person', X2],add,_), fact(['p:isParentOf', X2, X3],add,_), fact(['p:Person', X3],add,_), fact(['p:isParentOf', X3, X4],add,_), fact(['p:Person', X4],add,_) \ fact(['p:GreatGreatGrandparent', X],del,U) <=> true | fact(['p:GreatGreatGrandparent', X],add,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandfather', X, Y],add,_) \ fact(['p:hasGreatGrandParent', X, Y],del,U) <=> true | fact(['p:hasGreatGrandParent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', X, Y],add,_), fact(['p:isSiblingOf', Y, Z],add,_) \ fact(['p:isSiblingOf', X, Z],del,U) <=> true | fact(['p:isSiblingOf', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['p:isParentInLawOf', X, _],add,_) \ fact(['p:Person', X],del,U) <=> true | fact(['p:Person', X],add,U), applied_rules(1,red).

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
phase(5), fact(['p:hasParent', X, Y],add,U1), fact(['p:maleInFamilinx', Y],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasFather', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, Y],add,U1), fact(['p:femaleInFamilinx', Y],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasMother', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isWifeOf', X0, X1],add,U1), fact(['p:brotherOf', X1, X2],add,U2), fact(['p:isParentOf', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:isAuntInLawOf', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatUncleOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasGreatUncle', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isGreatUncleOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X0, X1],add,U1), fact(['p:isSiblingOf', X1, X2],add,U2), fact(['p:grandParentOf', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:isSecondCousinOf', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasGrandParent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:alsoKnownAs', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:knownAs', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:directSiblingOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasBirthYear', X, Y1],add,U1), fact(['p:hasBirthYear', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isChildOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isChildOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParentInLaw', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isParentInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', X, Y],add,U1), fact(['p:isForefatherOf', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['p:isForefatherOf', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasDeathYear', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,U1), fact(['p:hasFather', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasFatherInLaw', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', X, Y1],add,U1), fact(['p:hasMother', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAuntInLaw', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasAuntInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAuntInLaw', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasAuntInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Grandparent', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isParentOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:Grandparent', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:alsoKnownAs', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:GreatUncle', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:brotherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5), fact(['p:isParentOf', X2, X3],add,U6), fact(['p:Person', X3],add,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | fact(['p:GreatUncle', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,U1) ==> member(U,[U1]) | fact(['p:DomainEntity', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X0, X1],add,U1), fact(['p:isParentOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isUncleOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandmotherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandmother', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandmotherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasBirthYear', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:MotherInLaw', X],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,U1), fact(['p:isMotherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isSpouseOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:MotherInLaw', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMalePartner', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isMalePartnerIn', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasMalePartner', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Grandfather', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isFatherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:Grandfather', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Female', X],add,U1) ==> member(U,[U1]) | fact(['p:Sex', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:Uncle', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:brotherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:Uncle', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', X, Y],add,U1), fact(['p:isRelationOf', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['p:isRelationOf', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasSister', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:sisterOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasSister', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGender', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Sex', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isDaughterOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasDaughter', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isDaughterOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSonOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasSon', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isSonOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Sex', X],add,U1) ==> member(U,[U1]) | fact(['p:DomainEntity', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isHusbandOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasHusband', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isHusbandOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isParentOf', X0, X1],add,U1), fact(['p:isSpouseOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isParentInLawOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X0, X1],add,U1), fact(['p:hasBrother', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isBrotherInLawOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:BloodRelation', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isBloodRelationOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:BloodRelation', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,U1), fact(['p:Sex', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isParentOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isParentOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:directSiblingOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasGrandParent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasForeMother', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,U1), fact(['p:hasMother', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasGrandmother', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X0, X1],add,U1), fact(['p:hasBrother', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isSisterInLawOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:Wife', X],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,U1), fact(['p:isFemalePartnerIn', X, X1],add,U2), fact(['p:Marriage', X1],add,U3), fact(['p:hasMalePartner', X1, X2],add,U4), fact(['p:Man', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:Wife', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasDeathYear', X, Y1],add,U1), fact(['p:hasDeathYear', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasPartner', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isPartnerIn', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasPartner', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:directSiblingOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasForeFather', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isForefatherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFatherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasFather', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isFatherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isHusbandOf', X0, X1],add,U1), fact(['p:sisterOf', X1, X2],add,U2), fact(['p:isParentOf', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:isUncleInLawOf', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:ThirdCousin', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:hasParent', X, X1],add,U2), fact(['p:hasParent', X1, X2],add,U3), fact(['p:Person', X2],add,U4), fact(['p:hasParent', X2, X3],add,U5), fact(['p:Person', X3],add,U6), fact(['p:isSiblingOf', X3, X4],add,U7), fact(['p:Person', X4],add,U8), fact(['p:isParentOf', X4, X5],add,U9), fact(['p:Person', X5],add,U10), fact(['p:isParentOf', X5, X6],add,U11), fact(['p:Person', X6],add,U12), fact(['p:isParentOf', X6, X7],add,U13), fact(['p:Person', X7],add,U14) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9,U10,U11,U12,U13,U14]) | fact(['p:ThirdCousin', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:hasGender', X, X1],add,U2), fact(['p:Female', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,U1), fact(['p:isSiblingOf', X1, X2],add,U2), fact(['p:isParentOf', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:isFirstCousinOf', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X0, X1],add,U1), fact(['p:isParentOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isAuntOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasGreatAunt', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isGreatAuntOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Spouse', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isSpouseOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Spouse', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:Mother', X],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,U1), fact(['p:isMotherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Mother', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:FirstCousin', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:hasParent', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isSiblingOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5), fact(['p:isParentOf', X2, X3],add,U6), fact(['p:Person', X3],add,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | fact(['p:FirstCousin', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isMotherInLawOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasMotherInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isMotherInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFamilyName', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,U1), fact(['p:hasFather', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasGrandfather', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:Son', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isSonOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Son', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', X0, X1],add,U1), fact(['p:isSiblingOf', X1, X2],add,U2), fact(['p:isGreatGrandParentOf', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:isThirdCousinOf', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGrandfatherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasGrandfather', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isGrandfatherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Daughter', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isDaughterOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Daughter', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:MaleAncestor', X],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,U1), fact(['p:isAncestorOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:MaleAncestor', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFatherInLawOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasFatherInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isFatherInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, Y1],add,U1), fact(['p:hasFather', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:brotherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasBrother', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Parent', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isParentOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Parent', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Forefather', X],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,U1), fact(['p:isForefatherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Forefather', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:SecondCousin', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:hasParent', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:hasParent', X1, X2],add,U4), fact(['p:Person', X2],add,U5), fact(['p:isSiblingOf', X2, X3],add,U6), fact(['p:Person', X3],add,U7), fact(['p:isParentOf', X3, X4],add,U8), fact(['p:Person', X4],add,U9), fact(['p:isParentOf', X4, X5],add,U10), fact(['p:Person', X5],add,U11) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9,U10,U11]) | fact(['p:SecondCousin', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isSecondCousinOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGrandmotherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasGrandmother', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isGrandmotherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Ancestor', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isAncestorOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Ancestor', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isSiblingOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', X, Y],add,U1), fact(['p:isForemotherOf', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['p:isForemotherOf', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, Y],add,U1), fact(['p:hasForeFather', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasForeFather', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:knownAs', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatUncleOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X0, X1],add,U1), fact(['p:hasFemalePartner', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasWife', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', X0, X1],add,U1), fact(['p:hasMalePartner', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasHusband', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isSiblingOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isParentOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:ParentInLaw', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isParentOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isSpouseOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:ParentInLaw', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:formerlyKnownAs', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Cousin', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:hasAncestor', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isSiblingOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5), fact(['p:isParentOf', X2, X3],add,U6), fact(['p:Person', X3],add,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | fact(['p:Cousin', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGrandparent', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isParentOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5), fact(['p:isParentOf', X2, X3],add,U6), fact(['p:Person', X3],add,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | fact(['p:GreatGrandparent', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasUncle', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isUncleOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:formerlyKnownAs', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:knownAs', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isFirstCousinOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, Y],add,U1), fact(['p:hasForeMother', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasForeMother', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasAunt', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isAuntOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasForeFather', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1) ==> member(U,[U1]) | fact(['p:DomainEntity', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:FemaleDescendent', X],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,U1), fact(['p:hasAncestor', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:FemaleDescendent', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncleInLaw', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isUncleInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasUncleInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:FemaleAncestor', X],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,U1), fact(['p:isAncestorOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:FemaleAncestor', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGender', X, Y1],add,U1), fact(['p:hasGender', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, Y],add,U1), fact(['p:hasAncestor', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasAncestor', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['p:Foremother', X],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,U1), fact(['p:isForemotherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Foremother', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isAncestorOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X0, X1],add,U1), fact(['p:grandParentOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isGreatUncleOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,U1), fact(['p:hasGrandfather', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasGreatGrandfather', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:Male', X],add,U1) ==> member(U,[U1]) | fact(['p:Sex', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:Female', X],add,U1), fact(['p:Male', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:Sex', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrotherInLaw', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isSisterInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasBrotherInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,U1), fact(['p:isSiblingOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isSiblingInLawOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:hasGender', X, X1],add,U2), fact(['p:Male', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandParentOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandParentOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Father', X],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,U1), fact(['p:isFatherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Father', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:marriageYear', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Marriage', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X0, X1],add,U1), fact(['p:isParentOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isFirstCousinOnceRemovedOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:FatherInLaw', X],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,U1), fact(['p:isFatherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isSpouseOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:FatherInLaw', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandfatherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandfather', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandfatherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, Y],add,U1), fact(['p:isBloodRelationOf', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['p:isBloodRelationOf', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGrandfather', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isFatherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5), fact(['p:isParentOf', X2, X3],add,U6), fact(['p:Person', X3],add,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | fact(['p:GreatGrandfather', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isPartnerIn', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrotherInLaw', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isBrotherInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasBrotherInLaw', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Grandmother', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isMotherOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:Grandmother', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,U1), fact(['p:hasMother', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasMotherInLaw', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:Husband', X],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,U1), fact(['p:isMalePartnerIn', X, X1],add,U2), fact(['p:Marriage', X1],add,U3), fact(['p:hasFemalePartner', X1, X2],add,U4), fact(['p:Woman', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:Husband', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGender', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFemalePartner', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isFemalePartnerIn', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasFemalePartner', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:InLaw', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isInLawOf', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:InLaw', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Descendent', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:hasAncestor', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:Descendent', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,U1), fact(['p:Person', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:PersonWithManySibling', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:grandParentOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasGrandParent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:grandParentOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:MaleDescendent', X],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,U1), fact(['p:hasAncestor', X, X1],add,U2), fact(['p:Person', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['p:MaleDescendent', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSonOf', X0, X1],add,U1), fact(['p:isSiblingOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isNephewOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,U1), fact(['p:hasGrandmother', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:hasGreatGrandmother', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasForeMother', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isForemotherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:ParentOfSmallFamily', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:ParentOfLargeFamily', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Aunt', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:sisterOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5) ==> member(U,[U1,U2,U3,U4,U5]) | fact(['p:Aunt', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isMotherOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasMother', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isMotherOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isThirdCousinOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isWifeOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:hasWife', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', Y, X],add,U1) ==> member(U,[U1]) | fact(['p:isWifeOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatUncleOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:isPartnerIn', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:isDaughterOf', X0, X1],add,U1), fact(['p:isSiblingOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isNieceOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X0, X1],add,U1), fact(['p:grandParentOf', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['p:isGreatAuntOf', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGreatGrandparent', X],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,U1), fact(['p:isParentOf', X, X1],add,U2), fact(['p:Person', X1],add,U3), fact(['p:isParentOf', X1, X2],add,U4), fact(['p:Person', X2],add,U5), fact(['p:isParentOf', X2, X3],add,U6), fact(['p:Person', X3],add,U7), fact(['p:isParentOf', X3, X4],add,U8), fact(['p:Person', X4],add,U9) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9]) | fact(['p:GreatGreatGrandparent', X],add,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', X, Y],add,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', X, Y],add,U1), fact(['p:isSiblingOf', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['p:isSiblingOf', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', X, _],add,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,U), applied_rules(1,ins).

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
