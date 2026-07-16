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
phase(1), fact(['p:hasParent', X, Y],O1,M1,_), fact(['p:maleInFamilinx', Y],O2,M2,_) \ fact(['p:hasFather', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasParent',O1,M1),('p:maleInFamilinx',O2,M2)],M), fact(['p:hasFather', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, Y],O1,M1,_), fact(['p:femaleInFamilinx', Y],O2,M2,_) \ fact(['p:hasMother', X, Y],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasParent',O1,M1),('p:femaleInFamilinx',O2,M2)],M), fact(['p:hasMother', X, Y],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', X, Y],O1,M1,_) \ fact(['p:hasChild', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isWifeOf', X0, X1],O1,M1,_), fact(['p:brotherOf', X1, X2],O2,M2,_), fact(['p:isParentOf', X2, X3],O3,M3,_) \ fact(['p:isAuntInLawOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:isWifeOf',O1,M1),('p:brotherOf',O2,M2),('p:isParentOf',O3,M3)],M), fact(['p:isAuntInLawOf', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', X, Y],O1,M1,_) \ fact(['p:hasChild', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', Y, X],O1,M1,_) \ fact(['p:hasGreatUncle', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatUncle', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', Y, X],O1,M1,_) \ fact(['p:isGreatUncleOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatUncleOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X0, X1],O1,M1,_), fact(['p:isSiblingOf', X1, X2],O2,M2,_), fact(['p:grandParentOf', X2, X3],O3,M3,_) \ fact(['p:isSecondCousinOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:hasGrandParent',O1,M1),('p:isSiblingOf',O2,M2),('p:grandParentOf',O3,M3)],M), fact(['p:isSecondCousinOf', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', X, Y],O1,M1,_) \ fact(['p:hasGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:alsoKnownAs', X, Y],O1,M1,_) \ fact(['p:knownAs', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:knownAs', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', Y, X],O1,M1,_) \ fact(['p:directSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasBirthYear', X, Y1],O1,M1,_), fact(['p:hasBirthYear', X, Y2],O2,M2,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasBirthYear',O1,M1),('p:hasBirthYear',O2,M2)],M), fact(['owl:sameAs', Y1, Y2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', X, Y],O1,M1,_) \ fact(['p:isRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isChildOf', Y, X],O1,M1,_) \ fact(['p:hasChild', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', Y, X],O1,M1,_) \ fact(['p:isChildOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isChildOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasParentInLaw', Y, X],O1,M1,_) \ fact(['p:isParentInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isParentInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', Y, X],O1,M1,_) \ fact(['p:hasParentInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', X, Y],O1,M1,_), fact(['p:isForefatherOf', Y, Z],O2,M2,_) \ fact(['p:isForefatherOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isForefatherOf',O1,M1),('p:isForefatherOf',O2,M2)],M), fact(['p:isForefatherOf', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasDeathYear', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', X, Y],O1,M1,_) \ fact(['p:hasParentInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', X, Y],O1,M1,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,M1,_), fact(['p:hasFather', X1, X2],O2,M2,_) \ fact(['p:hasFatherInLaw', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isSpouseOf',O1,M1),('p:hasFather',O2,M2)],M), fact(['p:hasFatherInLaw', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, Y],O1,M1,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, Y1],O1,M1,_), fact(['p:hasMother', X, Y2],O2,M2,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasMother',O1,M1),('p:hasMother',O2,M2)],M), fact(['owl:sameAs', Y1, Y2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasAuntInLaw', Y, X],O1,M1,_) \ fact(['p:hasAuntInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAuntInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAuntInLaw', Y, X],O1,M1,_) \ fact(['p:hasAuntInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAuntInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Grandparent', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isParentOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_) \ fact(['p:Grandparent', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Person',O1,M1),('p:isParentOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5)],M), fact(['p:Grandparent', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', X, _],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:alsoKnownAs', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:GreatUncle', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:brotherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_), fact(['p:isParentOf', X2, X3],O6,M6,_), fact(['p:Person', X3],O7,M7,_) \ fact(['p:GreatUncle', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | check_pos_mark([('p:Person',O1,M1),('p:brotherOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5),('p:isParentOf',O6,M6),('p:Person',O7,M7)],M), fact(['p:GreatUncle', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', X, _],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,M1,_) \ fact(['p:DomainEntity', X],add,_,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X0, X1],O1,M1,_), fact(['p:isParentOf', X1, X2],O2,M2,_) \ fact(['p:isUncleOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:brotherOf',O1,M1),('p:isParentOf',O2,M2)],M), fact(['p:isUncleOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', _, X1],O1,M1,_) \ fact(['p:Marriage', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandmotherOf', Y, X],O1,M1,_) \ fact(['p:hasGreatGrandmother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandmother', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', Y, X],O1,M1,_) \ fact(['p:isGreatGrandmotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatGrandmotherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasBirthYear', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:MotherInLaw', X],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,M1,_), fact(['p:isMotherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isSpouseOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_) \ fact(['p:MotherInLaw', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Woman',O1,M1),('p:isMotherOf',O2,M2),('p:Person',O3,M3),('p:isSpouseOf',O4,M4),('p:Person',O5,M5)],M), fact(['p:MotherInLaw', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasMalePartner', Y, X],O1,M1,_) \ fact(['p:isMalePartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isMalePartnerIn', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', Y, X],O1,M1,_) \ fact(['p:hasMalePartner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasMalePartner', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X, _],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', X, Y],O1,M1,_) \ fact(['p:isAncestorOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Grandfather', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isFatherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_) \ fact(['p:Grandfather', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Person',O1,M1),('p:isFatherOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5)],M), fact(['p:Grandfather', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:Female', X],O1,M1,_) \ fact(['p:Sex', X],add,_,U) <=> member(del,[O1]) | fact(['p:Sex', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Uncle', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:brotherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_) \ fact(['p:Uncle', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Person',O1,M1),('p:brotherOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5)],M), fact(['p:Uncle', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', X, Y],O1,M1,_), fact(['p:isRelationOf', Y, Z],O2,M2,_) \ fact(['p:isRelationOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isRelationOf',O1,M1),('p:isRelationOf',O2,M2)],M), fact(['p:isRelationOf', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X, _],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasSister', Y, X],O1,M1,_) \ fact(['p:sisterOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:sisterOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', Y, X],O1,M1,_) \ fact(['p:hasSister', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasSister', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', _, X1],O1,M1,_) \ fact(['p:Sex', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Sex', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isDaughterOf', Y, X],O1,M1,_) \ fact(['p:hasDaughter', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasDaughter', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', Y, X],O1,M1,_) \ fact(['p:isDaughterOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isDaughterOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSonOf', Y, X],O1,M1,_) \ fact(['p:hasSon', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasSon', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', Y, X],O1,M1,_) \ fact(['p:isSonOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSonOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Sex', X],O1,M1,_) \ fact(['p:DomainEntity', X],add,_,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isHusbandOf', Y, X],O1,M1,_) \ fact(['p:hasHusband', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasHusband', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', Y, X],O1,M1,_) \ fact(['p:isHusbandOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isHusbandOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', X, Y],O1,M1,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isParentOf', X0, X1],O1,M1,_), fact(['p:isSpouseOf', X1, X2],O2,M2,_) \ fact(['p:isParentInLawOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isParentOf',O1,M1),('p:isSpouseOf',O2,M2)],M), fact(['p:isParentInLawOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', X, _],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X0, X1],O1,M1,_), fact(['p:hasBrother', X1, X2],O2,M2,_) \ fact(['p:isBrotherInLawOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasWife',O1,M1),('p:hasBrother',O2,M2)],M), fact(['p:isBrotherInLawOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:BloodRelation', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isBloodRelationOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:BloodRelation', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:isBloodRelationOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:BloodRelation', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,M1,_), fact(['p:Sex', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:Marriage',O1,M1),('p:Sex',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isParentOf', X, Y],O1,M1,_) \ fact(['p:hasChild', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', X, Y],O1,M1,_) \ fact(['p:isParentOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isParentOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X, Y],O1,M1,_) \ fact(['p:directSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', X, Y],O1,M1,_) \ fact(['p:hasGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, Y],O1,M1,_) \ fact(['p:hasForeMother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasForeMother', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,M1,_), fact(['p:hasMother', X1, X2],O2,M2,_) \ fact(['p:hasGrandmother', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasParent',O1,M1),('p:hasMother',O2,M2)],M), fact(['p:hasGrandmother', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X0, X1],O1,M1,_), fact(['p:hasBrother', X1, X2],O2,M2,_) \ fact(['p:isSisterInLawOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasWife',O1,M1),('p:hasBrother',O2,M2)],M), fact(['p:isSisterInLawOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Wife', X],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,M1,_), fact(['p:isFemalePartnerIn', X, X1],O2,M2,_), fact(['p:Marriage', X1],O3,M3,_), fact(['p:hasMalePartner', X1, X2],O4,M4,_), fact(['p:Man', X2],O5,M5,_) \ fact(['p:Wife', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Woman',O1,M1),('p:isFemalePartnerIn',O2,M2),('p:Marriage',O3,M3),('p:hasMalePartner',O4,M4),('p:Man',O5,M5)],M), fact(['p:Wife', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasDeathYear', X, Y1],O1,M1,_), fact(['p:hasDeathYear', X, Y2],O2,M2,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasDeathYear',O1,M1),('p:hasDeathYear',O2,M2)],M), fact(['owl:sameAs', Y1, Y2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasPartner', Y, X],O1,M1,_) \ fact(['p:isPartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', Y, X],O1,M1,_) \ fact(['p:hasPartner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasPartner', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X, Y],O1,M1,_) \ fact(['p:directSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', Y, X],O1,M1,_) \ fact(['p:hasForeFather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasForeFather', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', Y, X],O1,M1,_) \ fact(['p:isForefatherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isForefatherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFatherOf', Y, X],O1,M1,_) \ fact(['p:hasFather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasFather', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', Y, X],O1,M1,_) \ fact(['p:isFatherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFatherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isHusbandOf', X0, X1],O1,M1,_), fact(['p:sisterOf', X1, X2],O2,M2,_), fact(['p:isParentOf', X2, X3],O3,M3,_) \ fact(['p:isUncleInLawOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:isHusbandOf',O1,M1),('p:sisterOf',O2,M2),('p:isParentOf',O3,M3)],M), fact(['p:isUncleInLawOf', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:ThirdCousin', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:hasParent', X, X1],O2,M2,_), fact(['p:hasParent', X1, X2],O3,M3,_), fact(['p:Person', X2],O4,M4,_), fact(['p:hasParent', X2, X3],O5,M5,_), fact(['p:Person', X3],O6,M6,_), fact(['p:isSiblingOf', X3, X4],O7,M7,_), fact(['p:Person', X4],O8,M8,_), fact(['p:isParentOf', X4, X5],O9,M9,_), fact(['p:Person', X5],O10,M10,_), fact(['p:isParentOf', X5, X6],O11,M11,_), fact(['p:Person', X6],O12,M12,_), fact(['p:isParentOf', X6, X7],O13,M13,_), fact(['p:Person', X7],O14,M14,_) \ fact(['p:ThirdCousin', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14]) | check_pos_mark([('p:Person',O1,M1),('p:hasParent',O2,M2),('p:hasParent',O3,M3),('p:Person',O4,M4),('p:hasParent',O5,M5),('p:Person',O6,M6),('p:isSiblingOf',O7,M7),('p:Person',O8,M8),('p:isParentOf',O9,M9),('p:Person',O10,M10),('p:isParentOf',O11,M11),('p:Person',O12,M12),('p:isParentOf',O13,M13),('p:Person',O14,M14)],M), fact(['p:ThirdCousin', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:hasGender', X, X1],O2,M2,_), fact(['p:Female', X1],O3,M3,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:hasGender',O2,M2),('p:Female',O3,M3)],M), fact(['p:Woman', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,M1,_), fact(['p:isSiblingOf', X1, X2],O2,M2,_), fact(['p:isParentOf', X2, X3],O3,M3,_) \ fact(['p:isFirstCousinOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:hasParent',O1,M1),('p:isSiblingOf',O2,M2),('p:isParentOf',O3,M3)],M), fact(['p:isFirstCousinOf', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, Y],O1,M1,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', Y, X],O1,M1,_) \ fact(['p:isSpouseOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X0, X1],O1,M1,_), fact(['p:isParentOf', X1, X2],O2,M2,_) \ fact(['p:isAuntOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:sisterOf',O1,M1),('p:isParentOf',O2,M2)],M), fact(['p:isAuntOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X, Y],O1,M1,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', X, Y],O1,M1,_) \ fact(['p:isSiblingInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', Y, X],O1,M1,_) \ fact(['p:hasGreatAunt', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatAunt', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', Y, X],O1,M1,_) \ fact(['p:isGreatAuntOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatAuntOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Spouse', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isSpouseOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Spouse', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:isSpouseOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Spouse', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', _, X1],O1,M1,_) \ fact(['p:Marriage', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Mother', X],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,M1,_), fact(['p:isMotherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Mother', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Woman',O1,M1),('p:isMotherOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Mother', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:FirstCousin', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:hasParent', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isSiblingOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_), fact(['p:isParentOf', X2, X3],O6,M6,_), fact(['p:Person', X3],O7,M7,_) \ fact(['p:FirstCousin', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | check_pos_mark([('p:Person',O1,M1),('p:hasParent',O2,M2),('p:Person',O3,M3),('p:isSiblingOf',O4,M4),('p:Person',O5,M5),('p:isParentOf',O6,M6),('p:Person',O7,M7)],M), fact(['p:FirstCousin', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isMotherInLawOf', Y, X],O1,M1,_) \ fact(['p:hasMotherInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasMotherInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', Y, X],O1,M1,_) \ fact(['p:isMotherInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isMotherInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFamilyName', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,M1,_), fact(['p:hasFather', X1, X2],O2,M2,_) \ fact(['p:hasGrandfather', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasParent',O1,M1),('p:hasFather',O2,M2)],M), fact(['p:hasGrandfather', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:Son', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isSonOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Son', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:isSonOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Son', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X0, X1],O1,M1,_), fact(['p:isSiblingOf', X1, X2],O2,M2,_), fact(['p:isGreatGrandParentOf', X2, X3],O3,M3,_) \ fact(['p:isThirdCousinOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:hasGreatGrandParent',O1,M1),('p:isSiblingOf',O2,M2),('p:isGreatGrandParentOf',O3,M3)],M), fact(['p:isThirdCousinOf', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isGrandfatherOf', Y, X],O1,M1,_) \ fact(['p:hasGrandfather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandfather', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', Y, X],O1,M1,_) \ fact(['p:isGrandfatherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGrandfatherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X, Y],O1,M1,_) \ fact(['p:isSpouseOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Daughter', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isDaughterOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Daughter', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:isDaughterOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Daughter', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', X, Y],O1,M1,_) \ fact(['p:hasParentInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:MaleAncestor', X],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,M1,_), fact(['p:isAncestorOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:MaleAncestor', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Man',O1,M1),('p:isAncestorOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:MaleAncestor', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isFatherInLawOf', Y, X],O1,M1,_) \ fact(['p:hasFatherInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasFatherInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', Y, X],O1,M1,_) \ fact(['p:isFatherInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFatherInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, Y1],O1,M1,_), fact(['p:hasFather', X, Y2],O2,M2,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasFather',O1,M1),('p:hasFather',O2,M2)],M), fact(['owl:sameAs', Y1, Y2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X, Y],O1,M1,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', Y, X],O1,M1,_) \ fact(['p:brotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:brotherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', Y, X],O1,M1,_) \ fact(['p:hasBrother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasBrother', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X, _],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Parent', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isParentOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Parent', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:isParentOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Parent', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X, _],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', X, _],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', X, _],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Forefather', X],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,M1,_), fact(['p:isForefatherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Forefather', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Man',O1,M1),('p:isForefatherOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Forefather', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', X, _],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:SecondCousin', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:hasParent', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:hasParent', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_), fact(['p:isSiblingOf', X2, X3],O6,M6,_), fact(['p:Person', X3],O7,M7,_), fact(['p:isParentOf', X3, X4],O8,M8,_), fact(['p:Person', X4],O9,M9,_), fact(['p:isParentOf', X4, X5],O10,M10,_), fact(['p:Person', X5],O11,M11,_) \ fact(['p:SecondCousin', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11]) | check_pos_mark([('p:Person',O1,M1),('p:hasParent',O2,M2),('p:Person',O3,M3),('p:hasParent',O4,M4),('p:Person',O5,M5),('p:isSiblingOf',O6,M6),('p:Person',O7,M7),('p:isParentOf',O8,M8),('p:Person',O9,M9),('p:isParentOf',O10,M10),('p:Person',O11,M11)],M), fact(['p:SecondCousin', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', Y, X],O1,M1,_) \ fact(['p:isRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', Y, X],O1,M1,_) \ fact(['p:isSecondCousinOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSecondCousinOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGrandmotherOf', Y, X],O1,M1,_) \ fact(['p:hasGrandmother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandmother', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', Y, X],O1,M1,_) \ fact(['p:isGrandmotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGrandmotherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', X, Y],O1,M1,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Ancestor', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isAncestorOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Ancestor', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:isAncestorOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Ancestor', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', Y, X],O1,M1,_) \ fact(['p:isSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', X, Y],O1,M1,_) \ fact(['p:isAncestorOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', X, Y],O1,M1,_), fact(['p:isForemotherOf', Y, Z],O2,M2,_) \ fact(['p:isForemotherOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isForemotherOf',O1,M1),('p:isForemotherOf',O2,M2)],M), fact(['p:isForemotherOf', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, Y],O1,M1,_), fact(['p:hasForeFather', Y, Z],O2,M2,_) \ fact(['p:hasForeFather', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasForeFather',O1,M1),('p:hasForeFather',O2,M2)],M), fact(['p:hasForeFather', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', X, Y],O1,M1,_) \ fact(['p:isSpouseOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:knownAs', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X0, X1],O1,M1,_), fact(['p:hasFemalePartner', X1, X2],O2,M2,_) \ fact(['p:hasWife', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isMalePartnerIn',O1,M1),('p:hasFemalePartner',O2,M2)],M), fact(['p:hasWife', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X0, X1],O1,M1,_), fact(['p:hasMalePartner', X1, X2],O2,M2,_) \ fact(['p:hasHusband', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isFemalePartnerIn',O1,M1),('p:hasMalePartner',O2,M2)],M), fact(['p:hasHusband', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', X, Y],O1,M1,_) \ fact(['p:isSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', Y, X],O1,M1,_) \ fact(['p:isParentOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isParentOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:ParentInLaw', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isParentOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isSpouseOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_) \ fact(['p:ParentInLaw', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Person',O1,M1),('p:isParentOf',O2,M2),('p:Person',O3,M3),('p:isSpouseOf',O4,M4),('p:Person',O5,M5)],M), fact(['p:ParentInLaw', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:formerlyKnownAs', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, Y],O1,M1,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Cousin', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:hasAncestor', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isSiblingOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_), fact(['p:isParentOf', X2, X3],O6,M6,_), fact(['p:Person', X3],O7,M7,_) \ fact(['p:Cousin', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | check_pos_mark([('p:Person',O1,M1),('p:hasAncestor',O2,M2),('p:Person',O3,M3),('p:isSiblingOf',O4,M4),('p:Person',O5,M5),('p:isParentOf',O6,M6),('p:Person',O7,M7)],M), fact(['p:Cousin', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:GreatGrandparent', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isParentOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_), fact(['p:isParentOf', X2, X3],O6,M6,_), fact(['p:Person', X3],O7,M7,_) \ fact(['p:GreatGrandparent', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | check_pos_mark([('p:Person',O1,M1),('p:isParentOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5),('p:isParentOf',O6,M6),('p:Person',O7,M7)],M), fact(['p:GreatGrandparent', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', Y, X],O1,M1,_) \ fact(['p:hasUncle', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasUncle', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', Y, X],O1,M1,_) \ fact(['p:isUncleOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isUncleOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', X, _],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:formerlyKnownAs', X, Y],O1,M1,_) \ fact(['p:knownAs', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:knownAs', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', Y, X],O1,M1,_) \ fact(['p:isFirstCousinOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFirstCousinOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, Y],O1,M1,_), fact(['p:hasForeMother', Y, Z],O2,M2,_) \ fact(['p:hasForeMother', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasForeMother',O1,M1),('p:hasForeMother',O2,M2)],M), fact(['p:hasForeMother', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', Y, X],O1,M1,_) \ fact(['p:hasAunt', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAunt', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', Y, X],O1,M1,_) \ fact(['p:isAuntOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isAuntOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', X, _],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, Y],O1,M1,_) \ fact(['p:hasForeFather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasForeFather', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_) \ fact(['p:DomainEntity', X],add,_,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:FemaleDescendent', X],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,M1,_), fact(['p:hasAncestor', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:FemaleDescendent', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Woman',O1,M1),('p:hasAncestor',O2,M2),('p:Person',O3,M3)],M), fact(['p:FemaleDescendent', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasUncleInLaw', Y, X],O1,M1,_) \ fact(['p:isUncleInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isUncleInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', Y, X],O1,M1,_) \ fact(['p:hasUncleInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasUncleInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:FemaleAncestor', X],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,M1,_), fact(['p:isAncestorOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:FemaleAncestor', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Woman',O1,M1),('p:isAncestorOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:FemaleAncestor', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', _, X1],O1,M1,_) \ fact(['p:Marriage', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', X, Y1],O1,M1,_), fact(['p:hasGender', X, Y2],O2,M2,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasGender',O1,M1),('p:hasGender',O2,M2)],M), fact(['owl:sameAs', Y1, Y2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, Y],O1,M1,_), fact(['p:hasAncestor', Y, Z],O2,M2,_) \ fact(['p:hasAncestor', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasAncestor',O1,M1),('p:hasAncestor',O2,M2)],M), fact(['p:hasAncestor', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['p:Foremother', X],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,M1,_), fact(['p:isForemotherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Foremother', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Woman',O1,M1),('p:isForemotherOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Foremother', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', Y, X],O1,M1,_) \ fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', Y, X],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isAncestorOf', Y, X],O1,M1,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', Y, X],O1,M1,_) \ fact(['p:isAncestorOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X, Y],O1,M1,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X0, X1],O1,M1,_), fact(['p:grandParentOf', X1, X2],O2,M2,_) \ fact(['p:isGreatUncleOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:brotherOf',O1,M1),('p:grandParentOf',O2,M2)],M), fact(['p:isGreatUncleOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,M1,_), fact(['p:hasGrandfather', X1, X2],O2,M2,_) \ fact(['p:hasGreatGrandfather', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasParent',O1,M1),('p:hasGrandfather',O2,M2)],M), fact(['p:hasGreatGrandfather', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:Male', X],O1,M1,_) \ fact(['p:Sex', X],add,_,U) <=> member(del,[O1]) | fact(['p:Sex', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Female', X],O1,M1,_), fact(['p:Male', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:Female',O1,M1),('p:Male',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:Sex', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:Person',O1,M1),('p:Sex',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasBrotherInLaw', Y, X],O1,M1,_) \ fact(['p:isSisterInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSisterInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', Y, X],O1,M1,_) \ fact(['p:hasBrotherInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasBrotherInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,M1,_), fact(['p:isSiblingOf', X1, X2],O2,M2,_) \ fact(['p:isSiblingInLawOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isSpouseOf',O1,M1),('p:isSiblingOf',O2,M2)],M), fact(['p:isSiblingInLawOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:hasGender', X, X1],O2,M2,_), fact(['p:Male', X1],O3,M3,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:hasGender',O2,M2),('p:Male',O3,M3)],M), fact(['p:Man', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandParentOf', Y, X],O1,M1,_) \ fact(['p:hasGreatGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', Y, X],O1,M1,_) \ fact(['p:isGreatGrandParentOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatGrandParentOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', X, _],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Father', X],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,M1,_), fact(['p:isFatherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Father', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Man',O1,M1),('p:isFatherOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:Father', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:marriageYear', X, _],O1,M1,_) \ fact(['p:Marriage', X],add,_,U) <=> member(del,[O1]) | fact(['p:Marriage', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X, _],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X0, X1],O1,M1,_), fact(['p:isParentOf', X1, X2],O2,M2,_) \ fact(['p:isFirstCousinOnceRemovedOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isFirstCousinOf',O1,M1),('p:isParentOf',O2,M2)],M), fact(['p:isFirstCousinOnceRemovedOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:FatherInLaw', X],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,M1,_), fact(['p:isFatherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isSpouseOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_) \ fact(['p:FatherInLaw', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Man',O1,M1),('p:isFatherOf',O2,M2),('p:Person',O3,M3),('p:isSpouseOf',O4,M4),('p:Person',O5,M5)],M), fact(['p:FatherInLaw', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandfatherOf', Y, X],O1,M1,_) \ fact(['p:hasGreatGrandfather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandfather', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', Y, X],O1,M1,_) \ fact(['p:isGreatGrandfatherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatGrandfatherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, Y],O1,M1,_), fact(['p:isBloodRelationOf', Y, Z],O2,M2,_) \ fact(['p:isBloodRelationOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isBloodRelationOf',O1,M1),('p:isBloodRelationOf',O2,M2)],M), fact(['p:isBloodRelationOf', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['p:GreatGrandfather', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isFatherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_), fact(['p:isParentOf', X2, X3],O6,M6,_), fact(['p:Person', X3],O7,M7,_) \ fact(['p:GreatGrandfather', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | check_pos_mark([('p:Person',O1,M1),('p:isFatherOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5),('p:isParentOf',O6,M6),('p:Person',O7,M7)],M), fact(['p:GreatGrandfather', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X, Y],O1,M1,_) \ fact(['p:isPartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', X, Y],O1,M1,_) \ fact(['p:hasGreatGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasBrotherInLaw', Y, X],O1,M1,_) \ fact(['p:isBrotherInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBrotherInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', Y, X],O1,M1,_) \ fact(['p:hasBrotherInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasBrotherInLaw', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Grandmother', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isMotherOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_) \ fact(['p:Grandmother', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Person',O1,M1),('p:isMotherOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5)],M), fact(['p:Grandmother', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,M1,_), fact(['p:hasMother', X1, X2],O2,M2,_) \ fact(['p:hasMotherInLaw', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isSpouseOf',O1,M1),('p:hasMother',O2,M2)],M), fact(['p:hasMotherInLaw', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:Husband', X],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,M1,_), fact(['p:isMalePartnerIn', X, X1],O2,M2,_), fact(['p:Marriage', X1],O3,M3,_), fact(['p:hasFemalePartner', X1, X2],O4,M4,_), fact(['p:Woman', X2],O5,M5,_) \ fact(['p:Husband', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Man',O1,M1),('p:isMalePartnerIn',O2,M2),('p:Marriage',O3,M3),('p:hasFemalePartner',O4,M4),('p:Woman',O5,M5)],M), fact(['p:Husband', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFemalePartner', Y, X],O1,M1,_) \ fact(['p:isFemalePartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFemalePartnerIn', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', Y, X],O1,M1,_) \ fact(['p:hasFemalePartner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasFemalePartner', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:InLaw', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isInLawOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:InLaw', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:isInLawOf',O2,M2),('p:Person',O3,M3)],M), fact(['p:InLaw', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', Y, X],O1,M1,_) \ fact(['p:isSiblingInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Descendent', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:hasAncestor', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:Descendent', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Person',O1,M1),('p:hasAncestor',O2,M2),('p:Person',O3,M3)],M), fact(['p:Descendent', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', X, Y],O1,M1,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,M1,_), fact(['p:Person', X],O2,M2,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:Marriage',O1,M1),('p:Person',O2,M2)],M), fact(['owl:Nothing', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', X, Y],O1,M1,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, Y],O1,M1,_) \ fact(['p:isRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:PersonWithManySibling', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', _, X1],O1,M1,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:grandParentOf', Y, X],O1,M1,_) \ fact(['p:hasGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', Y, X],O1,M1,_) \ fact(['p:grandParentOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:grandParentOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:MaleDescendent', X],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,M1,_), fact(['p:hasAncestor', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_) \ fact(['p:MaleDescendent', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('p:Man',O1,M1),('p:hasAncestor',O2,M2),('p:Person',O3,M3)],M), fact(['p:MaleDescendent', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isSonOf', X0, X1],O1,M1,_), fact(['p:isSiblingOf', X1, X2],O2,M2,_) \ fact(['p:isNephewOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isSonOf',O1,M1),('p:isSiblingOf',O2,M2)],M), fact(['p:isNephewOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', Y, X],O1,M1,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,M1,_), fact(['p:hasGrandmother', X1, X2],O2,M2,_) \ fact(['p:hasGreatGrandmother', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:hasParent',O1,M1),('p:hasGrandmother',O2,M2)],M), fact(['p:hasGreatGrandmother', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', Y, X],O1,M1,_) \ fact(['p:hasForeMother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasForeMother', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', Y, X],O1,M1,_) \ fact(['p:isForemotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isForemotherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', _, X1],O1,M1,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', X, Y],O1,M1,_) \ fact(['p:isSiblingInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:ParentOfSmallFamily', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:ParentOfLargeFamily', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Aunt', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:sisterOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_) \ fact(['p:Aunt', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | check_pos_mark([('p:Person',O1,M1),('p:sisterOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5)],M), fact(['p:Aunt', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isMotherOf', Y, X],O1,M1,_) \ fact(['p:hasMother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasMother', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', Y, X],O1,M1,_) \ fact(['p:isMotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isMotherOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', Y, X],O1,M1,_) \ fact(['p:isThirdCousinOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isThirdCousinOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isWifeOf', Y, X],O1,M1,_) \ fact(['p:hasWife', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasWife', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', Y, X],O1,M1,_) \ fact(['p:isWifeOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isWifeOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', X, _],O1,M1,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', X, _],O1,M1,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X, Y],O1,M1,_) \ fact(['p:isPartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isDaughterOf', X0, X1],O1,M1,_), fact(['p:isSiblingOf', X1, X2],O2,M2,_) \ fact(['p:isNieceOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isDaughterOf',O1,M1),('p:isSiblingOf',O2,M2)],M), fact(['p:isNieceOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X0, X1],O1,M1,_), fact(['p:grandParentOf', X1, X2],O2,M2,_) \ fact(['p:isGreatAuntOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:sisterOf',O1,M1),('p:grandParentOf',O2,M2)],M), fact(['p:isGreatAuntOf', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', _, X1],O1,M1,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:GreatGreatGrandparent', X],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,M1,_), fact(['p:isParentOf', X, X1],O2,M2,_), fact(['p:Person', X1],O3,M3,_), fact(['p:isParentOf', X1, X2],O4,M4,_), fact(['p:Person', X2],O5,M5,_), fact(['p:isParentOf', X2, X3],O6,M6,_), fact(['p:Person', X3],O7,M7,_), fact(['p:isParentOf', X3, X4],O8,M8,_), fact(['p:Person', X4],O9,M9,_) \ fact(['p:GreatGreatGrandparent', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9]) | check_pos_mark([('p:Person',O1,M1),('p:isParentOf',O2,M2),('p:Person',O3,M3),('p:isParentOf',O4,M4),('p:Person',O5,M5),('p:isParentOf',O6,M6),('p:Person',O7,M7),('p:isParentOf',O8,M8),('p:Person',O9,M9)],M), fact(['p:GreatGreatGrandparent', X],del,M,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', X, Y],O1,M1,_) \ fact(['p:hasGreatGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, Y],O1,M1,_), fact(['p:isSiblingOf', Y, Z],O2,M2,_) \ fact(['p:isSiblingOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('p:isSiblingOf',O1,M1),('p:isSiblingOf',O2,M2)],M), fact(['p:isSiblingOf', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', X, _],O1,M1,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],del,M1,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact(['p:hasParent', X, Y],add,M1,_), fact(['p:maleInFamilinx', Y],add,M2,_) \ fact(['p:hasFather', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasFather', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X, Y],add,M1,_), fact(['p:femaleInFamilinx', Y],add,M2,_) \ fact(['p:hasMother', X, Y],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasMother', X, Y],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasSon', X, Y],add,M1,_) \ fact(['p:hasChild', X, Y],del,_,U) <=> true | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isWifeOf', X0, X1],add,M1,_), fact(['p:brotherOf', X1, X2],add,M2,_), fact(['p:isParentOf', X2, X3],add,M3,_) \ fact(['p:isAuntInLawOf', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:isAuntInLawOf', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasDaughter', X, Y],add,M1,_) \ fact(['p:hasChild', X, Y],del,_,U) <=> true | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGreatUncleOf', Y, X],add,M1,_) \ fact(['p:hasGreatUncle', X, Y],del,_,U) <=> true | fact(['p:hasGreatUncle', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatUncle', Y, X],add,M1,_) \ fact(['p:isGreatUncleOf', X, Y],del,_,U) <=> true | fact(['p:isGreatUncleOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', X0, X1],add,M1,_), fact(['p:isSiblingOf', X1, X2],add,M2,_), fact(['p:grandParentOf', X2, X3],add,M3,_) \ fact(['p:isSecondCousinOf', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:isSecondCousinOf', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandmother', X, Y],add,M1,_) \ fact(['p:hasGrandParent', X, Y],del,_,U) <=> true | fact(['p:hasGrandParent', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:alsoKnownAs', X, Y],add,M1,_) \ fact(['p:knownAs', X, Y],del,_,U) <=> true | fact(['p:knownAs', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:directSiblingOf', Y, X],add,M1,_) \ fact(['p:directSiblingOf', X, Y],del,_,U) <=> true | fact(['p:directSiblingOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasBirthYear', X, Y1],add,M1,_), fact(['p:hasBirthYear', X, Y2],add,M2,_) \ fact(['owl:sameAs', Y1, Y2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasHusband', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isInLawOf', X, Y],add,M1,_) \ fact(['p:isRelationOf', X, Y],del,_,U) <=> true | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isChildOf', Y, X],add,M1,_) \ fact(['p:hasChild', X, Y],del,_,U) <=> true | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasChild', Y, X],add,M1,_) \ fact(['p:isChildOf', X, Y],del,_,U) <=> true | fact(['p:isChildOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasParentInLaw', Y, X],add,M1,_) \ fact(['p:isParentInLawOf', X, Y],del,_,U) <=> true | fact(['p:isParentInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isParentInLawOf', Y, X],add,M1,_) \ fact(['p:hasParentInLaw', X, Y],del,_,U) <=> true | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isForefatherOf', X, Y],add,M1,_), fact(['p:isForefatherOf', Y, Z],add,M2,_) \ fact(['p:isForefatherOf', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isForefatherOf', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasAunt', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatUncle', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasDeathYear', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasMotherInLaw', X, Y],add,M1,_) \ fact(['p:hasParentInLaw', X, Y],del,_,U) <=> true | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isAuntInLawOf', X, Y],add,M1,_) \ fact(['p:isInLawOf', X, Y],del,_,U) <=> true | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X0, X1],add,M1,_), fact(['p:hasFather', X1, X2],add,M2,_) \ fact(['p:hasFatherInLaw', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasFatherInLaw', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', X, Y],add,M1,_) \ fact(['p:hasAncestor', X, Y],del,_,U) <=> true | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', X, Y1],add,M1,_), fact(['p:hasMother', X, Y2],add,M2,_) \ fact(['owl:sameAs', Y1, Y2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasAuntInLaw', Y, X],add,M1,_) \ fact(['p:hasAuntInLaw', X, Y],del,_,U) <=> true | fact(['p:hasAuntInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAuntInLaw', Y, X],add,M1,_) \ fact(['p:hasAuntInLaw', X, Y],del,_,U) <=> true | fact(['p:hasAuntInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Grandparent', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isParentOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_) \ fact(['p:Grandparent', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Grandparent', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isAuntInLawOf', X, _],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasUncle', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:alsoKnownAs', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:GreatUncle', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:brotherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_), fact(['p:isParentOf', X2, X3],add,M6,_), fact(['p:Person', X3],add,M7,_) \ fact(['p:GreatUncle', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:GreatUncle', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOnceRemovedOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isAuntOf', X, _],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasSon', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Marriage', X],add,M1,_) \ fact(['p:DomainEntity', X],del,_,U) <=> true | fact(['p:DomainEntity', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAunt', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', X0, X1],add,M1,_), fact(['p:isParentOf', X1, X2],add,M2,_) \ fact(['p:isUncleOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isUncleOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isPartnerIn', _, X1],add,M1,_) \ fact(['p:Marriage', X1],del,_,U) <=> true | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGreatGrandmotherOf', Y, X],add,M1,_) \ fact(['p:hasGreatGrandmother', X, Y],del,_,U) <=> true | fact(['p:hasGreatGrandmother', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandmother', Y, X],add,M1,_) \ fact(['p:isGreatGrandmotherOf', X, Y],del,_,U) <=> true | fact(['p:isGreatGrandmotherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasBirthYear', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:MotherInLaw', X],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,M1,_), fact(['p:isMotherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isSpouseOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_) \ fact(['p:MotherInLaw', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:MotherInLaw', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasMalePartner', Y, X],add,M1,_) \ fact(['p:isMalePartnerIn', X, Y],del,_,U) <=> true | fact(['p:isMalePartnerIn', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', Y, X],add,M1,_) \ fact(['p:hasMalePartner', X, Y],del,_,U) <=> true | fact(['p:hasMalePartner', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', X, _],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isForefatherOf', X, Y],add,M1,_) \ fact(['p:isAncestorOf', X, Y],del,_,U) <=> true | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Grandfather', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isFatherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_) \ fact(['p:Grandfather', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Grandfather', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:Female', X],add,M1,_) \ fact(['p:Sex', X],del,_,U) <=> true | fact(['p:Sex', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Uncle', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:brotherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_) \ fact(['p:Uncle', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Uncle', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isNephewOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isRelationOf', X, Y],add,M1,_), fact(['p:isRelationOf', Y, Z],add,M2,_) \ fact(['p:isRelationOf', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isRelationOf', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandmother', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isRelationOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', X, _],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasSister', Y, X],add,M1,_) \ fact(['p:sisterOf', X, Y],del,_,U) <=> true | fact(['p:sisterOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', Y, X],add,M1,_) \ fact(['p:hasSister', X, Y],del,_,U) <=> true | fact(['p:hasSister', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:directSiblingOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isThirdCousinOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGender', _, X1],add,M1,_) \ fact(['p:Sex', X1],del,_,U) <=> true | fact(['p:Sex', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isDaughterOf', Y, X],add,M1,_) \ fact(['p:hasDaughter', X, Y],del,_,U) <=> true | fact(['p:hasDaughter', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasDaughter', Y, X],add,M1,_) \ fact(['p:isDaughterOf', X, Y],del,_,U) <=> true | fact(['p:isDaughterOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandfather', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingInLawOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSonOf', Y, X],add,M1,_) \ fact(['p:hasSon', X, Y],del,_,U) <=> true | fact(['p:hasSon', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasSon', Y, X],add,M1,_) \ fact(['p:isSonOf', X, Y],del,_,U) <=> true | fact(['p:isSonOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Sex', X],add,M1,_) \ fact(['p:DomainEntity', X],del,_,U) <=> true | fact(['p:DomainEntity', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isHusbandOf', Y, X],add,M1,_) \ fact(['p:hasHusband', X, Y],del,_,U) <=> true | fact(['p:hasHusband', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasHusband', Y, X],add,M1,_) \ fact(['p:isHusbandOf', X, Y],del,_,U) <=> true | fact(['p:isHusbandOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isUncleInLawOf', X, Y],add,M1,_) \ fact(['p:isInLawOf', X, Y],del,_,U) <=> true | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isParentOf', X0, X1],add,M1,_), fact(['p:isSpouseOf', X1, X2],add,M2,_) \ fact(['p:isParentInLawOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isParentInLawOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isBrotherInLawOf', X, _],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', X0, X1],add,M1,_), fact(['p:hasBrother', X1, X2],add,M2,_) \ fact(['p:isBrotherInLawOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isBrotherInLawOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:BloodRelation', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isBloodRelationOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:BloodRelation', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:BloodRelation', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:Marriage', X],add,M1,_), fact(['p:Sex', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasFatherInLaw', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isParentOf', X, Y],add,M1,_) \ fact(['p:hasChild', X, Y],del,_,U) <=> true | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasChild', X, Y],add,M1,_) \ fact(['p:isParentOf', X, Y],del,_,U) <=> true | fact(['p:isParentOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', X, Y],add,M1,_) \ fact(['p:directSiblingOf', X, Y],del,_,U) <=> true | fact(['p:directSiblingOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandfather', X, Y],add,M1,_) \ fact(['p:hasGrandParent', X, Y],del,_,U) <=> true | fact(['p:hasGrandParent', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasUncle', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', X, Y],add,M1,_) \ fact(['p:hasForeMother', X, Y],del,_,U) <=> true | fact(['p:hasForeMother', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,M1,_), fact(['p:hasMother', X1, X2],add,M2,_) \ fact(['p:hasGrandmother', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasGrandmother', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', X0, X1],add,M1,_), fact(['p:hasBrother', X1, X2],add,M2,_) \ fact(['p:isSisterInLawOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isSisterInLawOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isAuntInLawOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Wife', X],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,M1,_), fact(['p:isFemalePartnerIn', X, X1],add,M2,_), fact(['p:Marriage', X1],add,M3,_), fact(['p:hasMalePartner', X1, X2],add,M4,_), fact(['p:Man', X2],add,M5,_) \ fact(['p:Wife', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Wife', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasDeathYear', X, Y1],add,M1,_), fact(['p:hasDeathYear', X, Y2],add,M2,_) \ fact(['owl:sameAs', Y1, Y2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasPartner', Y, X],add,M1,_) \ fact(['p:isPartnerIn', X, Y],del,_,U) <=> true | fact(['p:isPartnerIn', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isPartnerIn', Y, X],add,M1,_) \ fact(['p:hasPartner', X, Y],del,_,U) <=> true | fact(['p:hasPartner', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', X, Y],add,M1,_) \ fact(['p:directSiblingOf', X, Y],del,_,U) <=> true | fact(['p:directSiblingOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isForefatherOf', Y, X],add,M1,_) \ fact(['p:hasForeFather', X, Y],del,_,U) <=> true | fact(['p:hasForeFather', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', Y, X],add,M1,_) \ fact(['p:isForefatherOf', X, Y],del,_,U) <=> true | fact(['p:isForefatherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFatherOf', Y, X],add,M1,_) \ fact(['p:hasFather', X, Y],del,_,U) <=> true | fact(['p:hasFather', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', Y, X],add,M1,_) \ fact(['p:isFatherOf', X, Y],del,_,U) <=> true | fact(['p:isFatherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isHusbandOf', X0, X1],add,M1,_), fact(['p:sisterOf', X1, X2],add,M2,_), fact(['p:isParentOf', X2, X3],add,M3,_) \ fact(['p:isUncleInLawOf', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:isUncleInLawOf', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:ThirdCousin', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:hasParent', X, X1],add,M2,_), fact(['p:hasParent', X1, X2],add,M3,_), fact(['p:Person', X2],add,M4,_), fact(['p:hasParent', X2, X3],add,M5,_), fact(['p:Person', X3],add,M6,_), fact(['p:isSiblingOf', X3, X4],add,M7,_), fact(['p:Person', X4],add,M8,_), fact(['p:isParentOf', X4, X5],add,M9,_), fact(['p:Person', X5],add,M10,_), fact(['p:isParentOf', X5, X6],add,M11,_), fact(['p:Person', X6],add,M12,_), fact(['p:isParentOf', X6, X7],add,M13,_), fact(['p:Person', X7],add,M14,_) \ fact(['p:ThirdCousin', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5,M6,M7,M8,M9,M10,M11,M12,M13,M14],M), fact(['p:ThirdCousin', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:hasGender', X, X1],add,M2,_), fact(['p:Female', X1],add,M3,_) \ fact(['p:Woman', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Woman', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,M1,_), fact(['p:isSiblingOf', X1, X2],add,M2,_), fact(['p:isParentOf', X2, X3],add,M3,_) \ fact(['p:isFirstCousinOf', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:isFirstCousinOf', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', X, Y],add,M1,_) \ fact(['p:hasAncestor', X, Y],del,_,U) <=> true | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', Y, X],add,M1,_) \ fact(['p:isSpouseOf', X, Y],del,_,U) <=> true | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', X0, X1],add,M1,_), fact(['p:isParentOf', X1, X2],add,M2,_) \ fact(['p:isAuntOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isAuntOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', X, Y],add,M1,_) \ fact(['p:hasAncestor', X, Y],del,_,U) <=> true | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSisterInLawOf', X, Y],add,M1,_) \ fact(['p:isSiblingInLawOf', X, Y],del,_,U) <=> true | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGreatAuntOf', Y, X],add,M1,_) \ fact(['p:hasGreatAunt', X, Y],del,_,U) <=> true | fact(['p:hasGreatAunt', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatAunt', Y, X],add,M1,_) \ fact(['p:isGreatAuntOf', X, Y],del,_,U) <=> true | fact(['p:isGreatAuntOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Spouse', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isSpouseOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Spouse', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Spouse', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', _, X1],add,M1,_) \ fact(['p:Marriage', X1],del,_,U) <=> true | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isBrotherInLawOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Mother', X],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,M1,_), fact(['p:isMotherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Mother', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Mother', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasDaughter', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isUncleOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:FirstCousin', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:hasParent', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isSiblingOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_), fact(['p:isParentOf', X2, X3],add,M6,_), fact(['p:Person', X3],add,M7,_) \ fact(['p:FirstCousin', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:FirstCousin', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isMotherInLawOf', Y, X],add,M1,_) \ fact(['p:hasMotherInLaw', X, Y],del,_,U) <=> true | fact(['p:hasMotherInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasMotherInLaw', Y, X],add,M1,_) \ fact(['p:isMotherInLawOf', X, Y],del,_,U) <=> true | fact(['p:isMotherInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGreatAuntOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFamilyName', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,M1,_), fact(['p:hasFather', X1, X2],add,M2,_) \ fact(['p:hasGrandfather', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasGrandfather', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:Son', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isSonOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Son', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Son', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', X0, X1],add,M1,_), fact(['p:isSiblingOf', X1, X2],add,M2,_), fact(['p:isGreatGrandParentOf', X2, X3],add,M3,_) \ fact(['p:isThirdCousinOf', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:isThirdCousinOf', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isGrandfatherOf', Y, X],add,M1,_) \ fact(['p:hasGrandfather', X, Y],del,_,U) <=> true | fact(['p:hasGrandfather', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandfather', Y, X],add,M1,_) \ fact(['p:isGrandfatherOf', X, Y],del,_,U) <=> true | fact(['p:isGrandfatherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', X, Y],add,M1,_) \ fact(['p:isSpouseOf', X, Y],del,_,U) <=> true | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Daughter', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isDaughterOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Daughter', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Daughter', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasFatherInLaw', X, Y],add,M1,_) \ fact(['p:hasParentInLaw', X, Y],del,_,U) <=> true | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:MaleAncestor', X],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,M1,_), fact(['p:isAncestorOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:MaleAncestor', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:MaleAncestor', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isFatherInLawOf', Y, X],add,M1,_) \ fact(['p:hasFatherInLaw', X, Y],del,_,U) <=> true | fact(['p:hasFatherInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFatherInLaw', Y, X],add,M1,_) \ fact(['p:isFatherInLawOf', X, Y],del,_,U) <=> true | fact(['p:isFatherInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasDaughter', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', X, Y1],add,M1,_), fact(['p:hasFather', X, Y2],add,M2,_) \ fact(['owl:sameAs', Y1, Y2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X, Y],add,M1,_) \ fact(['p:isInLawOf', X, Y],del,_,U) <=> true | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasBrother', Y, X],add,M1,_) \ fact(['p:brotherOf', X, Y],del,_,U) <=> true | fact(['p:brotherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', Y, X],add,M1,_) \ fact(['p:hasBrother', X, Y],del,_,U) <=> true | fact(['p:hasBrother', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', X, _],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Parent', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isParentOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Parent', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Parent', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', X, _],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasSon', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGreatAuntOf', X, _],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isNephewOf', X, _],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Forefather', X],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,M1,_), fact(['p:isForefatherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Forefather', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Forefather', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isNieceOf', X, _],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isInLawOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:SecondCousin', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:hasParent', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:hasParent', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_), fact(['p:isSiblingOf', X2, X3],add,M6,_), fact(['p:Person', X3],add,M7,_), fact(['p:isParentOf', X3, X4],add,M8,_), fact(['p:Person', X4],add,M9,_), fact(['p:isParentOf', X4, X5],add,M10,_), fact(['p:Person', X5],add,M11,_) \ fact(['p:SecondCousin', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5,M6,M7,M8,M9,M10,M11],M), fact(['p:SecondCousin', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasChild', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isRelationOf', Y, X],add,M1,_) \ fact(['p:isRelationOf', X, Y],del,_,U) <=> true | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSecondCousinOf', Y, X],add,M1,_) \ fact(['p:isSecondCousinOf', X, Y],del,_,U) <=> true | fact(['p:isSecondCousinOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isNieceOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGrandmotherOf', Y, X],add,M1,_) \ fact(['p:hasGrandmother', X, Y],del,_,U) <=> true | fact(['p:hasGrandmother', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandmother', Y, X],add,M1,_) \ fact(['p:isGrandmotherOf', X, Y],del,_,U) <=> true | fact(['p:isGrandmotherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingInLawOf', X, Y],add,M1,_) \ fact(['p:isInLawOf', X, Y],del,_,U) <=> true | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Ancestor', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isAncestorOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Ancestor', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Ancestor', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatAunt', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', Y, X],add,M1,_) \ fact(['p:isSiblingOf', X, Y],del,_,U) <=> true | fact(['p:isSiblingOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isForemotherOf', X, Y],add,M1,_) \ fact(['p:isAncestorOf', X, Y],del,_,U) <=> true | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isForemotherOf', X, Y],add,M1,_), fact(['p:isForemotherOf', Y, Z],add,M2,_) \ fact(['p:isForemotherOf', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isForemotherOf', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasForeFather', X, Y],add,M1,_), fact(['p:hasForeFather', Y, Z],add,M2,_) \ fact(['p:hasForeFather', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasForeFather', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasHusband', X, Y],add,M1,_) \ fact(['p:isSpouseOf', X, Y],del,_,U) <=> true | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isParentInLawOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:knownAs', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasBrother', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGreatUncleOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', X0, X1],add,M1,_), fact(['p:hasFemalePartner', X1, X2],add,M2,_) \ fact(['p:hasWife', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasWife', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', X0, X1],add,M1,_), fact(['p:hasMalePartner', X1, X2],add,M2,_) \ fact(['p:hasHusband', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasHusband', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:directSiblingOf', X, Y],add,M1,_) \ fact(['p:isSiblingOf', X, Y],del,_,U) <=> true | fact(['p:isSiblingOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasMotherInLaw', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', Y, X],add,M1,_) \ fact(['p:isParentOf', X, Y],del,_,U) <=> true | fact(['p:isParentOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:ParentInLaw', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isParentOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isSpouseOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_) \ fact(['p:ParentInLaw', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:ParentInLaw', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:formerlyKnownAs', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X, Y],add,M1,_) \ fact(['p:hasAncestor', X, Y],del,_,U) <=> true | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Cousin', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:hasAncestor', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isSiblingOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_), fact(['p:isParentOf', X2, X3],add,M6,_), fact(['p:Person', X3],add,M7,_) \ fact(['p:Cousin', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:Cousin', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:GreatGrandparent', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isParentOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_), fact(['p:isParentOf', X2, X3],add,M6,_), fact(['p:Person', X3],add,M7,_) \ fact(['p:GreatGrandparent', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:GreatGrandparent', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isUncleOf', Y, X],add,M1,_) \ fact(['p:hasUncle', X, Y],del,_,U) <=> true | fact(['p:hasUncle', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasUncle', Y, X],add,M1,_) \ fact(['p:isUncleOf', X, Y],del,_,U) <=> true | fact(['p:isUncleOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasHusband', X, _],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:formerlyKnownAs', X, Y],add,M1,_) \ fact(['p:knownAs', X, Y],del,_,U) <=> true | fact(['p:knownAs', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', Y, X],add,M1,_) \ fact(['p:isFirstCousinOf', X, Y],del,_,U) <=> true | fact(['p:isFirstCousinOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOnceRemovedOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandfather', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', X, Y],add,M1,_), fact(['p:hasForeMother', Y, Z],add,M2,_) \ fact(['p:hasForeMother', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasForeMother', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isAuntOf', Y, X],add,M1,_) \ fact(['p:hasAunt', X, Y],del,_,U) <=> true | fact(['p:hasAunt', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAunt', Y, X],add,M1,_) \ fact(['p:isAuntOf', X, Y],del,_,U) <=> true | fact(['p:isAuntOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isUncleOf', X, _],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', X, Y],add,M1,_) \ fact(['p:hasForeFather', X, Y],del,_,U) <=> true | fact(['p:hasForeFather', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_) \ fact(['p:DomainEntity', X],del,_,U) <=> true | fact(['p:DomainEntity', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatUncle', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isUncleInLawOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:FemaleDescendent', X],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,M1,_), fact(['p:hasAncestor', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:FemaleDescendent', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:FemaleDescendent', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandmother', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isPartnerIn', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasUncleInLaw', Y, X],add,M1,_) \ fact(['p:isUncleInLawOf', X, Y],del,_,U) <=> true | fact(['p:isUncleInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isUncleInLawOf', Y, X],add,M1,_) \ fact(['p:hasUncleInLaw', X, Y],del,_,U) <=> true | fact(['p:hasUncleInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:FemaleAncestor', X],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,M1,_), fact(['p:isAncestorOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:FemaleAncestor', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:FemaleAncestor', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isNieceOf', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', _, X1],add,M1,_) \ fact(['p:Marriage', X1],del,_,U) <=> true | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGender', X, Y1],add,M1,_), fact(['p:hasGender', X, Y2],add,M2,_) \ fact(['owl:sameAs', Y1, Y2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasBrother', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', X, Y],add,M1,_), fact(['p:hasAncestor', Y, Z],add,M2,_) \ fact(['p:hasAncestor', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasAncestor', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['p:Foremother', X],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Woman', X],add,M1,_), fact(['p:isForemotherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Foremother', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Foremother', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOnceRemovedOf', Y, X],add,M1,_) \ fact(['p:isFirstCousinOnceRemovedOf', X, Y],del,_,U) <=> true | fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:directSiblingOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', Y, X],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isAncestorOf', Y, X],add,M1,_) \ fact(['p:hasAncestor', X, Y],del,_,U) <=> true | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', Y, X],add,M1,_) \ fact(['p:isAncestorOf', X, Y],del,_,U) <=> true | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasUncle', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', X, Y],add,M1,_) \ fact(['p:hasAncestor', X, Y],del,_,U) <=> true | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', X0, X1],add,M1,_), fact(['p:grandParentOf', X1, X2],add,M2,_) \ fact(['p:isGreatUncleOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isGreatUncleOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,M1,_), fact(['p:hasGrandfather', X1, X2],add,M2,_) \ fact(['p:hasGreatGrandfather', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasGreatGrandfather', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:Male', X],add,M1,_) \ fact(['p:Sex', X],del,_,U) <=> true | fact(['p:Sex', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Female', X],add,M1,_), fact(['p:Male', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasMotherInLaw', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatAunt', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:Sex', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isRelationOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSecondCousinOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasBrotherInLaw', Y, X],add,M1,_) \ fact(['p:isSisterInLawOf', X, Y],del,_,U) <=> true | fact(['p:isSisterInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSisterInLawOf', Y, X],add,M1,_) \ fact(['p:hasBrotherInLaw', X, Y],del,_,U) <=> true | fact(['p:hasBrotherInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X0, X1],add,M1,_), fact(['p:isSiblingOf', X1, X2],add,M2,_) \ fact(['p:isSiblingInLawOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isSiblingInLawOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:hasGender', X, X1],add,M2,_), fact(['p:Male', X1],add,M3,_) \ fact(['p:Man', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Man', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isGreatGrandParentOf', Y, X],add,M1,_) \ fact(['p:hasGreatGrandParent', X, Y],del,_,U) <=> true | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', Y, X],add,M1,_) \ fact(['p:isGreatGrandParentOf', X, Y],del,_,U) <=> true | fact(['p:isGreatGrandParentOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatAunt', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isUncleInLawOf', X, _],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isThirdCousinOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Father', X],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,M1,_), fact(['p:isFatherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Father', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Father', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isNephewOf', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAunt', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasAncestor', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingInLawOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:marriageYear', X, _],add,M1,_) \ fact(['p:Marriage', X],del,_,U) <=> true | fact(['p:Marriage', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:brotherOf', X, _],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', X0, X1],add,M1,_), fact(['p:isParentOf', X1, X2],add,M2,_) \ fact(['p:isFirstCousinOnceRemovedOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isFirstCousinOnceRemovedOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:FatherInLaw', X],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,M1,_), fact(['p:isFatherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isSpouseOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_) \ fact(['p:FatherInLaw', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:FatherInLaw', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandParent', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGreatGrandfatherOf', Y, X],add,M1,_) \ fact(['p:hasGreatGrandfather', X, Y],del,_,U) <=> true | fact(['p:hasGreatGrandfather', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandfather', Y, X],add,M1,_) \ fact(['p:isGreatGrandfatherOf', X, Y],del,_,U) <=> true | fact(['p:isGreatGrandfatherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isUncleOf', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isInLawOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatUncle', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', X, Y],add,M1,_), fact(['p:isBloodRelationOf', Y, Z],add,M2,_) \ fact(['p:isBloodRelationOf', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isBloodRelationOf', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['p:GreatGrandfather', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isFatherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_), fact(['p:isParentOf', X2, X3],add,M6,_), fact(['p:Person', X3],add,M7,_) \ fact(['p:GreatGrandfather', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:GreatGrandfather', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isFirstCousinOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isMalePartnerIn', X, Y],add,M1,_) \ fact(['p:isPartnerIn', X, Y],del,_,U) <=> true | fact(['p:isPartnerIn', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSecondCousinOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandmother', X, Y],add,M1,_) \ fact(['p:hasGreatGrandParent', X, Y],del,_,U) <=> true | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasBrotherInLaw', Y, X],add,M1,_) \ fact(['p:isBrotherInLawOf', X, Y],del,_,U) <=> true | fact(['p:isBrotherInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isBrotherInLawOf', Y, X],add,M1,_) \ fact(['p:hasBrotherInLaw', X, Y],del,_,U) <=> true | fact(['p:hasBrotherInLaw', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Grandmother', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isMotherOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_) \ fact(['p:Grandmother', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Grandmother', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isSpouseOf', X0, X1],add,M1,_), fact(['p:hasMother', X1, X2],add,M2,_) \ fact(['p:hasMotherInLaw', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasMotherInLaw', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:Husband', X],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,M1,_), fact(['p:isMalePartnerIn', X, X1],add,M2,_), fact(['p:Marriage', X1],add,M3,_), fact(['p:hasFemalePartner', X1, X2],add,M4,_), fact(['p:Woman', X2],add,M5,_) \ fact(['p:Husband', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Husband', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandmother', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isThirdCousinOf', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGender', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFemalePartner', Y, X],add,M1,_) \ fact(['p:isFemalePartnerIn', X, Y],del,_,U) <=> true | fact(['p:isFemalePartnerIn', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', Y, X],add,M1,_) \ fact(['p:hasFemalePartner', X, Y],del,_,U) <=> true | fact(['p:hasFemalePartner', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:InLaw', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isInLawOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:InLaw', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:InLaw', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingInLawOf', Y, X],add,M1,_) \ fact(['p:isSiblingInLawOf', X, Y],del,_,U) <=> true | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Descendent', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:hasAncestor', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:Descendent', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:Descendent', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isParentInLawOf', X, Y],add,M1,_) \ fact(['p:isInLawOf', X, Y],del,_,U) <=> true | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Marriage', X],add,M1,_), fact(['p:Person', X],add,M2,_) \ fact(['owl:Nothing', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isSecondCousinOf', X, Y],add,M1,_) \ fact(['p:isBloodRelationOf', X, Y],del,_,U) <=> true | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandfather', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', X, Y],add,M1,_) \ fact(['p:isRelationOf', X, Y],del,_,U) <=> true | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:PersonWithManySibling', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFather', _, X1],add,M1,_) \ fact(['p:Man', X1],del,_,U) <=> true | fact(['p:Man', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:grandParentOf', Y, X],add,M1,_) \ fact(['p:hasGrandParent', X, Y],del,_,U) <=> true | fact(['p:hasGrandParent', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandParent', Y, X],add,M1,_) \ fact(['p:grandParentOf', X, Y],del,_,U) <=> true | fact(['p:grandParentOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:MaleDescendent', X],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Man', X],add,M1,_), fact(['p:hasAncestor', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_) \ fact(['p:MaleDescendent', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['p:MaleDescendent', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isSonOf', X0, X1],add,M1,_), fact(['p:isSiblingOf', X1, X2],add,M2,_) \ fact(['p:isNephewOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isNephewOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isInLawOf', Y, X],add,M1,_) \ fact(['p:isInLawOf', X, Y],del,_,U) <=> true | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasParent', X0, X1],add,M1,_), fact(['p:hasGrandmother', X1, X2],add,M2,_) \ fact(['p:hasGreatGrandmother', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:hasGreatGrandmother', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isForemotherOf', Y, X],add,M1,_) \ fact(['p:hasForeMother', X, Y],del,_,U) <=> true | fact(['p:hasForeMother', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasForeMother', Y, X],add,M1,_) \ fact(['p:isForemotherOf', X, Y],del,_,U) <=> true | fact(['p:isForemotherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandmother', _, X1],add,M1,_) \ fact(['p:Woman', X1],del,_,U) <=> true | fact(['p:Woman', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isBrotherInLawOf', X, Y],add,M1,_) \ fact(['p:isSiblingInLawOf', X, Y],del,_,U) <=> true | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:ParentOfSmallFamily', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:ParentOfLargeFamily', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Aunt', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:sisterOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_) \ fact(['p:Aunt', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Aunt', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isMotherOf', Y, X],add,M1,_) \ fact(['p:hasMother', X, Y],del,_,U) <=> true | fact(['p:hasMother', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasMother', Y, X],add,M1,_) \ fact(['p:isMotherOf', X, Y],del,_,U) <=> true | fact(['p:isMotherOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasGrandfather', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isThirdCousinOf', Y, X],add,M1,_) \ fact(['p:isThirdCousinOf', X, Y],del,_,U) <=> true | fact(['p:isThirdCousinOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSisterInLawOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isWifeOf', Y, X],add,M1,_) \ fact(['p:hasWife', X, Y],del,_,U) <=> true | fact(['p:hasWife', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasWife', Y, X],add,M1,_) \ fact(['p:isWifeOf', X, Y],del,_,U) <=> true | fact(['p:isWifeOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSisterInLawOf', X, _],add,M1,_) \ fact(['p:Woman', X],del,_,U) <=> true | fact(['p:Woman', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasFatherInLaw', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isGreatUncleOf', X, _],add,M1,_) \ fact(['p:Man', X],del,_,U) <=> true | fact(['p:Man', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isFemalePartnerIn', X, Y],add,M1,_) \ fact(['p:isPartnerIn', X, Y],del,_,U) <=> true | fact(['p:isPartnerIn', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isAuntOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isDaughterOf', X0, X1],add,M1,_), fact(['p:isSiblingOf', X1, X2],add,M2,_) \ fact(['p:isNieceOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isNieceOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:sisterOf', X0, X1],add,M1,_), fact(['p:grandParentOf', X1, X2],add,M2,_) \ fact(['p:isGreatAuntOf', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isGreatAuntOf', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isBloodRelationOf', _, X1],add,M1,_) \ fact(['p:Person', X1],del,_,U) <=> true | fact(['p:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:hasChild', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:GreatGreatGrandparent', X],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:Person', X],add,M1,_), fact(['p:isParentOf', X, X1],add,M2,_), fact(['p:Person', X1],add,M3,_), fact(['p:isParentOf', X1, X2],add,M4,_), fact(['p:Person', X2],add,M5,_), fact(['p:isParentOf', X2, X3],add,M6,_), fact(['p:Person', X3],add,M7,_), fact(['p:isParentOf', X3, X4],add,M8,_), fact(['p:Person', X4],add,M9,_) \ fact(['p:GreatGreatGrandparent', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3,M4,M5,M6,M7,M8,M9],M), fact(['p:GreatGreatGrandparent', X],add,M,U), applied_rules(1,red).
phase(2), fact(['p:hasGreatGrandfather', X, Y],add,M1,_) \ fact(['p:hasGreatGrandParent', X, Y],del,_,U) <=> true | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['p:isSiblingOf', X, Y],add,M1,_), fact(['p:isSiblingOf', Y, Z],add,M2,_) \ fact(['p:isSiblingOf', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['p:isSiblingOf', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['p:isParentInLawOf', X, _],add,M1,_) \ fact(['p:Person', X],del,_,U) <=> true | fact(['p:Person', X],add,M1,U), applied_rules(1,red).

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
phase(5), fact(['p:hasParent', X, Y],add,M1,U1), fact(['p:maleInFamilinx', Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasFather', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, Y],add,M1,U1), fact(['p:femaleInFamilinx', Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasMother', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isWifeOf', X0, X1],add,M1,U1), fact(['p:brotherOf', X1, X2],add,M2,U2), fact(['p:isParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:isAuntInLawOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatUncleOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatUncle', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatUncleOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2), fact(['p:grandParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:isSecondCousinOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:alsoKnownAs', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:knownAs', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:directSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBirthYear', X, Y1],add,M1,U1), fact(['p:hasBirthYear', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isChildOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isChildOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParentInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isParentInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', X, Y],add,M1,U1), fact(['p:isForefatherOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isForefatherOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasDeathYear', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,M1,U1), fact(['p:hasFather', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasFatherInLaw', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', X, Y1],add,M1,U1), fact(['p:hasMother', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasAuntInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAuntInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAuntInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAuntInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Grandparent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Grandparent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:alsoKnownAs', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:GreatUncle', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:brotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:GreatUncle', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:DomainEntity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X0, X1],add,M1,U1), fact(['p:isParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isUncleOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandmotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandmother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandmotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBirthYear', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:MotherInLaw', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isMotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSpouseOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:MotherInLaw', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasMalePartner', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isMalePartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasMalePartner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Grandfather', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isFatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Grandfather', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Female', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Sex', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Uncle', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:brotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Uncle', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', X, Y],add,M1,U1), fact(['p:isRelationOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isRelationOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasSister', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:sisterOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasSister', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGender', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Sex', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isDaughterOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasDaughter', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isDaughterOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSonOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasSon', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSonOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Sex', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:DomainEntity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isHusbandOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasHusband', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isHusbandOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isParentOf', X0, X1],add,M1,U1), fact(['p:isSpouseOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isParentInLawOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X0, X1],add,M1,U1), fact(['p:hasBrother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isBrotherInLawOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:BloodRelation', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isBloodRelationOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:BloodRelation', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,M1,U1), fact(['p:Sex', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isParentOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isParentOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:directSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasForeMother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:hasMother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasGrandmother', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X0, X1],add,M1,U1), fact(['p:hasBrother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isSisterInLawOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Wife', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isFemalePartnerIn', X, X1],add,M2,U2), fact(['p:Marriage', X1],add,M3,U3), fact(['p:hasMalePartner', X1, X2],add,M4,U4), fact(['p:Man', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Wife', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasDeathYear', X, Y1],add,M1,U1), fact(['p:hasDeathYear', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasPartner', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isPartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasPartner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:directSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasForeFather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isForefatherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFatherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasFather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFatherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isHusbandOf', X0, X1],add,M1,U1), fact(['p:sisterOf', X1, X2],add,M2,U2), fact(['p:isParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:isUncleInLawOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:ThirdCousin', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasParent', X, X1],add,M2,U2), fact(['p:hasParent', X1, X2],add,M3,U3), fact(['p:Person', X2],add,M4,U4), fact(['p:hasParent', X2, X3],add,M5,U5), fact(['p:Person', X3],add,M6,U6), fact(['p:isSiblingOf', X3, X4],add,M7,U7), fact(['p:Person', X4],add,M8,U8), fact(['p:isParentOf', X4, X5],add,M9,U9), fact(['p:Person', X5],add,M10,U10), fact(['p:isParentOf', X5, X6],add,M11,U11), fact(['p:Person', X6],add,M12,U12), fact(['p:isParentOf', X6, X7],add,M13,U13), fact(['p:Person', X7],add,M14,U14) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9,U10,U11,U12,U13,U14]) | check_neg_mark([M1,M2,M3,M4,M5,M6,M7,M8,M9,M10,M11,M12,M13,M14],M), fact(['p:ThirdCousin', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasGender', X, X1],add,M2,U2), fact(['p:Female', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Woman', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2), fact(['p:isParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:isFirstCousinOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X0, X1],add,M1,U1), fact(['p:isParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isAuntOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatAunt', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatAuntOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Spouse', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isSpouseOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Spouse', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Mother', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isMotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Mother', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:FirstCousin', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasParent', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSiblingOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:FirstCousin', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isMotherInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasMotherInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isMotherInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFamilyName', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:hasFather', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasGrandfather', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Son', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isSonOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Son', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2), fact(['p:isGreatGrandParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:isThirdCousinOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isGrandfatherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandfather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGrandfatherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Daughter', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isDaughterOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Daughter', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:MaleAncestor', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isAncestorOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:MaleAncestor', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFatherInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasFatherInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFatherInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, Y1],add,M1,U1), fact(['p:hasFather', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:brotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasBrother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Parent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Parent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Forefather', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isForefatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Forefather', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:SecondCousin', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasParent', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:hasParent', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isSiblingOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7), fact(['p:isParentOf', X3, X4],add,M8,U8), fact(['p:Person', X4],add,M9,U9), fact(['p:isParentOf', X4, X5],add,M10,U10), fact(['p:Person', X5],add,M11,U11) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9,U10,U11]) | check_neg_mark([M1,M2,M3,M4,M5,M6,M7,M8,M9,M10,M11],M), fact(['p:SecondCousin', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSecondCousinOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGrandmotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandmother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGrandmotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Ancestor', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isAncestorOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Ancestor', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', X, Y],add,M1,U1), fact(['p:isForemotherOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isForemotherOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, Y],add,M1,U1), fact(['p:hasForeFather', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasForeFather', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:knownAs', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatUncleOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X0, X1],add,M1,U1), fact(['p:hasFemalePartner', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasWife', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', X0, X1],add,M1,U1), fact(['p:hasMalePartner', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasHusband', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isParentOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:ParentInLaw', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSpouseOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:ParentInLaw', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:formerlyKnownAs', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Cousin', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasAncestor', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSiblingOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:Cousin', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGrandparent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:GreatGrandparent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasUncle', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isUncleOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:formerlyKnownAs', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:knownAs', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFirstCousinOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, Y],add,M1,U1), fact(['p:hasForeMother', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasForeMother', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAunt', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isAuntOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasForeFather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:DomainEntity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:FemaleDescendent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:hasAncestor', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:FemaleDescendent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncleInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isUncleInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasUncleInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:FemaleAncestor', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isAncestorOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:FemaleAncestor', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGender', X, Y1],add,M1,U1), fact(['p:hasGender', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, Y],add,M1,U1), fact(['p:hasAncestor', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasAncestor', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Foremother', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isForemotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Foremother', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isAncestorOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X0, X1],add,M1,U1), fact(['p:grandParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isGreatUncleOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:hasGrandfather', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasGreatGrandfather', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Male', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Sex', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Female', X],add,M1,U1), fact(['p:Male', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:Sex', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrotherInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSisterInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasBrotherInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isSiblingInLawOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasGender', X, X1],add,M2,U2), fact(['p:Male', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Man', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandParentOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandParentOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Father', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isFatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Father', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:marriageYear', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Marriage', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X0, X1],add,M1,U1), fact(['p:isParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isFirstCousinOnceRemovedOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:FatherInLaw', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isFatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSpouseOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:FatherInLaw', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandfatherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandfather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandfatherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, Y],add,M1,U1), fact(['p:isBloodRelationOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isBloodRelationOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGrandfather', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isFatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([M1,M2,M3,M4,M5,M6,M7],M), fact(['p:GreatGrandfather', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isPartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrotherInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBrotherInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasBrotherInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Grandmother', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isMotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Grandmother', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,M1,U1), fact(['p:hasMother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasMotherInLaw', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Husband', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isMalePartnerIn', X, X1],add,M2,U2), fact(['p:Marriage', X1],add,M3,U3), fact(['p:hasFemalePartner', X1, X2],add,M4,U4), fact(['p:Woman', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Husband', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGender', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFemalePartner', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFemalePartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasFemalePartner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:InLaw', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isInLawOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:InLaw', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Descendent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasAncestor', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:Descendent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,M1,U1), fact(['p:Person', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:PersonWithManySibling', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:grandParentOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:grandParentOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:MaleDescendent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:hasAncestor', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['p:MaleDescendent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isSonOf', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isNephewOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:hasGrandmother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:hasGreatGrandmother', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasForeMother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isForemotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:ParentOfSmallFamily', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:ParentOfLargeFamily', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Aunt', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:sisterOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([M1,M2,M3,M4,M5],M), fact(['p:Aunt', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isMotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasMother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isMotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isThirdCousinOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isWifeOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasWife', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isWifeOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatUncleOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isPartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isDaughterOf', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isNieceOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X0, X1],add,M1,U1), fact(['p:grandParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isGreatAuntOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGreatGrandparent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7), fact(['p:isParentOf', X3, X4],add,M8,U8), fact(['p:Person', X4],add,M9,U9) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9]) | check_neg_mark([M1,M2,M3,M4,M5,M6,M7,M8,M9],M), fact(['p:GreatGreatGrandparent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', X, Y],add,M1,U1), fact(['p:isSiblingOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['p:isSiblingOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).

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
explicit('p:hasParent').
explicit('p:maleInFamilinx').
explicit('p:femaleInFamilinx').
explicit('p:alsoKnownAs').
explicit('p:hasBirthYear').
explicit('p:hasDeathYear').
explicit('p:Female').
explicit('p:hasGender').
explicit('p:hasFamilyName').
explicit('p:formerlyKnownAs').
explicit('p:Male').
explicit('p:marriageYear').
explicit('p:PersonWithManySibling').
explicit('p:ParentOfSmallFamily').
explicit('p:ParentOfLargeFamily').
