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
phase(1), fact(['p:hasParent', X, Y],O1,_,_), fact(['p:maleInFamilinx', Y],O2,_,_) \ fact(['p:hasFather', X, Y],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasFather', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, Y],O1,_,_), fact(['p:femaleInFamilinx', Y],O2,_,_) \ fact(['p:hasMother', X, Y],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasMother', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', X, Y],O1,_,_) \ fact(['p:hasChild', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isWifeOf', X0, X1],O1,_,_), fact(['p:brotherOf', X1, X2],O2,_,_), fact(['p:isParentOf', X2, X3],O3,_,_) \ fact(['p:isAuntInLawOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:isAuntInLawOf', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', X, Y],O1,_,_) \ fact(['p:hasChild', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', Y, X],O1,_,_) \ fact(['p:hasGreatUncle', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatUncle', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', Y, X],O1,_,_) \ fact(['p:isGreatUncleOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatUncleOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X0, X1],O1,_,_), fact(['p:isSiblingOf', X1, X2],O2,_,_), fact(['p:grandParentOf', X2, X3],O3,_,_) \ fact(['p:isSecondCousinOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:isSecondCousinOf', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', X, Y],O1,_,_) \ fact(['p:hasGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:alsoKnownAs', X, Y],O1,_,_) \ fact(['p:knownAs', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:knownAs', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', Y, X],O1,_,_) \ fact(['p:directSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasBirthYear', X, Y1],O1,_,_), fact(['p:hasBirthYear', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', X, Y],O1,_,_) \ fact(['p:isRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isChildOf', Y, X],O1,_,_) \ fact(['p:hasChild', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', Y, X],O1,_,_) \ fact(['p:isChildOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isChildOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParentInLaw', Y, X],O1,_,_) \ fact(['p:isParentInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isParentInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', Y, X],O1,_,_) \ fact(['p:hasParentInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', X, Y],O1,_,_), fact(['p:isForefatherOf', Y, Z],O2,_,_) \ fact(['p:isForefatherOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isForefatherOf', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasDeathYear', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', X, Y],O1,_,_) \ fact(['p:hasParentInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', X, Y],O1,_,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,_,_), fact(['p:hasFather', X1, X2],O2,_,_) \ fact(['p:hasFatherInLaw', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasFatherInLaw', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, Y],O1,_,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, Y1],O1,_,_), fact(['p:hasMother', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAuntInLaw', Y, X],O1,_,_) \ fact(['p:hasAuntInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAuntInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAuntInLaw', Y, X],O1,_,_) \ fact(['p:hasAuntInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAuntInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Grandparent', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isParentOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_) \ fact(['p:Grandparent', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Grandparent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', X, _],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:alsoKnownAs', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:GreatUncle', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:brotherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_), fact(['p:isParentOf', X2, X3],O6,_,_), fact(['p:Person', X3],O7,_,_) \ fact(['p:GreatUncle', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:GreatUncle', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', X, _],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,_,_) \ fact(['p:DomainEntity', X],add,_,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X0, X1],O1,_,_), fact(['p:isParentOf', X1, X2],O2,_,_) \ fact(['p:isUncleOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isUncleOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', _, X1],O1,_,_) \ fact(['p:Marriage', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandmotherOf', Y, X],O1,_,_) \ fact(['p:hasGreatGrandmother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandmother', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', Y, X],O1,_,_) \ fact(['p:isGreatGrandmotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatGrandmotherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasBirthYear', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:MotherInLaw', X],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_,_), fact(['p:isMotherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isSpouseOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_) \ fact(['p:MotherInLaw', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:MotherInLaw', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMalePartner', Y, X],O1,_,_) \ fact(['p:isMalePartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isMalePartnerIn', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', Y, X],O1,_,_) \ fact(['p:hasMalePartner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasMalePartner', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X, _],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', X, Y],O1,_,_) \ fact(['p:isAncestorOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Grandfather', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isFatherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_) \ fact(['p:Grandfather', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Grandfather', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Female', X],O1,_,_) \ fact(['p:Sex', X],add,_,U) <=> member(del,[O1]) | fact(['p:Sex', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Uncle', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:brotherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_) \ fact(['p:Uncle', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Uncle', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', X, Y],O1,_,_), fact(['p:isRelationOf', Y, Z],O2,_,_) \ fact(['p:isRelationOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isRelationOf', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X, _],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasSister', Y, X],O1,_,_) \ fact(['p:sisterOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:sisterOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', Y, X],O1,_,_) \ fact(['p:hasSister', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasSister', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', _, X1],O1,_,_) \ fact(['p:Sex', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Sex', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isDaughterOf', Y, X],O1,_,_) \ fact(['p:hasDaughter', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasDaughter', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', Y, X],O1,_,_) \ fact(['p:isDaughterOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isDaughterOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSonOf', Y, X],O1,_,_) \ fact(['p:hasSon', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasSon', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', Y, X],O1,_,_) \ fact(['p:isSonOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSonOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Sex', X],O1,_,_) \ fact(['p:DomainEntity', X],add,_,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isHusbandOf', Y, X],O1,_,_) \ fact(['p:hasHusband', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasHusband', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', Y, X],O1,_,_) \ fact(['p:isHusbandOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isHusbandOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', X, Y],O1,_,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isParentOf', X0, X1],O1,_,_), fact(['p:isSpouseOf', X1, X2],O2,_,_) \ fact(['p:isParentInLawOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isParentInLawOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', X, _],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X0, X1],O1,_,_), fact(['p:hasBrother', X1, X2],O2,_,_) \ fact(['p:isBrotherInLawOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isBrotherInLawOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:BloodRelation', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isBloodRelationOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:BloodRelation', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:BloodRelation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,_,_), fact(['p:Sex', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isParentOf', X, Y],O1,_,_) \ fact(['p:hasChild', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasChild', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', X, Y],O1,_,_) \ fact(['p:isParentOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isParentOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X, Y],O1,_,_) \ fact(['p:directSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', X, Y],O1,_,_) \ fact(['p:hasGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, Y],O1,_,_) \ fact(['p:hasForeMother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasForeMother', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_,_), fact(['p:hasMother', X1, X2],O2,_,_) \ fact(['p:hasGrandmother', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasGrandmother', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X0, X1],O1,_,_), fact(['p:hasBrother', X1, X2],O2,_,_) \ fact(['p:isSisterInLawOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isSisterInLawOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isAuntInLawOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Wife', X],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_,_), fact(['p:isFemalePartnerIn', X, X1],O2,_,_), fact(['p:Marriage', X1],O3,_,_), fact(['p:hasMalePartner', X1, X2],O4,_,_), fact(['p:Man', X2],O5,_,_) \ fact(['p:Wife', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Wife', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasDeathYear', X, Y1],O1,_,_), fact(['p:hasDeathYear', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasPartner', Y, X],O1,_,_) \ fact(['p:isPartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', Y, X],O1,_,_) \ fact(['p:hasPartner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasPartner', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X, Y],O1,_,_) \ fact(['p:directSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:directSiblingOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isForefatherOf', Y, X],O1,_,_) \ fact(['p:hasForeFather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasForeFather', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', Y, X],O1,_,_) \ fact(['p:isForefatherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isForefatherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFatherOf', Y, X],O1,_,_) \ fact(['p:hasFather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasFather', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', Y, X],O1,_,_) \ fact(['p:isFatherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFatherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isHusbandOf', X0, X1],O1,_,_), fact(['p:sisterOf', X1, X2],O2,_,_), fact(['p:isParentOf', X2, X3],O3,_,_) \ fact(['p:isUncleInLawOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:isUncleInLawOf', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:ThirdCousin', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:hasParent', X, X1],O2,_,_), fact(['p:hasParent', X1, X2],O3,_,_), fact(['p:Person', X2],O4,_,_), fact(['p:hasParent', X2, X3],O5,_,_), fact(['p:Person', X3],O6,_,_), fact(['p:isSiblingOf', X3, X4],O7,_,_), fact(['p:Person', X4],O8,_,_), fact(['p:isParentOf', X4, X5],O9,_,_), fact(['p:Person', X5],O10,_,_), fact(['p:isParentOf', X5, X6],O11,_,_), fact(['p:Person', X6],O12,_,_), fact(['p:isParentOf', X6, X7],O13,_,_), fact(['p:Person', X7],O14,_,_) \ fact(['p:ThirdCousin', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14]) | fact(['p:ThirdCousin', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:hasGender', X, X1],O2,_,_), fact(['p:Female', X1],O3,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_,_), fact(['p:isSiblingOf', X1, X2],O2,_,_), fact(['p:isParentOf', X2, X3],O3,_,_) \ fact(['p:isFirstCousinOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:isFirstCousinOf', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, Y],O1,_,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', Y, X],O1,_,_) \ fact(['p:isSpouseOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X0, X1],O1,_,_), fact(['p:isParentOf', X1, X2],O2,_,_) \ fact(['p:isAuntOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isAuntOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X, Y],O1,_,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', X, Y],O1,_,_) \ fact(['p:isSiblingInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', Y, X],O1,_,_) \ fact(['p:hasGreatAunt', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatAunt', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', Y, X],O1,_,_) \ fact(['p:isGreatAuntOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatAuntOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Spouse', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isSpouseOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Spouse', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Spouse', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', _, X1],O1,_,_) \ fact(['p:Marriage', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Mother', X],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_,_), fact(['p:isMotherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Mother', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Mother', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:FirstCousin', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:hasParent', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isSiblingOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_), fact(['p:isParentOf', X2, X3],O6,_,_), fact(['p:Person', X3],O7,_,_) \ fact(['p:FirstCousin', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:FirstCousin', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isMotherInLawOf', Y, X],O1,_,_) \ fact(['p:hasMotherInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasMotherInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', Y, X],O1,_,_) \ fact(['p:isMotherInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isMotherInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFamilyName', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_,_), fact(['p:hasFather', X1, X2],O2,_,_) \ fact(['p:hasGrandfather', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasGrandfather', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Son', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isSonOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Son', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Son', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', X0, X1],O1,_,_), fact(['p:isSiblingOf', X1, X2],O2,_,_), fact(['p:isGreatGrandParentOf', X2, X3],O3,_,_) \ fact(['p:isThirdCousinOf', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:isThirdCousinOf', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGrandfatherOf', Y, X],O1,_,_) \ fact(['p:hasGrandfather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandfather', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', Y, X],O1,_,_) \ fact(['p:isGrandfatherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGrandfatherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', X, Y],O1,_,_) \ fact(['p:isSpouseOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Daughter', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isDaughterOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Daughter', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Daughter', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', X, Y],O1,_,_) \ fact(['p:hasParentInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasParentInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:MaleAncestor', X],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_,_), fact(['p:isAncestorOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:MaleAncestor', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:MaleAncestor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFatherInLawOf', Y, X],O1,_,_) \ fact(['p:hasFatherInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasFatherInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', Y, X],O1,_,_) \ fact(['p:isFatherInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFatherInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasDaughter', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, Y1],O1,_,_), fact(['p:hasFather', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X, Y],O1,_,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', Y, X],O1,_,_) \ fact(['p:brotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:brotherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', Y, X],O1,_,_) \ fact(['p:hasBrother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasBrother', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X, _],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Parent', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isParentOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Parent', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Parent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X, _],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasSon', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatAuntOf', X, _],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', X, _],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Forefather', X],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_,_), fact(['p:isForefatherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Forefather', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Forefather', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', X, _],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:SecondCousin', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:hasParent', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:hasParent', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_), fact(['p:isSiblingOf', X2, X3],O6,_,_), fact(['p:Person', X3],O7,_,_), fact(['p:isParentOf', X3, X4],O8,_,_), fact(['p:Person', X4],O9,_,_), fact(['p:isParentOf', X4, X5],O10,_,_), fact(['p:Person', X5],O11,_,_) \ fact(['p:SecondCousin', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11]) | fact(['p:SecondCousin', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', Y, X],O1,_,_) \ fact(['p:isRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', Y, X],O1,_,_) \ fact(['p:isSecondCousinOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSecondCousinOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGrandmotherOf', Y, X],O1,_,_) \ fact(['p:hasGrandmother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandmother', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', Y, X],O1,_,_) \ fact(['p:isGrandmotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGrandmotherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', X, Y],O1,_,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Ancestor', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isAncestorOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Ancestor', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Ancestor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', Y, X],O1,_,_) \ fact(['p:isSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', X, Y],O1,_,_) \ fact(['p:isAncestorOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', X, Y],O1,_,_), fact(['p:isForemotherOf', Y, Z],O2,_,_) \ fact(['p:isForemotherOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isForemotherOf', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeFather', X, Y],O1,_,_), fact(['p:hasForeFather', Y, Z],O2,_,_) \ fact(['p:hasForeFather', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasForeFather', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', X, Y],O1,_,_) \ fact(['p:isSpouseOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSpouseOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:knownAs', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X0, X1],O1,_,_), fact(['p:hasFemalePartner', X1, X2],O2,_,_) \ fact(['p:hasWife', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasWife', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X0, X1],O1,_,_), fact(['p:hasMalePartner', X1, X2],O2,_,_) \ fact(['p:hasHusband', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasHusband', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', X, Y],O1,_,_) \ fact(['p:isSiblingOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', Y, X],O1,_,_) \ fact(['p:isParentOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isParentOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:ParentInLaw', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isParentOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isSpouseOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_) \ fact(['p:ParentInLaw', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:ParentInLaw', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:formerlyKnownAs', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, Y],O1,_,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Cousin', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:hasAncestor', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isSiblingOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_), fact(['p:isParentOf', X2, X3],O6,_,_), fact(['p:Person', X3],O7,_,_) \ fact(['p:Cousin', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:Cousin', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:GreatGrandparent', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isParentOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_), fact(['p:isParentOf', X2, X3],O6,_,_), fact(['p:Person', X3],O7,_,_) \ fact(['p:GreatGrandparent', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:GreatGrandparent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', Y, X],O1,_,_) \ fact(['p:hasUncle', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasUncle', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', Y, X],O1,_,_) \ fact(['p:isUncleOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isUncleOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasHusband', X, _],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:formerlyKnownAs', X, Y],O1,_,_) \ fact(['p:knownAs', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:knownAs', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', Y, X],O1,_,_) \ fact(['p:isFirstCousinOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFirstCousinOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', X, Y],O1,_,_), fact(['p:hasForeMother', Y, Z],O2,_,_) \ fact(['p:hasForeMother', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasForeMother', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', Y, X],O1,_,_) \ fact(['p:hasAunt', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAunt', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', Y, X],O1,_,_) \ fact(['p:isAuntOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isAuntOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', X, _],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', X, Y],O1,_,_) \ fact(['p:hasForeFather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasForeFather', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_) \ fact(['p:DomainEntity', X],add,_,U) <=> member(del,[O1]) | fact(['p:DomainEntity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:FemaleDescendent', X],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_,_), fact(['p:hasAncestor', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:FemaleDescendent', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:FemaleDescendent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isPartnerIn', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasUncleInLaw', Y, X],O1,_,_) \ fact(['p:isUncleInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isUncleInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', Y, X],O1,_,_) \ fact(['p:hasUncleInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasUncleInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:FemaleAncestor', X],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_,_), fact(['p:isAncestorOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:FemaleAncestor', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:FemaleAncestor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isNieceOf', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', _, X1],O1,_,_) \ fact(['p:Marriage', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Marriage', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', X, Y1],O1,_,_), fact(['p:hasGender', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasBrother', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, Y],O1,_,_), fact(['p:hasAncestor', Y, Z],O2,_,_) \ fact(['p:hasAncestor', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasAncestor', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Foremother', X],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Woman', X],O1,_,_), fact(['p:isForemotherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Foremother', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Foremother', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOnceRemovedOf', Y, X],O1,_,_) \ fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:directSiblingOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', Y, X],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isAncestorOf', Y, X],O1,_,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', Y, X],O1,_,_) \ fact(['p:isAncestorOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isAncestorOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasUncle', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X, Y],O1,_,_) \ fact(['p:hasAncestor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasAncestor', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X0, X1],O1,_,_), fact(['p:grandParentOf', X1, X2],O2,_,_) \ fact(['p:isGreatUncleOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isGreatUncleOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_,_), fact(['p:hasGrandfather', X1, X2],O2,_,_) \ fact(['p:hasGreatGrandfather', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasGreatGrandfather', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Male', X],O1,_,_) \ fact(['p:Sex', X],add,_,U) <=> member(del,[O1]) | fact(['p:Sex', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Female', X],O1,_,_), fact(['p:Male', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMotherInLaw', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:Sex', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isRelationOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasBrotherInLaw', Y, X],O1,_,_) \ fact(['p:isSisterInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSisterInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', Y, X],O1,_,_) \ fact(['p:hasBrotherInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasBrotherInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,_,_), fact(['p:isSiblingOf', X1, X2],O2,_,_) \ fact(['p:isSiblingInLawOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isSiblingInLawOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:hasGender', X, X1],O2,_,_), fact(['p:Male', X1],O3,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandParentOf', Y, X],O1,_,_) \ fact(['p:hasGreatGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', Y, X],O1,_,_) \ fact(['p:isGreatGrandParentOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatGrandParentOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatAunt', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isUncleInLawOf', X, _],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Father', X],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_,_), fact(['p:isFatherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Father', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Father', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isNephewOf', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAunt', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasAncestor', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:marriageYear', X, _],O1,_,_) \ fact(['p:Marriage', X],add,_,U) <=> member(del,[O1]) | fact(['p:Marriage', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:brotherOf', X, _],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', X0, X1],O1,_,_), fact(['p:isParentOf', X1, X2],O2,_,_) \ fact(['p:isFirstCousinOnceRemovedOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isFirstCousinOnceRemovedOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:FatherInLaw', X],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_,_), fact(['p:isFatherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isSpouseOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_) \ fact(['p:FatherInLaw', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:FatherInLaw', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandParent', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatGrandfatherOf', Y, X],O1,_,_) \ fact(['p:hasGreatGrandfather', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandfather', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', Y, X],O1,_,_) \ fact(['p:isGreatGrandfatherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isGreatGrandfatherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isUncleOf', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatUncle', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, Y],O1,_,_), fact(['p:isBloodRelationOf', Y, Z],O2,_,_) \ fact(['p:isBloodRelationOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isBloodRelationOf', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:GreatGrandfather', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isFatherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_), fact(['p:isParentOf', X2, X3],O6,_,_), fact(['p:Person', X3],O7,_,_) \ fact(['p:GreatGrandfather', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:GreatGrandfather', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFirstCousinOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isMalePartnerIn', X, Y],O1,_,_) \ fact(['p:isPartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', X, Y],O1,_,_) \ fact(['p:hasGreatGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasBrotherInLaw', Y, X],O1,_,_) \ fact(['p:isBrotherInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBrotherInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', Y, X],O1,_,_) \ fact(['p:hasBrotherInLaw', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasBrotherInLaw', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Grandmother', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isMotherOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_) \ fact(['p:Grandmother', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Grandmother', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSpouseOf', X0, X1],O1,_,_), fact(['p:hasMother', X1, X2],O2,_,_) \ fact(['p:hasMotherInLaw', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasMotherInLaw', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Husband', X],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_,_), fact(['p:isMalePartnerIn', X, X1],O2,_,_), fact(['p:Marriage', X1],O3,_,_), fact(['p:hasFemalePartner', X1, X2],O4,_,_), fact(['p:Woman', X2],O5,_,_) \ fact(['p:Husband', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Husband', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandmother', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGender', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFemalePartner', Y, X],O1,_,_) \ fact(['p:isFemalePartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isFemalePartnerIn', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', Y, X],O1,_,_) \ fact(['p:hasFemalePartner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasFemalePartner', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:InLaw', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isInLawOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:InLaw', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:InLaw', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingInLawOf', Y, X],O1,_,_) \ fact(['p:isSiblingInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Descendent', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:hasAncestor', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:Descendent', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:Descendent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', X, Y],O1,_,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Marriage', X],O1,_,_), fact(['p:Person', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSecondCousinOf', X, Y],O1,_,_) \ fact(['p:isBloodRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', X, Y],O1,_,_) \ fact(['p:isRelationOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isRelationOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:PersonWithManySibling', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFather', _, X1],O1,_,_) \ fact(['p:Man', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:grandParentOf', Y, X],O1,_,_) \ fact(['p:hasGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGrandParent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandParent', Y, X],O1,_,_) \ fact(['p:grandParentOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:grandParentOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:MaleDescendent', X],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Man', X],O1,_,_), fact(['p:hasAncestor', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_) \ fact(['p:MaleDescendent', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['p:MaleDescendent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSonOf', X0, X1],O1,_,_), fact(['p:isSiblingOf', X1, X2],O2,_,_) \ fact(['p:isNephewOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isNephewOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isInLawOf', Y, X],O1,_,_) \ fact(['p:isInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasParent', X0, X1],O1,_,_), fact(['p:hasGrandmother', X1, X2],O2,_,_) \ fact(['p:hasGreatGrandmother', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:hasGreatGrandmother', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isForemotherOf', Y, X],O1,_,_) \ fact(['p:hasForeMother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasForeMother', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasForeMother', Y, X],O1,_,_) \ fact(['p:isForemotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isForemotherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandmother', _, X1],O1,_,_) \ fact(['p:Woman', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBrotherInLawOf', X, Y],O1,_,_) \ fact(['p:isSiblingInLawOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:ParentOfSmallFamily', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:ParentOfLargeFamily', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Aunt', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:sisterOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_) \ fact(['p:Aunt', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5]) | fact(['p:Aunt', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isMotherOf', Y, X],O1,_,_) \ fact(['p:hasMother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasMother', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasMother', Y, X],O1,_,_) \ fact(['p:isMotherOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isMotherOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGrandfather', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isThirdCousinOf', Y, X],O1,_,_) \ fact(['p:isThirdCousinOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isThirdCousinOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isWifeOf', Y, X],O1,_,_) \ fact(['p:hasWife', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasWife', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasWife', Y, X],O1,_,_) \ fact(['p:isWifeOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isWifeOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSisterInLawOf', X, _],O1,_,_) \ fact(['p:Woman', X],add,_,U) <=> member(del,[O1]) | fact(['p:Woman', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasFatherInLaw', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isGreatUncleOf', X, _],O1,_,_) \ fact(['p:Man', X],add,_,U) <=> member(del,[O1]) | fact(['p:Man', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isFemalePartnerIn', X, Y],O1,_,_) \ fact(['p:isPartnerIn', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:isPartnerIn', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isAuntOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isDaughterOf', X0, X1],O1,_,_), fact(['p:isSiblingOf', X1, X2],O2,_,_) \ fact(['p:isNieceOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isNieceOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:sisterOf', X0, X1],O1,_,_), fact(['p:grandParentOf', X1, X2],O2,_,_) \ fact(['p:isGreatAuntOf', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isGreatAuntOf', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isBloodRelationOf', _, X1],O1,_,_) \ fact(['p:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasChild', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:GreatGreatGrandparent', X],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:Person', X],O1,_,_), fact(['p:isParentOf', X, X1],O2,_,_), fact(['p:Person', X1],O3,_,_), fact(['p:isParentOf', X1, X2],O4,_,_), fact(['p:Person', X2],O5,_,_), fact(['p:isParentOf', X2, X3],O6,_,_), fact(['p:Person', X3],O7,_,_), fact(['p:isParentOf', X3, X4],O8,_,_), fact(['p:Person', X4],O9,_,_) \ fact(['p:GreatGreatGrandparent', X],add,_,U) <=> member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9]) | fact(['p:GreatGreatGrandparent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:hasGreatGrandfather', X, Y],O1,_,_) \ fact(['p:hasGreatGrandParent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isSiblingOf', X, Y],O1,_,_), fact(['p:isSiblingOf', Y, Z],O2,_,_) \ fact(['p:isSiblingOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['p:isSiblingOf', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['p:isParentInLawOf', X, _],O1,_,_) \ fact(['p:Person', X],add,_,U) <=> member(del,[O1]) | fact(['p:Person', X],chk,_,U), applied_rules(1,del).

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
fact(['p:hasParent', X, Y],prv,M1,_), fact(['p:maleInFamilinx', Y],prv,M2,_) \ fact(['p:hasFather', X, Y],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasParent',M1),('p:maleInFamilinx',M2)],M), fact(['p:hasFather', X, Y],prv,M,U), applied_rules(1,fwd).
fact(['p:hasParent', X, Y],prv,M1,_), fact(['p:femaleInFamilinx', Y],prv,M2,_) \ fact(['p:hasMother', X, Y],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasParent',M1),('p:femaleInFamilinx',M2)],M), fact(['p:hasMother', X, Y],prv,M,U), applied_rules(1,fwd).
fact(['p:hasSon', X, Y],prv,_,_) \ fact(['p:hasChild', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasChild', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isWifeOf', X0, X1],prv,_,_), fact(['p:brotherOf', X1, X2],prv,_,_), fact(['p:isParentOf', X2, X3],prv,_,_) \ fact(['p:isAuntInLawOf', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isAuntInLawOf', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['p:hasDaughter', X, Y],prv,_,_) \ fact(['p:hasChild', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasChild', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isGreatUncleOf', Y, X],prv,_,_) \ fact(['p:hasGreatUncle', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGreatUncle', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatUncle', Y, X],prv,_,_) \ fact(['p:isGreatUncleOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGreatUncleOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandParent', X0, X1],prv,_,_), fact(['p:isSiblingOf', X1, X2],prv,_,_), fact(['p:grandParentOf', X2, X3],prv,_,_) \ fact(['p:isSecondCousinOf', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSecondCousinOf', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandmother', X, Y],prv,_,_) \ fact(['p:hasGrandParent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGrandParent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:alsoKnownAs', X, Y],prv,M1,_) \ fact(['p:knownAs', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:knownAs', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['p:directSiblingOf', Y, X],prv,_,_) \ fact(['p:directSiblingOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:directSiblingOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasBirthYear', X, Y1],prv,M1,_), fact(['p:hasBirthYear', X, Y2],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasBirthYear',M1),('p:hasBirthYear',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['p:hasHusband', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isInLawOf', X, Y],prv,_,_) \ fact(['p:isRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isChildOf', Y, X],prv,_,_) \ fact(['p:hasChild', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasChild', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasChild', Y, X],prv,_,_) \ fact(['p:isChildOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isChildOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasParentInLaw', Y, X],prv,_,_) \ fact(['p:isParentInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isParentInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isParentInLawOf', Y, X],prv,_,_) \ fact(['p:hasParentInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasParentInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isForefatherOf', X, Y],prv,_,_), fact(['p:isForefatherOf', Y, Z],prv,_,_) \ fact(['p:isForefatherOf', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isForefatherOf', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAunt', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatUncle', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasDeathYear', X, _],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:hasMotherInLaw', X, Y],prv,_,_) \ fact(['p:hasParentInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasParentInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isAuntInLawOf', X, Y],prv,_,_) \ fact(['p:isInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOf', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSpouseOf', X0, X1],prv,_,_), fact(['p:hasFather', X1, X2],prv,_,_) \ fact(['p:hasFatherInLaw', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasFatherInLaw', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeFather', X, Y],prv,_,_) \ fact(['p:hasAncestor', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAncestor', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasMother', X, Y1],prv,_,_), fact(['p:hasMother', X, Y2],prv,_,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', Y1, Y2],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAuntInLaw', Y, X],prv,_,_) \ fact(['p:hasAuntInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAuntInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAuntInLaw', Y, X],prv,_,_) \ fact(['p:hasAuntInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAuntInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Grandparent', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isParentOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_) \ fact(['p:Grandparent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Grandparent', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isAuntInLawOf', X, _],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasUncle', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:alsoKnownAs', X, _],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:GreatUncle', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:brotherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_), fact(['p:isParentOf', X2, X3],prv,_,_), fact(['p:Person', X3],prv,_,_) \ fact(['p:GreatUncle', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:GreatUncle', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasParent', _, X1],prv,M1,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOnceRemovedOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isAuntOf', X, _],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasSon', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Marriage', X],prv,_,_) \ fact(['p:DomainEntity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:DomainEntity', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAunt', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:brotherOf', X0, X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_) \ fact(['p:isUncleOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isUncleOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:isPartnerIn', _, X1],prv,_,_) \ fact(['p:Marriage', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Marriage', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isGreatGrandmotherOf', Y, X],prv,_,_) \ fact(['p:hasGreatGrandmother', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGreatGrandmother', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandmother', Y, X],prv,_,_) \ fact(['p:isGreatGrandmotherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGreatGrandmotherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasBirthYear', X, _],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:MotherInLaw', X],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Woman', X],prv,_,_), fact(['p:isMotherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isSpouseOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_) \ fact(['p:MotherInLaw', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:MotherInLaw', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasMalePartner', Y, X],prv,_,_) \ fact(['p:isMalePartnerIn', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isMalePartnerIn', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isMalePartnerIn', Y, X],prv,_,_) \ fact(['p:hasMalePartner', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasMalePartner', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasWife', X, _],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isForefatherOf', X, Y],prv,_,_) \ fact(['p:isAncestorOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isAncestorOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Grandfather', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isFatherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_) \ fact(['p:Grandfather', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Grandfather', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Female', X],prv,M1,_) \ fact(['p:Sex', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Sex', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:hasAncestor', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:Uncle', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:brotherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_) \ fact(['p:Uncle', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Uncle', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isNephewOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isRelationOf', X, Y],prv,_,_), fact(['p:isRelationOf', Y, Z],prv,_,_) \ fact(['p:isRelationOf', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isRelationOf', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandmother', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isRelationOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isFemalePartnerIn', X, _],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasSister', Y, X],prv,_,_) \ fact(['p:sisterOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:sisterOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:sisterOf', Y, X],prv,_,_) \ fact(['p:hasSister', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasSister', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:directSiblingOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isThirdCousinOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGender', _, X1],prv,M1,_) \ fact(['p:Sex', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Sex', X1],prv,M1,U), applied_rules(1,fwd).
fact(['p:isDaughterOf', Y, X],prv,_,_) \ fact(['p:hasDaughter', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasDaughter', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasDaughter', Y, X],prv,_,_) \ fact(['p:isDaughterOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isDaughterOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandfather', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingInLawOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isSonOf', Y, X],prv,_,_) \ fact(['p:hasSon', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasSon', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasSon', Y, X],prv,_,_) \ fact(['p:isSonOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSonOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Sex', X],prv,_,_) \ fact(['p:DomainEntity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:DomainEntity', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isHusbandOf', Y, X],prv,_,_) \ fact(['p:hasHusband', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasHusband', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasHusband', Y, X],prv,_,_) \ fact(['p:isHusbandOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isHusbandOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isUncleInLawOf', X, Y],prv,_,_) \ fact(['p:isInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isParentOf', X0, X1],prv,_,_), fact(['p:isSpouseOf', X1, X2],prv,_,_) \ fact(['p:isParentInLawOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isParentInLawOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:isBrotherInLawOf', X, _],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasWife', X0, X1],prv,_,_), fact(['p:hasBrother', X1, X2],prv,_,_) \ fact(['p:isBrotherInLawOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBrotherInLawOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:BloodRelation', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isBloodRelationOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:BloodRelation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:BloodRelation', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Marriage', X],prv,_,_), fact(['p:Sex', X],prv,_,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:Nothing', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFatherInLaw', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeFather', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isParentOf', X, Y],prv,_,_) \ fact(['p:hasChild', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasChild', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasChild', X, Y],prv,_,_) \ fact(['p:isParentOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isParentOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:brotherOf', X, Y],prv,_,_) \ fact(['p:directSiblingOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:directSiblingOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandParent', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandfather', X, Y],prv,_,_) \ fact(['p:hasGrandParent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGrandParent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasUncle', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasMother', X, Y],prv,_,_) \ fact(['p:hasForeMother', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasForeMother', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandParent', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasParent', X0, X1],prv,M1,_), fact(['p:hasMother', X1, X2],prv,M2,_) \ fact(['p:hasGrandmother', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasParent',M1),('p:hasMother',M2)],M), fact(['p:hasGrandmother', X0, X2],prv,M,U), applied_rules(1,fwd).
fact(['p:hasWife', X0, X1],prv,_,_), fact(['p:hasBrother', X1, X2],prv,_,_) \ fact(['p:isSisterInLawOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSisterInLawOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:isAuntInLawOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:sisterOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:Wife', X],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Woman', X],prv,_,_), fact(['p:isFemalePartnerIn', X, X1],prv,_,_), fact(['p:Marriage', X1],prv,_,_), fact(['p:hasMalePartner', X1, X2],prv,_,_), fact(['p:Man', X2],prv,_,_) \ fact(['p:Wife', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Wife', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasDeathYear', X, Y1],prv,M1,_), fact(['p:hasDeathYear', X, Y2],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasDeathYear',M1),('p:hasDeathYear',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['p:hasPartner', Y, X],prv,_,_) \ fact(['p:isPartnerIn', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isPartnerIn', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isPartnerIn', Y, X],prv,_,_) \ fact(['p:hasPartner', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasPartner', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:sisterOf', X, Y],prv,_,_) \ fact(['p:directSiblingOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:directSiblingOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isForefatherOf', Y, X],prv,_,_) \ fact(['p:hasForeFather', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasForeFather', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeFather', Y, X],prv,_,_) \ fact(['p:isForefatherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isForefatherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isFatherOf', Y, X],prv,_,_) \ fact(['p:hasFather', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasFather', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFather', Y, X],prv,_,_) \ fact(['p:isFatherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isFatherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSpouseOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isHusbandOf', X0, X1],prv,_,_), fact(['p:sisterOf', X1, X2],prv,_,_), fact(['p:isParentOf', X2, X3],prv,_,_) \ fact(['p:isUncleInLawOf', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isUncleInLawOf', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeMother', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:ThirdCousin', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,M1,_), fact(['p:hasParent', X, X1],prv,M2,_), fact(['p:hasParent', X1, X2],prv,M3,_), fact(['p:Person', X2],prv,M4,_), fact(['p:hasParent', X2, X3],prv,M5,_), fact(['p:Person', X3],prv,M6,_), fact(['p:isSiblingOf', X3, X4],prv,M7,_), fact(['p:Person', X4],prv,M8,_), fact(['p:isParentOf', X4, X5],prv,M9,_), fact(['p:Person', X5],prv,M10,_), fact(['p:isParentOf', X5, X6],prv,M11,_), fact(['p:Person', X6],prv,M12,_), fact(['p:isParentOf', X6, X7],prv,M13,_), fact(['p:Person', X7],prv,M14,_) \ fact(['p:ThirdCousin', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:Person',M1),('p:hasParent',M2),('p:hasParent',M3),('p:Person',M4),('p:hasParent',M5),('p:Person',M6),('p:isSiblingOf',M7),('p:Person',M8),('p:isParentOf',M9),('p:Person',M10),('p:isParentOf',M11),('p:Person',M12),('p:isParentOf',M13),('p:Person',M14)],M), fact(['p:ThirdCousin', X],prv,M,U), applied_rules(1,fwd).
fact(['p:Woman', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,M1,_), fact(['p:hasGender', X, X1],prv,M2,_), fact(['p:Female', X1],prv,M3,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:Person',M1),('p:hasGender',M2),('p:Female',M3)],M), fact(['p:Woman', X],prv,M,U), applied_rules(1,fwd).
fact(['p:hasParent', X0, X1],prv,M1,_), fact(['p:isSiblingOf', X1, X2],prv,M2,_), fact(['p:isParentOf', X2, X3],prv,M3,_) \ fact(['p:isFirstCousinOf', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasParent',M1),('p:isSiblingOf',M2),('p:isParentOf',M3)],M), fact(['p:isFirstCousinOf', X0, X3],prv,M,U), applied_rules(1,fwd).
fact(['p:hasForeMother', X, Y],prv,_,_) \ fact(['p:hasAncestor', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAncestor', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSpouseOf', Y, X],prv,_,_) \ fact(['p:isSpouseOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSpouseOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:sisterOf', X0, X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_) \ fact(['p:isAuntOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isAuntOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandParent', X, Y],prv,_,_) \ fact(['p:hasAncestor', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAncestor', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSisterInLawOf', X, Y],prv,_,_) \ fact(['p:isSiblingInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSiblingInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isGreatAuntOf', Y, X],prv,_,_) \ fact(['p:hasGreatAunt', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGreatAunt', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatAunt', Y, X],prv,_,_) \ fact(['p:isGreatAuntOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGreatAuntOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Spouse', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isSpouseOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Spouse', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Spouse', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isMalePartnerIn', _, X1],prv,_,_) \ fact(['p:Marriage', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Marriage', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasMother', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isBrotherInLawOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:Mother', X],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Woman', X],prv,_,_), fact(['p:isMotherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Mother', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Mother', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasDaughter', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isUncleOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:FirstCousin', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,M1,_), fact(['p:hasParent', X, X1],prv,M2,_), fact(['p:Person', X1],prv,M3,_), fact(['p:isSiblingOf', X1, X2],prv,M4,_), fact(['p:Person', X2],prv,M5,_), fact(['p:isParentOf', X2, X3],prv,M6,_), fact(['p:Person', X3],prv,M7,_) \ fact(['p:FirstCousin', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:Person',M1),('p:hasParent',M2),('p:Person',M3),('p:isSiblingOf',M4),('p:Person',M5),('p:isParentOf',M6),('p:Person',M7)],M), fact(['p:FirstCousin', X],prv,M,U), applied_rules(1,fwd).
fact(['p:isBloodRelationOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isMotherInLawOf', Y, X],prv,_,_) \ fact(['p:hasMotherInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasMotherInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasMotherInLaw', Y, X],prv,_,_) \ fact(['p:isMotherInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isMotherInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isGreatAuntOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFamilyName', X, _],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:hasParent', X0, X1],prv,M1,_), fact(['p:hasFather', X1, X2],prv,M2,_) \ fact(['p:hasGrandfather', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasParent',M1),('p:hasFather',M2)],M), fact(['p:hasGrandfather', X0, X2],prv,M,U), applied_rules(1,fwd).
fact(['p:Son', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isSonOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Son', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Son', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandParent', X0, X1],prv,_,_), fact(['p:isSiblingOf', X1, X2],prv,_,_), fact(['p:isGreatGrandParentOf', X2, X3],prv,_,_) \ fact(['p:isThirdCousinOf', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isThirdCousinOf', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['p:isGrandfatherOf', Y, X],prv,_,_) \ fact(['p:hasGrandfather', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGrandfather', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandfather', Y, X],prv,_,_) \ fact(['p:isGrandfatherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGrandfatherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasWife', X, Y],prv,_,_) \ fact(['p:isSpouseOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSpouseOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Daughter', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isDaughterOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Daughter', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Daughter', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFatherInLaw', X, Y],prv,_,_) \ fact(['p:hasParentInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasParentInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:MaleAncestor', X],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Man', X],prv,_,_), fact(['p:isAncestorOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:MaleAncestor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:MaleAncestor', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isFatherInLawOf', Y, X],prv,_,_) \ fact(['p:hasFatherInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasFatherInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFatherInLaw', Y, X],prv,_,_) \ fact(['p:isFatherInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isFatherInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasDaughter', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFather', X, Y1],prv,_,_), fact(['p:hasFather', X, Y2],prv,_,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', Y1, Y2],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeFather', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isSpouseOf', X, Y],prv,_,_) \ fact(['p:isInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasBrother', Y, X],prv,_,_) \ fact(['p:brotherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:brotherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:brotherOf', Y, X],prv,_,_) \ fact(['p:hasBrother', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasBrother', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:sisterOf', X, _],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Parent', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isParentOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Parent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Parent', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isMalePartnerIn', X, _],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasSon', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isGreatAuntOf', X, _],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isNephewOf', X, _],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOnceRemovedOf', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Forefather', X],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Man', X],prv,_,_), fact(['p:isForefatherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Forefather', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Forefather', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeMother', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isNieceOf', X, _],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isInLawOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:SecondCousin', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,M1,_), fact(['p:hasParent', X, X1],prv,M2,_), fact(['p:Person', X1],prv,M3,_), fact(['p:hasParent', X1, X2],prv,M4,_), fact(['p:Person', X2],prv,M5,_), fact(['p:isSiblingOf', X2, X3],prv,M6,_), fact(['p:Person', X3],prv,M7,_), fact(['p:isParentOf', X3, X4],prv,M8,_), fact(['p:Person', X4],prv,M9,_), fact(['p:isParentOf', X4, X5],prv,M10,_), fact(['p:Person', X5],prv,M11,_) \ fact(['p:SecondCousin', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:Person',M1),('p:hasParent',M2),('p:Person',M3),('p:hasParent',M4),('p:Person',M5),('p:isSiblingOf',M6),('p:Person',M7),('p:isParentOf',M8),('p:Person',M9),('p:isParentOf',M10),('p:Person',M11)],M), fact(['p:SecondCousin', X],prv,M,U), applied_rules(1,fwd).
fact(['p:hasChild', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isRelationOf', Y, X],prv,_,_) \ fact(['p:isRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSecondCousinOf', Y, X],prv,_,_) \ fact(['p:isSecondCousinOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSecondCousinOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isNieceOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isGrandmotherOf', Y, X],prv,_,_) \ fact(['p:hasGrandmother', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGrandmother', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandmother', Y, X],prv,_,_) \ fact(['p:isGrandmotherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGrandmotherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingInLawOf', X, Y],prv,_,_) \ fact(['p:isInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Ancestor', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isAncestorOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Ancestor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Ancestor', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatAunt', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingOf', Y, X],prv,_,_) \ fact(['p:isSiblingOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSiblingOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isForemotherOf', X, Y],prv,_,_) \ fact(['p:isAncestorOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isAncestorOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isForemotherOf', X, Y],prv,_,_), fact(['p:isForemotherOf', Y, Z],prv,_,_) \ fact(['p:isForemotherOf', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isForemotherOf', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeFather', X, Y],prv,_,_), fact(['p:hasForeFather', Y, Z],prv,_,_) \ fact(['p:hasForeFather', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasForeFather', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['p:hasHusband', X, Y],prv,_,_) \ fact(['p:isSpouseOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSpouseOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isParentInLawOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:knownAs', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasBrother', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isGreatUncleOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFather', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isMalePartnerIn', X0, X1],prv,_,_), fact(['p:hasFemalePartner', X1, X2],prv,_,_) \ fact(['p:hasWife', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasWife', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:isFemalePartnerIn', X0, X1],prv,_,_), fact(['p:hasMalePartner', X1, X2],prv,_,_) \ fact(['p:hasHusband', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasHusband', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:directSiblingOf', X, Y],prv,_,_) \ fact(['p:isSiblingOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSiblingOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasMotherInLaw', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingOf', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasParent', Y, X],prv,M1,_) \ fact(['p:isParentOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isParentOf', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['p:ParentInLaw', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isParentOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isSpouseOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_) \ fact(['p:ParentInLaw', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:ParentInLaw', X],prv,_,U), applied_rules(1,fwd).
fact(['p:brotherOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:formerlyKnownAs', X, _],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:hasParent', X, Y],prv,M1,_) \ fact(['p:hasAncestor', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAncestor', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['p:Cousin', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:hasAncestor', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isSiblingOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_), fact(['p:isParentOf', X2, X3],prv,_,_), fact(['p:Person', X3],prv,_,_) \ fact(['p:Cousin', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Cousin', X],prv,_,U), applied_rules(1,fwd).
fact(['p:GreatGrandparent', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isParentOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_), fact(['p:isParentOf', X2, X3],prv,_,_), fact(['p:Person', X3],prv,_,_) \ fact(['p:GreatGrandparent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:GreatGrandparent', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasParent', X, _],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:isUncleOf', Y, X],prv,_,_) \ fact(['p:hasUncle', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasUncle', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasUncle', Y, X],prv,_,_) \ fact(['p:isUncleOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isUncleOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasHusband', X, _],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasWife', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:formerlyKnownAs', X, Y],prv,M1,_) \ fact(['p:knownAs', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:knownAs', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOf', Y, X],prv,_,_) \ fact(['p:isFirstCousinOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isFirstCousinOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOnceRemovedOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandfather', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeMother', X, Y],prv,_,_), fact(['p:hasForeMother', Y, Z],prv,_,_) \ fact(['p:hasForeMother', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasForeMother', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['p:isAuntOf', Y, X],prv,_,_) \ fact(['p:hasAunt', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAunt', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAunt', Y, X],prv,_,_) \ fact(['p:isAuntOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isAuntOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isUncleOf', X, _],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFather', X, Y],prv,_,_) \ fact(['p:hasForeFather', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasForeFather', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_) \ fact(['p:DomainEntity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:DomainEntity', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatUncle', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isUncleInLawOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:FemaleDescendent', X],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Woman', X],prv,_,_), fact(['p:hasAncestor', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:FemaleDescendent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:FemaleDescendent', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandmother', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isPartnerIn', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasUncleInLaw', Y, X],prv,_,_) \ fact(['p:isUncleInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isUncleInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isUncleInLawOf', Y, X],prv,_,_) \ fact(['p:hasUncleInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasUncleInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:FemaleAncestor', X],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Woman', X],prv,_,_), fact(['p:isAncestorOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:FemaleAncestor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:FemaleAncestor', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isNieceOf', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isFemalePartnerIn', _, X1],prv,_,_) \ fact(['p:Marriage', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Marriage', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGender', X, Y1],prv,M1,_), fact(['p:hasGender', X, Y2],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasGender',M1),('p:hasGender',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['p:hasBrother', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAncestor', X, Y],prv,_,_), fact(['p:hasAncestor', Y, Z],prv,_,_) \ fact(['p:hasAncestor', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAncestor', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['p:Foremother', X],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Woman', X],prv,_,_), fact(['p:isForemotherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Foremother', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Foremother', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOnceRemovedOf', Y, X],prv,_,_) \ fact(['p:isFirstCousinOnceRemovedOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:directSiblingOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isBloodRelationOf', Y, X],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isAncestorOf', Y, X],prv,_,_) \ fact(['p:hasAncestor', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAncestor', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAncestor', Y, X],prv,_,_) \ fact(['p:isAncestorOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isAncestorOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasUncle', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandParent', X, Y],prv,_,_) \ fact(['p:hasAncestor', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasAncestor', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:brotherOf', X0, X1],prv,_,_), fact(['p:grandParentOf', X1, X2],prv,_,_) \ fact(['p:isGreatUncleOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGreatUncleOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:hasParent', X0, X1],prv,M1,_), fact(['p:hasGrandfather', X1, X2],prv,M2,_) \ fact(['p:hasGreatGrandfather', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasParent',M1),('p:hasGrandfather',M2)],M), fact(['p:hasGreatGrandfather', X0, X2],prv,M,U), applied_rules(1,fwd).
fact(['p:Male', X],prv,M1,_) \ fact(['p:Sex', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Sex', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:hasAncestor', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasMother', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:Female', X],prv,M1,_), fact(['p:Male', X],prv,M2,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:Female',M1),('p:Male',M2)],M), fact(['owl:Nothing', X],prv,M,U), applied_rules(1,fwd).
fact(['p:hasMotherInLaw', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatAunt', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:Sex', X],prv,_,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:Nothing', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isRelationOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isSecondCousinOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasBrotherInLaw', Y, X],prv,_,_) \ fact(['p:isSisterInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSisterInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSisterInLawOf', Y, X],prv,_,_) \ fact(['p:hasBrotherInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasBrotherInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isSpouseOf', X0, X1],prv,_,_), fact(['p:isSiblingOf', X1, X2],prv,_,_) \ fact(['p:isSiblingInLawOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSiblingInLawOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:Man', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,M1,_), fact(['p:hasGender', X, X1],prv,M2,_), fact(['p:Male', X1],prv,M3,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:Person',M1),('p:hasGender',M2),('p:Male',M3)],M), fact(['p:Man', X],prv,M,U), applied_rules(1,fwd).
fact(['p:isGreatGrandParentOf', Y, X],prv,_,_) \ fact(['p:hasGreatGrandParent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGreatGrandParent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandParent', Y, X],prv,_,_) \ fact(['p:isGreatGrandParentOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGreatGrandParentOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatAunt', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isUncleInLawOf', X, _],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isThirdCousinOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Father', X],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Man', X],prv,_,_), fact(['p:isFatherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Father', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Father', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isNephewOf', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAunt', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasAncestor', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingInLawOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:marriageYear', X, _],prv,M1,_) \ fact(['p:Marriage', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Marriage', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:brotherOf', X, _],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOf', X0, X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_) \ fact(['p:isFirstCousinOnceRemovedOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isFirstCousinOnceRemovedOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:FatherInLaw', X],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Man', X],prv,_,_), fact(['p:isFatherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isSpouseOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_) \ fact(['p:FatherInLaw', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:FatherInLaw', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandParent', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isGreatGrandfatherOf', Y, X],prv,_,_) \ fact(['p:hasGreatGrandfather', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGreatGrandfather', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandfather', Y, X],prv,_,_) \ fact(['p:isGreatGrandfatherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGreatGrandfatherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isUncleOf', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSpouseOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isInLawOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatUncle', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isBloodRelationOf', X, Y],prv,_,_), fact(['p:isBloodRelationOf', Y, Z],prv,_,_) \ fact(['p:isBloodRelationOf', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['p:GreatGrandfather', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isFatherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_), fact(['p:isParentOf', X2, X3],prv,_,_), fact(['p:Person', X3],prv,_,_) \ fact(['p:GreatGrandfather', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:GreatGrandfather', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isFirstCousinOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isMalePartnerIn', X, Y],prv,_,_) \ fact(['p:isPartnerIn', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isPartnerIn', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSecondCousinOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandParent', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandmother', X, Y],prv,_,_) \ fact(['p:hasGreatGrandParent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGreatGrandParent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasBrotherInLaw', Y, X],prv,_,_) \ fact(['p:isBrotherInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBrotherInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isBrotherInLawOf', Y, X],prv,_,_) \ fact(['p:hasBrotherInLaw', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasBrotherInLaw', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Grandmother', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isMotherOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_) \ fact(['p:Grandmother', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Grandmother', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isSpouseOf', X0, X1],prv,_,_), fact(['p:hasMother', X1, X2],prv,_,_) \ fact(['p:hasMotherInLaw', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasMotherInLaw', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:Husband', X],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Man', X],prv,_,_), fact(['p:isMalePartnerIn', X, X1],prv,_,_), fact(['p:Marriage', X1],prv,_,_), fact(['p:hasFemalePartner', X1, X2],prv,_,_), fact(['p:Woman', X2],prv,_,_) \ fact(['p:Husband', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Husband', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandmother', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isThirdCousinOf', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGender', X, _],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:hasFemalePartner', Y, X],prv,_,_) \ fact(['p:isFemalePartnerIn', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isFemalePartnerIn', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isFemalePartnerIn', Y, X],prv,_,_) \ fact(['p:hasFemalePartner', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasFemalePartner', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:InLaw', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isInLawOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:InLaw', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:InLaw', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingInLawOf', Y, X],prv,_,_) \ fact(['p:isSiblingInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSiblingInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Descendent', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:hasAncestor', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:Descendent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Descendent', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isParentInLawOf', X, Y],prv,_,_) \ fact(['p:isInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:Marriage', X],prv,_,_), fact(['p:Person', X],prv,_,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:Nothing', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isSecondCousinOf', X, Y],prv,_,_) \ fact(['p:isBloodRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isBloodRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandfather', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isBloodRelationOf', X, Y],prv,_,_) \ fact(['p:isRelationOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isRelationOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:PersonWithManySibling', X],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:hasFather', _, X1],prv,_,_) \ fact(['p:Man', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:grandParentOf', Y, X],prv,_,_) \ fact(['p:hasGrandParent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGrandParent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandParent', Y, X],prv,_,_) \ fact(['p:grandParentOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:grandParentOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:MaleDescendent', X],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Man', X],prv,_,_), fact(['p:hasAncestor', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_) \ fact(['p:MaleDescendent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:MaleDescendent', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isSonOf', X0, X1],prv,_,_), fact(['p:isSiblingOf', X1, X2],prv,_,_) \ fact(['p:isNephewOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isNephewOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:isInLawOf', Y, X],prv,_,_) \ fact(['p:isInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasParent', X0, X1],prv,M1,_), fact(['p:hasGrandmother', X1, X2],prv,M2,_) \ fact(['p:hasGreatGrandmother', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('p:hasParent',M1),('p:hasGrandmother',M2)],M), fact(['p:hasGreatGrandmother', X0, X2],prv,M,U), applied_rules(1,fwd).
fact(['p:isForemotherOf', Y, X],prv,_,_) \ fact(['p:hasForeMother', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasForeMother', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasForeMother', Y, X],prv,_,_) \ fact(['p:isForemotherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isForemotherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandmother', _, X1],prv,_,_) \ fact(['p:Woman', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isBrotherInLawOf', X, Y],prv,_,_) \ fact(['p:isSiblingInLawOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSiblingInLawOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:ParentOfSmallFamily', X],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:ParentOfLargeFamily', X],prv,M1,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['p:Aunt', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:sisterOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_) \ fact(['p:Aunt', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Aunt', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isMotherOf', Y, X],prv,_,_) \ fact(['p:hasMother', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasMother', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasMother', Y, X],prv,_,_) \ fact(['p:isMotherOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isMotherOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGrandfather', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isThirdCousinOf', Y, X],prv,_,_) \ fact(['p:isThirdCousinOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isThirdCousinOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSisterInLawOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isWifeOf', Y, X],prv,_,_) \ fact(['p:hasWife', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasWife', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:hasWife', Y, X],prv,_,_) \ fact(['p:isWifeOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isWifeOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSisterInLawOf', X, _],prv,_,_) \ fact(['p:Woman', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Woman', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasFatherInLaw', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isGreatUncleOf', X, _],prv,_,_) \ fact(['p:Man', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Man', X],prv,_,U), applied_rules(1,fwd).
fact(['p:isFemalePartnerIn', X, Y],prv,_,_) \ fact(['p:isPartnerIn', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isPartnerIn', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isAuntOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:isDaughterOf', X0, X1],prv,_,_), fact(['p:isSiblingOf', X1, X2],prv,_,_) \ fact(['p:isNieceOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isNieceOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:sisterOf', X0, X1],prv,_,_), fact(['p:grandParentOf', X1, X2],prv,_,_) \ fact(['p:isGreatAuntOf', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isGreatAuntOf', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['p:isBloodRelationOf', _, X1],prv,_,_) \ fact(['p:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['p:hasChild', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:GreatGreatGrandparent', X],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['p:Person', X],prv,_,_), fact(['p:isParentOf', X, X1],prv,_,_), fact(['p:Person', X1],prv,_,_), fact(['p:isParentOf', X1, X2],prv,_,_), fact(['p:Person', X2],prv,_,_), fact(['p:isParentOf', X2, X3],prv,_,_), fact(['p:Person', X3],prv,_,_), fact(['p:isParentOf', X3, X4],prv,_,_), fact(['p:Person', X4],prv,_,_) \ fact(['p:GreatGreatGrandparent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:GreatGreatGrandparent', X],prv,_,U), applied_rules(1,fwd).
fact(['p:hasGreatGrandfather', X, Y],prv,_,_) \ fact(['p:hasGreatGrandParent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:hasGreatGrandParent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['p:isSiblingOf', X, Y],prv,_,_), fact(['p:isSiblingOf', Y, Z],prv,_,_) \ fact(['p:isSiblingOf', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:isSiblingOf', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['p:isParentInLawOf', X, _],prv,_,_) \ fact(['p:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['p:Person', X],prv,_,U), applied_rules(1,fwd).


% - backward -
fact(['p:hasFather', X, Y],chk1,_,_), fact(['p:hasParent', X, Y],O1,M1,U1), fact(['p:maleInFamilinx', Y],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasParent', X, Y],chk1,M1,U1), fact(['p:maleInFamilinx', Y],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasMother', X, Y],chk1,_,_), fact(['p:hasParent', X, Y],O1,M1,U1), fact(['p:femaleInFamilinx', Y],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasParent', X, Y],chk1,M1,U1), fact(['p:femaleInFamilinx', Y],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasChild', X, Y],chk1,_,_), fact(['p:hasSon', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasSon', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isAuntInLawOf', X0, X3],chk1,_,_), fact(['p:isWifeOf', X0, X1],O1,M1,U1), fact(['p:brotherOf', X1, X2],O2,M2,U2), fact(['p:isParentOf', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:isWifeOf', X0, X1],chk1,M1,U1), fact(['p:brotherOf', X1, X2],chk1,M2,U2), fact(['p:isParentOf', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:hasChild', X, Y],chk1,_,_), fact(['p:hasDaughter', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasDaughter', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGreatUncle', X, Y],chk1,_,_), fact(['p:isGreatUncleOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatUncleOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isGreatUncleOf', X, Y],chk1,_,_), fact(['p:hasGreatUncle', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatUncle', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSecondCousinOf', X0, X3],chk1,_,_), fact(['p:hasGrandParent', X0, X1],O1,M1,U1), fact(['p:isSiblingOf', X1, X2],O2,M2,U2), fact(['p:grandParentOf', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:hasGrandParent', X0, X1],chk1,M1,U1), fact(['p:isSiblingOf', X1, X2],chk1,M2,U2), fact(['p:grandParentOf', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:hasGrandParent', X, Y],chk1,_,_), fact(['p:hasGrandmother', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandmother', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:knownAs', X, Y],chk1,_,_), fact(['p:alsoKnownAs', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:alsoKnownAs', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:directSiblingOf', X, Y],chk1,_,_), fact(['p:directSiblingOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:directSiblingOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['p:hasBirthYear', X, Y1],O1,M1,U1), fact(['p:hasBirthYear', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasBirthYear', X, Y1],chk1,M1,U1), fact(['p:hasBirthYear', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasHusband', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasHusband', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isRelationOf', X, Y],chk1,_,_), fact(['p:isInLawOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isInLawOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasChild', X, Y],chk1,_,_), fact(['p:isChildOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isChildOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isChildOf', X, Y],chk1,_,_), fact(['p:hasChild', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasChild', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isParentInLawOf', X, Y],chk1,_,_), fact(['p:hasParentInLaw', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasParentInLaw', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasParentInLaw', X, Y],chk1,_,_), fact(['p:isParentInLawOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isParentInLawOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isForefatherOf', X, Z],chk1,_,_), fact(['p:isForefatherOf', X, Y],O1,M1,U1), fact(['p:isForefatherOf', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isForefatherOf', X, Y],chk1,M1,U1), fact(['p:isForefatherOf', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasAunt', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAunt', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:hasGreatUncle', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatUncle', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasDeathYear', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasDeathYear', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasParentInLaw', X, Y],chk1,_,_), fact(['p:hasMotherInLaw', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMotherInLaw', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isInLawOf', X, Y],chk1,_,_), fact(['p:isAuntInLawOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isAuntInLawOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isFirstCousinOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFirstCousinOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasFatherInLaw', X0, X2],chk1,_,_), fact(['p:isSpouseOf', X0, X1],O1,M1,U1), fact(['p:hasFather', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isSpouseOf', X0, X1],chk1,M1,U1), fact(['p:hasFather', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasAncestor', X, Y],chk1,_,_), fact(['p:hasForeFather', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasForeFather', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['p:hasMother', X, Y1],O1,M1,U1), fact(['p:hasMother', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasMother', X, Y1],chk1,M1,U1), fact(['p:hasMother', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasAuntInLaw', X, Y],chk1,_,_), fact(['p:hasAuntInLaw', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAuntInLaw', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasAuntInLaw', X, Y],chk1,_,_), fact(['p:hasAuntInLaw', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAuntInLaw', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Grandparent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Grandparent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Grandparent', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isParentOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isParentOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:isAuntInLawOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isAuntInLawOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:hasUncle', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasUncle', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:alsoKnownAs', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:alsoKnownAs', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:GreatUncle', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:GreatUncle', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:GreatUncle', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:brotherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5), fact(['p:isParentOf', X2, X3],O6,M6,U6), fact(['p:Person', X3],O7,M7,U7) ==> \+member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:brotherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), fact(['p:isParentOf', X2, X3],chk1,M6,U6), fact(['p:Person', X3],chk1,M7,U7), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:hasParent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasParent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isFirstCousinOnceRemovedOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFirstCousinOnceRemovedOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:isAuntOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isAuntOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasSon', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasSon', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:DomainEntity', X],chk1,_,_), fact(['p:Marriage', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Marriage', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:hasAunt', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAunt', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isUncleOf', X0, X2],chk1,_,_), fact(['p:brotherOf', X0, X1],O1,M1,U1), fact(['p:isParentOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:brotherOf', X0, X1],chk1,M1,U1), fact(['p:isParentOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Marriage', X1],chk1,_,_), fact(['p:isPartnerIn', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isPartnerIn', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGreatGrandmother', X, Y],chk1,_,_), fact(['p:isGreatGrandmotherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatGrandmotherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isGreatGrandmotherOf', X, Y],chk1,_,_), fact(['p:hasGreatGrandmother', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandmother', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasBirthYear', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasBirthYear', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:MotherInLaw', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:MotherInLaw', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:MotherInLaw', X],chk1,_,_), fact(['p:Woman', X],O1,M1,U1), fact(['p:isMotherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isSpouseOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Woman', X],chk1,M1,U1), fact(['p:isMotherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isSpouseOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:isMalePartnerIn', X, Y],chk1,_,_), fact(['p:hasMalePartner', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMalePartner', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasMalePartner', X, Y],chk1,_,_), fact(['p:isMalePartnerIn', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isMalePartnerIn', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:hasWife', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasWife', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isAncestorOf', X, Y],chk1,_,_), fact(['p:isForefatherOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isForefatherOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Grandfather', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Grandfather', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Grandfather', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isFatherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isFatherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:Sex', X],chk1,_,_), fact(['p:Female', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Female', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:hasAncestor', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAncestor', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Uncle', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Uncle', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Uncle', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:brotherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:brotherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isNephewOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isNephewOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isRelationOf', X, Z],chk1,_,_), fact(['p:isRelationOf', X, Y],O1,M1,U1), fact(['p:isRelationOf', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isRelationOf', X, Y],chk1,M1,U1), fact(['p:isRelationOf', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGrandmother', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandmother', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isRelationOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isRelationOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:isFemalePartnerIn', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFemalePartnerIn', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:sisterOf', X, Y],chk1,_,_), fact(['p:hasSister', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasSister', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasSister', X, Y],chk1,_,_), fact(['p:sisterOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:sisterOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:directSiblingOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:directSiblingOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isThirdCousinOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isThirdCousinOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Sex', X1],chk1,_,_), fact(['p:hasGender', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGender', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasDaughter', X, Y],chk1,_,_), fact(['p:isDaughterOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isDaughterOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isDaughterOf', X, Y],chk1,_,_), fact(['p:hasDaughter', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasDaughter', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasGreatGrandfather', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandfather', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isSiblingInLawOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSiblingInLawOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasSon', X, Y],chk1,_,_), fact(['p:isSonOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSonOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSonOf', X, Y],chk1,_,_), fact(['p:hasSon', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasSon', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:DomainEntity', X],chk1,_,_), fact(['p:Sex', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Sex', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasHusband', X, Y],chk1,_,_), fact(['p:isHusbandOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isHusbandOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isHusbandOf', X, Y],chk1,_,_), fact(['p:hasHusband', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasHusband', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isInLawOf', X, Y],chk1,_,_), fact(['p:isUncleInLawOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isUncleInLawOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isParentInLawOf', X0, X2],chk1,_,_), fact(['p:isParentOf', X0, X1],O1,M1,U1), fact(['p:isSpouseOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isParentOf', X0, X1],chk1,M1,U1), fact(['p:isSpouseOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:isBrotherInLawOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isBrotherInLawOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBrotherInLawOf', X0, X2],chk1,_,_), fact(['p:hasWife', X0, X1],O1,M1,U1), fact(['p:hasBrother', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasWife', X0, X1],chk1,M1,U1), fact(['p:hasBrother', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:BloodRelation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:BloodRelation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:BloodRelation', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isBloodRelationOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isBloodRelationOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['p:Marriage', X],O1,M1,U1), fact(['p:Sex', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:Marriage', X],chk1,M1,U1), fact(['p:Sex', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasFatherInLaw', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFatherInLaw', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isSiblingOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSiblingOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasForeFather', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasForeFather', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasChild', X, Y],chk1,_,_), fact(['p:isParentOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isParentOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isParentOf', X, Y],chk1,_,_), fact(['p:hasChild', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasChild', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:directSiblingOf', X, Y],chk1,_,_), fact(['p:brotherOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:brotherOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGreatGrandParent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGrandParent', X, Y],chk1,_,_), fact(['p:hasGrandfather', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandfather', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasUncle', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasUncle', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasForeMother', X, Y],chk1,_,_), fact(['p:hasMother', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMother', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:hasGrandParent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandParent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGrandmother', X0, X2],chk1,_,_), fact(['p:hasParent', X0, X1],O1,M1,U1), fact(['p:hasMother', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasParent', X0, X1],chk1,M1,U1), fact(['p:hasMother', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:isSisterInLawOf', X0, X2],chk1,_,_), fact(['p:hasWife', X0, X1],O1,M1,U1), fact(['p:hasBrother', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasWife', X0, X1],chk1,M1,U1), fact(['p:hasBrother', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isAuntInLawOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isAuntInLawOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:sisterOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:sisterOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:Wife', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Wife', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Wife', X],chk1,_,_), fact(['p:Woman', X],O1,M1,U1), fact(['p:isFemalePartnerIn', X, X1],O2,M2,U2), fact(['p:Marriage', X1],O3,M3,U3), fact(['p:hasMalePartner', X1, X2],O4,M4,U4), fact(['p:Man', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Woman', X],chk1,M1,U1), fact(['p:isFemalePartnerIn', X, X1],chk1,M2,U2), fact(['p:Marriage', X1],chk1,M3,U3), fact(['p:hasMalePartner', X1, X2],chk1,M4,U4), fact(['p:Man', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['p:hasDeathYear', X, Y1],O1,M1,U1), fact(['p:hasDeathYear', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasDeathYear', X, Y1],chk1,M1,U1), fact(['p:hasDeathYear', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:isPartnerIn', X, Y],chk1,_,_), fact(['p:hasPartner', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasPartner', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasPartner', X, Y],chk1,_,_), fact(['p:isPartnerIn', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isPartnerIn', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:directSiblingOf', X, Y],chk1,_,_), fact(['p:sisterOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:sisterOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasForeFather', X, Y],chk1,_,_), fact(['p:isForefatherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isForefatherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isForefatherOf', X, Y],chk1,_,_), fact(['p:hasForeFather', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasForeFather', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasFather', X, Y],chk1,_,_), fact(['p:isFatherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFatherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isFatherOf', X, Y],chk1,_,_), fact(['p:hasFather', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFather', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isSpouseOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSpouseOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isUncleInLawOf', X0, X3],chk1,_,_), fact(['p:isHusbandOf', X0, X1],O1,M1,U1), fact(['p:sisterOf', X1, X2],O2,M2,U2), fact(['p:isParentOf', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:isHusbandOf', X0, X1],chk1,M1,U1), fact(['p:sisterOf', X1, X2],chk1,M2,U2), fact(['p:isParentOf', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasForeMother', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasForeMother', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:ThirdCousin', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:ThirdCousin', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:ThirdCousin', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:hasParent', X, X1],O2,M2,U2), fact(['p:hasParent', X1, X2],O3,M3,U3), fact(['p:Person', X2],O4,M4,U4), fact(['p:hasParent', X2, X3],O5,M5,U5), fact(['p:Person', X3],O6,M6,U6), fact(['p:isSiblingOf', X3, X4],O7,M7,U7), fact(['p:Person', X4],O8,M8,U8), fact(['p:isParentOf', X4, X5],O9,M9,U9), fact(['p:Person', X5],O10,M10,U10), fact(['p:isParentOf', X5, X6],O11,M11,U11), fact(['p:Person', X6],O12,M12,U12), fact(['p:isParentOf', X6, X7],O13,M13,U13), fact(['p:Person', X7],O14,M14,U14) ==> \+member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:hasParent', X, X1],chk1,M2,U2), fact(['p:hasParent', X1, X2],chk1,M3,U3), fact(['p:Person', X2],chk1,M4,U4), fact(['p:hasParent', X2, X3],chk1,M5,U5), fact(['p:Person', X3],chk1,M6,U6), fact(['p:isSiblingOf', X3, X4],chk1,M7,U7), fact(['p:Person', X4],chk1,M8,U8), fact(['p:isParentOf', X4, X5],chk1,M9,U9), fact(['p:Person', X5],chk1,M10,U10), fact(['p:isParentOf', X5, X6],chk1,M11,U11), fact(['p:Person', X6],chk1,M12,U12), fact(['p:isParentOf', X6, X7],chk1,M13,U13), fact(['p:Person', X7],chk1,M14,U14), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Woman', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Woman', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:hasGender', X, X1],O2,M2,U2), fact(['p:Female', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:hasGender', X, X1],chk1,M2,U2), fact(['p:Female', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:isFirstCousinOf', X0, X3],chk1,_,_), fact(['p:hasParent', X0, X1],O1,M1,U1), fact(['p:isSiblingOf', X1, X2],O2,M2,U2), fact(['p:isParentOf', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:hasParent', X0, X1],chk1,M1,U1), fact(['p:isSiblingOf', X1, X2],chk1,M2,U2), fact(['p:isParentOf', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:hasAncestor', X, Y],chk1,_,_), fact(['p:hasForeMother', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasForeMother', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSpouseOf', X, Y],chk1,_,_), fact(['p:isSpouseOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSpouseOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isAuntOf', X0, X2],chk1,_,_), fact(['p:sisterOf', X0, X1],O1,M1,U1), fact(['p:isParentOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:sisterOf', X0, X1],chk1,M1,U1), fact(['p:isParentOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isFirstCousinOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFirstCousinOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasAncestor', X, Y],chk1,_,_), fact(['p:hasGreatGrandParent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandParent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSiblingInLawOf', X, Y],chk1,_,_), fact(['p:isSisterInLawOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSisterInLawOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGreatAunt', X, Y],chk1,_,_), fact(['p:isGreatAuntOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatAuntOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isGreatAuntOf', X, Y],chk1,_,_), fact(['p:hasGreatAunt', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatAunt', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Spouse', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Spouse', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Spouse', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isSpouseOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isSpouseOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:Marriage', X1],chk1,_,_), fact(['p:isMalePartnerIn', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isMalePartnerIn', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasMother', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMother', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isBrotherInLawOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isBrotherInLawOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:Mother', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Mother', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Mother', X],chk1,_,_), fact(['p:Woman', X],O1,M1,U1), fact(['p:isMotherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Woman', X],chk1,M1,U1), fact(['p:isMotherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasDaughter', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasDaughter', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isUncleOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isUncleOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:FirstCousin', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:FirstCousin', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:FirstCousin', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:hasParent', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isSiblingOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5), fact(['p:isParentOf', X2, X3],O6,M6,U6), fact(['p:Person', X3],O7,M7,U7) ==> \+member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:hasParent', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isSiblingOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), fact(['p:isParentOf', X2, X3],chk1,M6,U6), fact(['p:Person', X3],chk1,M7,U7), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isBloodRelationOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isBloodRelationOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasMotherInLaw', X, Y],chk1,_,_), fact(['p:isMotherInLawOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isMotherInLawOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isMotherInLawOf', X, Y],chk1,_,_), fact(['p:hasMotherInLaw', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMotherInLaw', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isGreatAuntOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatAuntOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasFamilyName', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFamilyName', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGrandfather', X0, X2],chk1,_,_), fact(['p:hasParent', X0, X1],O1,M1,U1), fact(['p:hasFather', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasParent', X0, X1],chk1,M1,U1), fact(['p:hasFather', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Son', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Son', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Son', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isSonOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isSonOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:isThirdCousinOf', X0, X3],chk1,_,_), fact(['p:hasGreatGrandParent', X0, X1],O1,M1,U1), fact(['p:isSiblingOf', X1, X2],O2,M2,U2), fact(['p:isGreatGrandParentOf', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:hasGreatGrandParent', X0, X1],chk1,M1,U1), fact(['p:isSiblingOf', X1, X2],chk1,M2,U2), fact(['p:isGreatGrandParentOf', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:hasGrandfather', X, Y],chk1,_,_), fact(['p:isGrandfatherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGrandfatherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isGrandfatherOf', X, Y],chk1,_,_), fact(['p:hasGrandfather', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandfather', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSpouseOf', X, Y],chk1,_,_), fact(['p:hasWife', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasWife', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Daughter', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Daughter', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Daughter', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isDaughterOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isDaughterOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:hasParentInLaw', X, Y],chk1,_,_), fact(['p:hasFatherInLaw', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFatherInLaw', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:MaleAncestor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:MaleAncestor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:MaleAncestor', X],chk1,_,_), fact(['p:Man', X],O1,M1,U1), fact(['p:isAncestorOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Man', X],chk1,M1,U1), fact(['p:isAncestorOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:hasFatherInLaw', X, Y],chk1,_,_), fact(['p:isFatherInLawOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFatherInLawOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isFatherInLawOf', X, Y],chk1,_,_), fact(['p:hasFatherInLaw', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFatherInLaw', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasDaughter', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasDaughter', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['p:hasFather', X, Y1],O1,M1,U1), fact(['p:hasFather', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasFather', X, Y1],chk1,M1,U1), fact(['p:hasFather', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasForeFather', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasForeFather', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isInLawOf', X, Y],chk1,_,_), fact(['p:isSpouseOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSpouseOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:brotherOf', X, Y],chk1,_,_), fact(['p:hasBrother', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasBrother', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasBrother', X, Y],chk1,_,_), fact(['p:brotherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:brotherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:sisterOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:sisterOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Parent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Parent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Parent', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isParentOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isParentOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:isMalePartnerIn', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isMalePartnerIn', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasSon', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasSon', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:isGreatAuntOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatAuntOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:isNephewOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isNephewOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isFirstCousinOnceRemovedOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:Forefather', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Forefather', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Forefather', X],chk1,_,_), fact(['p:Man', X],O1,M1,U1), fact(['p:isForefatherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Man', X],chk1,M1,U1), fact(['p:isForefatherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasForeMother', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasForeMother', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:isNieceOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isNieceOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isInLawOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isInLawOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:SecondCousin', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:SecondCousin', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:SecondCousin', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:hasParent', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:hasParent', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5), fact(['p:isSiblingOf', X2, X3],O6,M6,U6), fact(['p:Person', X3],O7,M7,U7), fact(['p:isParentOf', X3, X4],O8,M8,U8), fact(['p:Person', X4],O9,M9,U9), fact(['p:isParentOf', X4, X5],O10,M10,U10), fact(['p:Person', X5],O11,M11,U11) ==> \+member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:hasParent', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:hasParent', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), fact(['p:isSiblingOf', X2, X3],chk1,M6,U6), fact(['p:Person', X3],chk1,M7,U7), fact(['p:isParentOf', X3, X4],chk1,M8,U8), fact(['p:Person', X4],chk1,M9,U9), fact(['p:isParentOf', X4, X5],chk1,M10,U10), fact(['p:Person', X5],chk1,M11,U11), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:hasChild', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasChild', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isRelationOf', X, Y],chk1,_,_), fact(['p:isRelationOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isRelationOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSecondCousinOf', X, Y],chk1,_,_), fact(['p:isSecondCousinOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSecondCousinOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isNieceOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isNieceOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGrandmother', X, Y],chk1,_,_), fact(['p:isGrandmotherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGrandmotherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isGrandmotherOf', X, Y],chk1,_,_), fact(['p:hasGrandmother', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandmother', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isInLawOf', X, Y],chk1,_,_), fact(['p:isSiblingInLawOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Ancestor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Ancestor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Ancestor', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isAncestorOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isAncestorOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasGreatAunt', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatAunt', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSiblingOf', X, Y],chk1,_,_), fact(['p:isSiblingOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSiblingOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isAncestorOf', X, Y],chk1,_,_), fact(['p:isForemotherOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isForemotherOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isForemotherOf', X, Z],chk1,_,_), fact(['p:isForemotherOf', X, Y],O1,M1,U1), fact(['p:isForemotherOf', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isForemotherOf', X, Y],chk1,M1,U1), fact(['p:isForemotherOf', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasForeFather', X, Z],chk1,_,_), fact(['p:hasForeFather', X, Y],O1,M1,U1), fact(['p:hasForeFather', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasForeFather', X, Y],chk1,M1,U1), fact(['p:hasForeFather', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:isSpouseOf', X, Y],chk1,_,_), fact(['p:hasHusband', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasHusband', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isParentInLawOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isParentInLawOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:knownAs', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:knownAs', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasBrother', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasBrother', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isGreatUncleOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatUncleOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasFather', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFather', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasWife', X0, X2],chk1,_,_), fact(['p:isMalePartnerIn', X0, X1],O1,M1,U1), fact(['p:hasFemalePartner', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isMalePartnerIn', X0, X1],chk1,M1,U1), fact(['p:hasFemalePartner', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasHusband', X0, X2],chk1,_,_), fact(['p:isFemalePartnerIn', X0, X1],O1,M1,U1), fact(['p:hasMalePartner', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isFemalePartnerIn', X0, X1],chk1,M1,U1), fact(['p:hasMalePartner', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:isSiblingOf', X, Y],chk1,_,_), fact(['p:directSiblingOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:directSiblingOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasMotherInLaw', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMotherInLaw', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isSiblingOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSiblingOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isParentOf', X, Y],chk1,_,_), fact(['p:hasParent', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasParent', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:ParentInLaw', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:ParentInLaw', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:ParentInLaw', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isParentOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isSpouseOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isParentOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isSpouseOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:brotherOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:brotherOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:formerlyKnownAs', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:formerlyKnownAs', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasAncestor', X, Y],chk1,_,_), fact(['p:hasParent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasParent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Cousin', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Cousin', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Cousin', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:hasAncestor', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isSiblingOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5), fact(['p:isParentOf', X2, X3],O6,M6,U6), fact(['p:Person', X3],O7,M7,U7) ==> \+member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:hasAncestor', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isSiblingOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), fact(['p:isParentOf', X2, X3],chk1,M6,U6), fact(['p:Person', X3],chk1,M7,U7), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:GreatGrandparent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:GreatGrandparent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:GreatGrandparent', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isParentOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5), fact(['p:isParentOf', X2, X3],O6,M6,U6), fact(['p:Person', X3],O7,M7,U7) ==> \+member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isParentOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), fact(['p:isParentOf', X2, X3],chk1,M6,U6), fact(['p:Person', X3],chk1,M7,U7), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasParent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasParent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasUncle', X, Y],chk1,_,_), fact(['p:isUncleOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isUncleOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isUncleOf', X, Y],chk1,_,_), fact(['p:hasUncle', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasUncle', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:hasHusband', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasHusband', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasWife', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasWife', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:knownAs', X, Y],chk1,_,_), fact(['p:formerlyKnownAs', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:formerlyKnownAs', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isFirstCousinOf', X, Y],chk1,_,_), fact(['p:isFirstCousinOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFirstCousinOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isFirstCousinOnceRemovedOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasGrandfather', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandfather', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasForeMother', X, Z],chk1,_,_), fact(['p:hasForeMother', X, Y],O1,M1,U1), fact(['p:hasForeMother', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasForeMother', X, Y],chk1,M1,U1), fact(['p:hasForeMother', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasAunt', X, Y],chk1,_,_), fact(['p:isAuntOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isAuntOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isAuntOf', X, Y],chk1,_,_), fact(['p:hasAunt', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAunt', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:isUncleOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isUncleOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasForeFather', X, Y],chk1,_,_), fact(['p:hasFather', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFather', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:DomainEntity', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Person', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGreatUncle', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatUncle', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isUncleInLawOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isUncleInLawOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:FemaleDescendent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:FemaleDescendent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:FemaleDescendent', X],chk1,_,_), fact(['p:Woman', X],O1,M1,U1), fact(['p:hasAncestor', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Woman', X],chk1,M1,U1), fact(['p:hasAncestor', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGreatGrandmother', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandmother', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isPartnerIn', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isPartnerIn', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isUncleInLawOf', X, Y],chk1,_,_), fact(['p:hasUncleInLaw', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasUncleInLaw', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasUncleInLaw', X, Y],chk1,_,_), fact(['p:isUncleInLawOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isUncleInLawOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:FemaleAncestor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:FemaleAncestor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:FemaleAncestor', X],chk1,_,_), fact(['p:Woman', X],O1,M1,U1), fact(['p:isAncestorOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Woman', X],chk1,M1,U1), fact(['p:isAncestorOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isNieceOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isNieceOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Marriage', X1],chk1,_,_), fact(['p:isFemalePartnerIn', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFemalePartnerIn', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['p:hasGender', X, Y1],O1,M1,U1), fact(['p:hasGender', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasGender', X, Y1],chk1,M1,U1), fact(['p:hasGender', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasBrother', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasBrother', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasAncestor', X, Z],chk1,_,_), fact(['p:hasAncestor', X, Y],O1,M1,U1), fact(['p:hasAncestor', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasAncestor', X, Y],chk1,M1,U1), fact(['p:hasAncestor', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:Foremother', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Foremother', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Foremother', X],chk1,_,_), fact(['p:Woman', X],O1,M1,U1), fact(['p:isForemotherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Woman', X],chk1,M1,U1), fact(['p:isForemotherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:isFirstCousinOnceRemovedOf', X, Y],chk1,_,_), fact(['p:isFirstCousinOnceRemovedOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFirstCousinOnceRemovedOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:directSiblingOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:directSiblingOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isBloodRelationOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isBloodRelationOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasAncestor', X, Y],chk1,_,_), fact(['p:isAncestorOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isAncestorOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isAncestorOf', X, Y],chk1,_,_), fact(['p:hasAncestor', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAncestor', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasUncle', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasUncle', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasAncestor', X, Y],chk1,_,_), fact(['p:hasGrandParent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandParent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isGreatUncleOf', X0, X2],chk1,_,_), fact(['p:brotherOf', X0, X1],O1,M1,U1), fact(['p:grandParentOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:brotherOf', X0, X1],chk1,M1,U1), fact(['p:grandParentOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasGreatGrandfather', X0, X2],chk1,_,_), fact(['p:hasParent', X0, X1],O1,M1,U1), fact(['p:hasGrandfather', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasParent', X0, X1],chk1,M1,U1), fact(['p:hasGrandfather', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Sex', X],chk1,_,_), fact(['p:Male', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Male', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:hasAncestor', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAncestor', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasMother', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMother', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['p:Female', X],O1,M1,U1), fact(['p:Male', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:Female', X],chk1,M1,U1), fact(['p:Male', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasMotherInLaw', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMotherInLaw', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:hasGreatAunt', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatAunt', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:Sex', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:Sex', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isRelationOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isRelationOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isSecondCousinOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSecondCousinOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSisterInLawOf', X, Y],chk1,_,_), fact(['p:hasBrotherInLaw', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasBrotherInLaw', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasBrotherInLaw', X, Y],chk1,_,_), fact(['p:isSisterInLawOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSisterInLawOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isSiblingOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSiblingOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSiblingInLawOf', X0, X2],chk1,_,_), fact(['p:isSpouseOf', X0, X1],O1,M1,U1), fact(['p:isSiblingOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isSpouseOf', X0, X1],chk1,M1,U1), fact(['p:isSiblingOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Man', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Man', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:hasGender', X, X1],O2,M2,U2), fact(['p:Male', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:hasGender', X, X1],chk1,M2,U2), fact(['p:Male', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:hasGreatGrandParent', X, Y],chk1,_,_), fact(['p:isGreatGrandParentOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatGrandParentOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isGreatGrandParentOf', X, Y],chk1,_,_), fact(['p:hasGreatGrandParent', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandParent', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGreatAunt', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatAunt', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:isUncleInLawOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isUncleInLawOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isThirdCousinOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isThirdCousinOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:Father', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Father', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Father', X],chk1,_,_), fact(['p:Man', X],O1,M1,U1), fact(['p:isFatherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Man', X],chk1,M1,U1), fact(['p:isFatherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isNephewOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isNephewOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasAunt', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAunt', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasAncestor', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasAncestor', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isSiblingInLawOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSiblingInLawOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Marriage', X],chk1,_,_), fact(['p:marriageYear', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:marriageYear', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:brotherOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:brotherOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isFirstCousinOnceRemovedOf', X0, X2],chk1,_,_), fact(['p:isFirstCousinOf', X0, X1],O1,M1,U1), fact(['p:isParentOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isFirstCousinOf', X0, X1],chk1,M1,U1), fact(['p:isParentOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:FatherInLaw', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:FatherInLaw', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:FatherInLaw', X],chk1,_,_), fact(['p:Man', X],O1,M1,U1), fact(['p:isFatherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isSpouseOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Man', X],chk1,M1,U1), fact(['p:isFatherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isSpouseOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:hasGreatGrandParent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandParent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGreatGrandfather', X, Y],chk1,_,_), fact(['p:isGreatGrandfatherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatGrandfatherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isGreatGrandfatherOf', X, Y],chk1,_,_), fact(['p:hasGreatGrandfather', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandfather', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isUncleOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isUncleOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isSpouseOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSpouseOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isInLawOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isInLawOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasGreatUncle', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatUncle', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Z],chk1,_,_), fact(['p:isBloodRelationOf', X, Y],O1,M1,U1), fact(['p:isBloodRelationOf', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isBloodRelationOf', X, Y],chk1,M1,U1), fact(['p:isBloodRelationOf', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:GreatGrandfather', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:GreatGrandfather', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:GreatGrandfather', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isFatherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5), fact(['p:isParentOf', X2, X3],O6,M6,U6), fact(['p:Person', X3],O7,M7,U7) ==> \+member(del,[O1,O2,O3,O4,O5,O6,O7]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isFatherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), fact(['p:isParentOf', X2, X3],chk1,M6,U6), fact(['p:Person', X3],chk1,M7,U7), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isFirstCousinOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFirstCousinOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isPartnerIn', X, Y],chk1,_,_), fact(['p:isMalePartnerIn', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isMalePartnerIn', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isSecondCousinOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSecondCousinOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGrandParent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandParent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGreatGrandParent', X, Y],chk1,_,_), fact(['p:hasGreatGrandmother', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandmother', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBrotherInLawOf', X, Y],chk1,_,_), fact(['p:hasBrotherInLaw', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasBrotherInLaw', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasBrotherInLaw', X, Y],chk1,_,_), fact(['p:isBrotherInLawOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isBrotherInLawOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Grandmother', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Grandmother', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Grandmother', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isMotherOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isMotherOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:hasMotherInLaw', X0, X2],chk1,_,_), fact(['p:isSpouseOf', X0, X1],O1,M1,U1), fact(['p:hasMother', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isSpouseOf', X0, X1],chk1,M1,U1), fact(['p:hasMother', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:Husband', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Husband', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Husband', X],chk1,_,_), fact(['p:Man', X],O1,M1,U1), fact(['p:isMalePartnerIn', X, X1],O2,M2,U2), fact(['p:Marriage', X1],O3,M3,U3), fact(['p:hasFemalePartner', X1, X2],O4,M4,U4), fact(['p:Woman', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Man', X],chk1,M1,U1), fact(['p:isMalePartnerIn', X, X1],chk1,M2,U2), fact(['p:Marriage', X1],chk1,M3,U3), fact(['p:hasFemalePartner', X1, X2],chk1,M4,U4), fact(['p:Woman', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasGrandmother', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandmother', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isThirdCousinOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isThirdCousinOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGender', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGender', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isFemalePartnerIn', X, Y],chk1,_,_), fact(['p:hasFemalePartner', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFemalePartner', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasFemalePartner', X, Y],chk1,_,_), fact(['p:isFemalePartnerIn', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFemalePartnerIn', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:InLaw', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:InLaw', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:InLaw', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isInLawOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isInLawOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:isSiblingInLawOf', X, Y],chk1,_,_), fact(['p:isSiblingInLawOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSiblingInLawOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Descendent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Descendent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Descendent', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:hasAncestor', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:hasAncestor', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:isInLawOf', X, Y],chk1,_,_), fact(['p:isParentInLawOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isParentInLawOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['p:Marriage', X],O1,M1,U1), fact(['p:Person', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:Marriage', X],chk1,M1,U1), fact(['p:Person', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:isBloodRelationOf', X, Y],chk1,_,_), fact(['p:isSecondCousinOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSecondCousinOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGreatGrandfather', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandfather', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isRelationOf', X, Y],chk1,_,_), fact(['p:isBloodRelationOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isBloodRelationOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:PersonWithManySibling', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:PersonWithManySibling', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X1],chk1,_,_), fact(['p:hasFather', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFather', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGrandParent', X, Y],chk1,_,_), fact(['p:grandParentOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:grandParentOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:grandParentOf', X, Y],chk1,_,_), fact(['p:hasGrandParent', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandParent', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:MaleDescendent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:MaleDescendent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:MaleDescendent', X],chk1,_,_), fact(['p:Man', X],O1,M1,U1), fact(['p:hasAncestor', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['p:Man', X],chk1,M1,U1), fact(['p:hasAncestor', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['p:isNephewOf', X0, X2],chk1,_,_), fact(['p:isSonOf', X0, X1],O1,M1,U1), fact(['p:isSiblingOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isSonOf', X0, X1],chk1,M1,U1), fact(['p:isSiblingOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:isInLawOf', X, Y],chk1,_,_), fact(['p:isInLawOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isInLawOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasGreatGrandmother', X0, X2],chk1,_,_), fact(['p:hasParent', X0, X1],O1,M1,U1), fact(['p:hasGrandmother', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:hasParent', X0, X1],chk1,M1,U1), fact(['p:hasGrandmother', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:hasForeMother', X, Y],chk1,_,_), fact(['p:isForemotherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isForemotherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isForemotherOf', X, Y],chk1,_,_), fact(['p:hasForeMother', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasForeMother', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X1],chk1,_,_), fact(['p:hasGreatGrandmother', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandmother', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSiblingInLawOf', X, Y],chk1,_,_), fact(['p:isBrotherInLawOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isBrotherInLawOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:ParentOfSmallFamily', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:ParentOfSmallFamily', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:ParentOfLargeFamily', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:ParentOfLargeFamily', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:Aunt', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:Aunt', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Aunt', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:sisterOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5) ==> \+member(del,[O1,O2,O3,O4,O5]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:sisterOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), applied_rules(1,bwd).
fact(['p:hasMother', X, Y],chk1,_,_), fact(['p:isMotherOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isMotherOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isMotherOf', X, Y],chk1,_,_), fact(['p:hasMother', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasMother', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasGrandfather', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGrandfather', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isThirdCousinOf', X, Y],chk1,_,_), fact(['p:isThirdCousinOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isThirdCousinOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isSisterInLawOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSisterInLawOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:hasWife', X, Y],chk1,_,_), fact(['p:isWifeOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isWifeOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isWifeOf', X, Y],chk1,_,_), fact(['p:hasWife', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasWife', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Woman', X],chk1,_,_), fact(['p:isSisterInLawOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isSisterInLawOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasFatherInLaw', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasFatherInLaw', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Man', X],chk1,_,_), fact(['p:isGreatUncleOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isGreatUncleOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isPartnerIn', X, Y],chk1,_,_), fact(['p:isFemalePartnerIn', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isFemalePartnerIn', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isAuntOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isAuntOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isNieceOf', X0, X2],chk1,_,_), fact(['p:isDaughterOf', X0, X1],O1,M1,U1), fact(['p:isSiblingOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isDaughterOf', X0, X1],chk1,M1,U1), fact(['p:isSiblingOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:isGreatAuntOf', X0, X2],chk1,_,_), fact(['p:sisterOf', X0, X1],O1,M1,U1), fact(['p:grandParentOf', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:sisterOf', X0, X1],chk1,M1,U1), fact(['p:grandParentOf', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X1],chk1,_,_), fact(['p:isBloodRelationOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isBloodRelationOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:hasChild', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasChild', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:GreatGreatGrandparent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:GreatGreatGrandparent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:GreatGreatGrandparent', X],chk1,_,_), fact(['p:Person', X],O1,M1,U1), fact(['p:isParentOf', X, X1],O2,M2,U2), fact(['p:Person', X1],O3,M3,U3), fact(['p:isParentOf', X1, X2],O4,M4,U4), fact(['p:Person', X2],O5,M5,U5), fact(['p:isParentOf', X2, X3],O6,M6,U6), fact(['p:Person', X3],O7,M7,U7), fact(['p:isParentOf', X3, X4],O8,M8,U8), fact(['p:Person', X4],O9,M9,U9) ==> \+member(del,[O1,O2,O3,O4,O5,O6,O7,O8,O9]) | fact(['p:Person', X],chk1,M1,U1), fact(['p:isParentOf', X, X1],chk1,M2,U2), fact(['p:Person', X1],chk1,M3,U3), fact(['p:isParentOf', X1, X2],chk1,M4,U4), fact(['p:Person', X2],chk1,M5,U5), fact(['p:isParentOf', X2, X3],chk1,M6,U6), fact(['p:Person', X3],chk1,M7,U7), fact(['p:isParentOf', X3, X4],chk1,M8,U8), fact(['p:Person', X4],chk1,M9,U9), applied_rules(1,bwd).
fact(['p:hasGreatGrandParent', X, Y],chk1,_,_), fact(['p:hasGreatGrandfather', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:hasGreatGrandfather', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['p:isSiblingOf', X, Z],chk1,_,_), fact(['p:isSiblingOf', X, Y],O1,M1,U1), fact(['p:isSiblingOf', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['p:isSiblingOf', X, Y],chk1,M1,U1), fact(['p:isSiblingOf', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['p:Person', X],chk1,_,_), fact(['p:isParentInLawOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['p:isParentInLawOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).

	
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
phase(5), fact(['p:hasParent', X, Y],add,M1,U1), fact(['p:maleInFamilinx', Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasParent',M1),('p:maleInFamilinx',M2)],M), fact(['p:hasFather', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, Y],add,M1,U1), fact(['p:femaleInFamilinx', Y],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasParent',M1),('p:femaleInFamilinx',M2)],M), fact(['p:hasMother', X, Y],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isWifeOf', X0, X1],add,M1,U1), fact(['p:brotherOf', X1, X2],add,M2,U2), fact(['p:isParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:isWifeOf',M1),('p:brotherOf',M2),('p:isParentOf',M3)],M), fact(['p:isAuntInLawOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatUncleOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatUncle', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatUncleOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2), fact(['p:grandParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:hasGrandParent',M1),('p:isSiblingOf',M2),('p:grandParentOf',M3)],M), fact(['p:isSecondCousinOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:alsoKnownAs', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:knownAs', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:directSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBirthYear', X, Y1],add,M1,U1), fact(['p:hasBirthYear', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasBirthYear',M1),('p:hasBirthYear',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isChildOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasChild', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isChildOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParentInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isParentInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', X, Y],add,M1,U1), fact(['p:isForefatherOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isForefatherOf',M1),('p:isForefatherOf',M2)],M), fact(['p:isForefatherOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasDeathYear', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,M1,U1), fact(['p:hasFather', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isSpouseOf',M1),('p:hasFather',M2)],M), fact(['p:hasFatherInLaw', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', X, Y1],add,M1,U1), fact(['p:hasMother', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasMother',M1),('p:hasMother',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasAuntInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAuntInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAuntInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAuntInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Grandparent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Person',M1),('p:isParentOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5)],M), fact(['p:Grandparent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:alsoKnownAs', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:GreatUncle', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:brotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([('p:Person',M1),('p:brotherOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5),('p:isParentOf',M6),('p:Person',M7)],M), fact(['p:GreatUncle', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:DomainEntity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X0, X1],add,M1,U1), fact(['p:isParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:brotherOf',M1),('p:isParentOf',M2)],M), fact(['p:isUncleOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandmotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandmother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandmotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBirthYear', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:MotherInLaw', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isMotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSpouseOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Woman',M1),('p:isMotherOf',M2),('p:Person',M3),('p:isSpouseOf',M4),('p:Person',M5)],M), fact(['p:MotherInLaw', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasMalePartner', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isMalePartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasMalePartner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Grandfather', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isFatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Person',M1),('p:isFatherOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5)],M), fact(['p:Grandfather', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Female', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Sex', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Uncle', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:brotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Person',M1),('p:brotherOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5)],M), fact(['p:Uncle', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', X, Y],add,M1,U1), fact(['p:isRelationOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isRelationOf',M1),('p:isRelationOf',M2)],M), fact(['p:isRelationOf', X, Z],add,M,U), applied_rules(1,ins).
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
phase(5), fact(['p:isParentOf', X0, X1],add,M1,U1), fact(['p:isSpouseOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isParentOf',M1),('p:isSpouseOf',M2)],M), fact(['p:isParentInLawOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X0, X1],add,M1,U1), fact(['p:hasBrother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasWife',M1),('p:hasBrother',M2)],M), fact(['p:isBrotherInLawOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:BloodRelation', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isBloodRelationOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:isBloodRelationOf',M2),('p:Person',M3)],M), fact(['p:BloodRelation', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,M1,U1), fact(['p:Sex', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:Marriage',M1),('p:Sex',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
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
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:hasMother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasParent',M1),('p:hasMother',M2)],M), fact(['p:hasGrandmother', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X0, X1],add,M1,U1), fact(['p:hasBrother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasWife',M1),('p:hasBrother',M2)],M), fact(['p:isSisterInLawOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Wife', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isFemalePartnerIn', X, X1],add,M2,U2), fact(['p:Marriage', X1],add,M3,U3), fact(['p:hasMalePartner', X1, X2],add,M4,U4), fact(['p:Man', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Woman',M1),('p:isFemalePartnerIn',M2),('p:Marriage',M3),('p:hasMalePartner',M4),('p:Man',M5)],M), fact(['p:Wife', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasDeathYear', X, Y1],add,M1,U1), fact(['p:hasDeathYear', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasDeathYear',M1),('p:hasDeathYear',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasPartner', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isPartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasPartner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:directSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForefatherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasForeFather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isForefatherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFatherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasFather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFatherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isHusbandOf', X0, X1],add,M1,U1), fact(['p:sisterOf', X1, X2],add,M2,U2), fact(['p:isParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:isHusbandOf',M1),('p:sisterOf',M2),('p:isParentOf',M3)],M), fact(['p:isUncleInLawOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:ThirdCousin', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasParent', X, X1],add,M2,U2), fact(['p:hasParent', X1, X2],add,M3,U3), fact(['p:Person', X2],add,M4,U4), fact(['p:hasParent', X2, X3],add,M5,U5), fact(['p:Person', X3],add,M6,U6), fact(['p:isSiblingOf', X3, X4],add,M7,U7), fact(['p:Person', X4],add,M8,U8), fact(['p:isParentOf', X4, X5],add,M9,U9), fact(['p:Person', X5],add,M10,U10), fact(['p:isParentOf', X5, X6],add,M11,U11), fact(['p:Person', X6],add,M12,U12), fact(['p:isParentOf', X6, X7],add,M13,U13), fact(['p:Person', X7],add,M14,U14) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9,U10,U11,U12,U13,U14]) | check_neg_mark([('p:Person',M1),('p:hasParent',M2),('p:hasParent',M3),('p:Person',M4),('p:hasParent',M5),('p:Person',M6),('p:isSiblingOf',M7),('p:Person',M8),('p:isParentOf',M9),('p:Person',M10),('p:isParentOf',M11),('p:Person',M12),('p:isParentOf',M13),('p:Person',M14)],M), fact(['p:ThirdCousin', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasGender', X, X1],add,M2,U2), fact(['p:Female', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:hasGender',M2),('p:Female',M3)],M), fact(['p:Woman', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2), fact(['p:isParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:hasParent',M1),('p:isSiblingOf',M2),('p:isParentOf',M3)],M), fact(['p:isFirstCousinOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X0, X1],add,M1,U1), fact(['p:isParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:sisterOf',M1),('p:isParentOf',M2)],M), fact(['p:isAuntOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatAunt', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatAuntOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Spouse', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isSpouseOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:isSpouseOf',M2),('p:Person',M3)],M), fact(['p:Spouse', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Mother', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isMotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Woman',M1),('p:isMotherOf',M2),('p:Person',M3)],M), fact(['p:Mother', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:FirstCousin', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasParent', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSiblingOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([('p:Person',M1),('p:hasParent',M2),('p:Person',M3),('p:isSiblingOf',M4),('p:Person',M5),('p:isParentOf',M6),('p:Person',M7)],M), fact(['p:FirstCousin', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isMotherInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasMotherInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isMotherInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFamilyName', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:hasFather', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasParent',M1),('p:hasFather',M2)],M), fact(['p:hasGrandfather', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Son', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isSonOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:isSonOf',M2),('p:Person',M3)],M), fact(['p:Son', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2), fact(['p:isGreatGrandParentOf', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:hasGreatGrandParent',M1),('p:isSiblingOf',M2),('p:isGreatGrandParentOf',M3)],M), fact(['p:isThirdCousinOf', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isGrandfatherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandfather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGrandfatherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Daughter', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isDaughterOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:isDaughterOf',M2),('p:Person',M3)],M), fact(['p:Daughter', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasParentInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:MaleAncestor', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isAncestorOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Man',M1),('p:isAncestorOf',M2),('p:Person',M3)],M), fact(['p:MaleAncestor', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFatherInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasFatherInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFatherInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFatherInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasDaughter', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, Y1],add,M1,U1), fact(['p:hasFather', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasFather',M1),('p:hasFather',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:brotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasBrother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Parent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:isParentOf',M2),('p:Person',M3)],M), fact(['p:Parent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasSon', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatAuntOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Forefather', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isForefatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Man',M1),('p:isForefatherOf',M2),('p:Person',M3)],M), fact(['p:Forefather', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:SecondCousin', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasParent', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:hasParent', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isSiblingOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7), fact(['p:isParentOf', X3, X4],add,M8,U8), fact(['p:Person', X4],add,M9,U9), fact(['p:isParentOf', X4, X5],add,M10,U10), fact(['p:Person', X5],add,M11,U11) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9,U10,U11]) | check_neg_mark([('p:Person',M1),('p:hasParent',M2),('p:Person',M3),('p:hasParent',M4),('p:Person',M5),('p:isSiblingOf',M6),('p:Person',M7),('p:isParentOf',M8),('p:Person',M9),('p:isParentOf',M10),('p:Person',M11)],M), fact(['p:SecondCousin', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSecondCousinOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGrandmotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandmother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGrandmotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Ancestor', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isAncestorOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:isAncestorOf',M2),('p:Person',M3)],M), fact(['p:Ancestor', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', X, Y],add,M1,U1), fact(['p:isForemotherOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isForemotherOf',M1),('p:isForemotherOf',M2)],M), fact(['p:isForemotherOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeFather', X, Y],add,M1,U1), fact(['p:hasForeFather', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasForeFather',M1),('p:hasForeFather',M2)],M), fact(['p:hasForeFather', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSpouseOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:knownAs', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatUncleOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X0, X1],add,M1,U1), fact(['p:hasFemalePartner', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isMalePartnerIn',M1),('p:hasFemalePartner',M2)],M), fact(['p:hasWife', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', X0, X1],add,M1,U1), fact(['p:hasMalePartner', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isFemalePartnerIn',M1),('p:hasMalePartner',M2)],M), fact(['p:hasHusband', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isParentOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:ParentInLaw', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSpouseOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Person',M1),('p:isParentOf',M2),('p:Person',M3),('p:isSpouseOf',M4),('p:Person',M5)],M), fact(['p:ParentInLaw', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:formerlyKnownAs', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Cousin', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasAncestor', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSiblingOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([('p:Person',M1),('p:hasAncestor',M2),('p:Person',M3),('p:isSiblingOf',M4),('p:Person',M5),('p:isParentOf',M6),('p:Person',M7)],M), fact(['p:Cousin', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGrandparent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([('p:Person',M1),('p:isParentOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5),('p:isParentOf',M6),('p:Person',M7)],M), fact(['p:GreatGrandparent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasUncle', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isUncleOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasHusband', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasWife', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:formerlyKnownAs', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:knownAs', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFirstCousinOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandfather', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', X, Y],add,M1,U1), fact(['p:hasForeMother', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasForeMother',M1),('p:hasForeMother',M2)],M), fact(['p:hasForeMother', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isAuntOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAunt', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isAuntOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasForeFather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:DomainEntity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:FemaleDescendent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:hasAncestor', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Woman',M1),('p:hasAncestor',M2),('p:Person',M3)],M), fact(['p:FemaleDescendent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isPartnerIn', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncleInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isUncleInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasUncleInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:FemaleAncestor', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isAncestorOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Woman',M1),('p:isAncestorOf',M2),('p:Person',M3)],M), fact(['p:FemaleAncestor', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isNieceOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Marriage', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGender', X, Y1],add,M1,U1), fact(['p:hasGender', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasGender',M1),('p:hasGender',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, Y],add,M1,U1), fact(['p:hasAncestor', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasAncestor',M1),('p:hasAncestor',M2)],M), fact(['p:hasAncestor', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Foremother', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Woman', X],add,M1,U1), fact(['p:isForemotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Woman',M1),('p:isForemotherOf',M2),('p:Person',M3)],M), fact(['p:Foremother', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOnceRemovedOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFirstCousinOnceRemovedOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:directSiblingOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isAncestorOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isAncestorOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasUncle', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasAncestor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X0, X1],add,M1,U1), fact(['p:grandParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:brotherOf',M1),('p:grandParentOf',M2)],M), fact(['p:isGreatUncleOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:hasGrandfather', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasParent',M1),('p:hasGrandfather',M2)],M), fact(['p:hasGreatGrandfather', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Male', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Sex', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasMother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Female', X],add,M1,U1), fact(['p:Male', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:Female',M1),('p:Male',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasMotherInLaw', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:Sex', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:Person',M1),('p:Sex',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isRelationOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrotherInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSisterInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSisterInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasBrotherInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isSpouseOf',M1),('p:isSiblingOf',M2)],M), fact(['p:isSiblingInLawOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasGender', X, X1],add,M2,U2), fact(['p:Male', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:hasGender',M2),('p:Male',M3)],M), fact(['p:Man', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandParentOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandParentOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatAunt', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Father', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isFatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Man',M1),('p:isFatherOf',M2),('p:Person',M3)],M), fact(['p:Father', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isNephewOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAunt', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasAncestor', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:marriageYear', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Marriage', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:brotherOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', X0, X1],add,M1,U1), fact(['p:isParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isFirstCousinOf',M1),('p:isParentOf',M2)],M), fact(['p:isFirstCousinOnceRemovedOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:FatherInLaw', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isFatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isSpouseOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Man',M1),('p:isFatherOf',M2),('p:Person',M3),('p:isSpouseOf',M4),('p:Person',M5)],M), fact(['p:FatherInLaw', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandParent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isGreatGrandfatherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandfather', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isGreatGrandfatherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isUncleOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatUncle', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, Y],add,M1,U1), fact(['p:isBloodRelationOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isBloodRelationOf',M1),('p:isBloodRelationOf',M2)],M), fact(['p:isBloodRelationOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGrandfather', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isFatherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7) ==> member(U,[U1,U2,U3,U4,U5,U6,U7]) | check_neg_mark([('p:Person',M1),('p:isFatherOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5),('p:isParentOf',M6),('p:Person',M7)],M), fact(['p:GreatGrandfather', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isFirstCousinOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isMalePartnerIn', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isPartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasBrotherInLaw', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBrotherInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasBrotherInLaw', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Grandmother', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isMotherOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Person',M1),('p:isMotherOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5)],M), fact(['p:Grandmother', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isSpouseOf', X0, X1],add,M1,U1), fact(['p:hasMother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isSpouseOf',M1),('p:hasMother',M2)],M), fact(['p:hasMotherInLaw', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:Husband', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:isMalePartnerIn', X, X1],add,M2,U2), fact(['p:Marriage', X1],add,M3,U3), fact(['p:hasFemalePartner', X1, X2],add,M4,U4), fact(['p:Woman', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Man',M1),('p:isMalePartnerIn',M2),('p:Marriage',M3),('p:hasFemalePartner',M4),('p:Woman',M5)],M), fact(['p:Husband', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandmother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isThirdCousinOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGender', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFemalePartner', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isFemalePartnerIn', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isFemalePartnerIn', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasFemalePartner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:InLaw', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isInLawOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:isInLawOf',M2),('p:Person',M3)],M), fact(['p:InLaw', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Descendent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:hasAncestor', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Person',M1),('p:hasAncestor',M2),('p:Person',M3)],M), fact(['p:Descendent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Marriage', X],add,M1,U1), fact(['p:Person', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:Marriage',M1),('p:Person',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isSecondCousinOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isBloodRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isRelationOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:PersonWithManySibling', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasFather', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:grandParentOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGrandParent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:grandParentOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:MaleDescendent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Man', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Man', X],add,M1,U1), fact(['p:hasAncestor', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('p:Man',M1),('p:hasAncestor',M2),('p:Person',M3)],M), fact(['p:MaleDescendent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isSonOf', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isSonOf',M1),('p:isSiblingOf',M2)],M), fact(['p:isNephewOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isInLawOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasParent', X0, X1],add,M1,U1), fact(['p:hasGrandmother', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:hasParent',M1),('p:hasGrandmother',M2)],M), fact(['p:hasGreatGrandmother', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isForemotherOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasForeMother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasForeMother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['p:isForemotherOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandmother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Woman', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isBrotherInLawOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:isSiblingInLawOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:ParentOfSmallFamily', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:ParentOfLargeFamily', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Aunt', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:sisterOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5) ==> member(U,[U1,U2,U3,U4,U5]) | check_neg_mark([('p:Person',M1),('p:sisterOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5)],M), fact(['p:Aunt', X],add,M,U), applied_rules(1,ins).
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
phase(5), fact(['p:isDaughterOf', X0, X1],add,M1,U1), fact(['p:isSiblingOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isDaughterOf',M1),('p:isSiblingOf',M2)],M), fact(['p:isNieceOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:sisterOf', X0, X1],add,M1,U1), fact(['p:grandParentOf', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:sisterOf',M1),('p:grandParentOf',M2)],M), fact(['p:isGreatAuntOf', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isBloodRelationOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:hasChild', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:GreatGreatGrandparent', X],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:Person', X],add,M1,U1), fact(['p:isParentOf', X, X1],add,M2,U2), fact(['p:Person', X1],add,M3,U3), fact(['p:isParentOf', X1, X2],add,M4,U4), fact(['p:Person', X2],add,M5,U5), fact(['p:isParentOf', X2, X3],add,M6,U6), fact(['p:Person', X3],add,M7,U7), fact(['p:isParentOf', X3, X4],add,M8,U8), fact(['p:Person', X4],add,M9,U9) ==> member(U,[U1,U2,U3,U4,U5,U6,U7,U8,U9]) | check_neg_mark([('p:Person',M1),('p:isParentOf',M2),('p:Person',M3),('p:isParentOf',M4),('p:Person',M5),('p:isParentOf',M6),('p:Person',M7),('p:isParentOf',M8),('p:Person',M9)],M), fact(['p:GreatGreatGrandparent', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:hasGreatGrandfather', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['p:hasGreatGrandParent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['p:isSiblingOf', X, Y],add,M1,U1), fact(['p:isSiblingOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('p:isSiblingOf',M1),('p:isSiblingOf',M2)],M), fact(['p:isSiblingOf', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['p:isParentInLawOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['p:Person', X],add,M1,U), applied_rules(1,ins).

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
