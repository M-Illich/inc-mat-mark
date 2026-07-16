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
phase(1), fact(['a1:colleagues', X, Y],O1,_,_), fact(['a1:colleagues', Y, Z],O2,_,_) \ fact(['a1:colleagues', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:colleagues', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', _, X1],O1,_,_) \ fact(['a1:University', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:title', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', Y, X],O1,_,_) \ fact(['a1:degreeFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', Y, X],O1,_,_) \ fact(['a1:hasAlumnus', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:hasAlumnus', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Faculty', X],O1,_,_) \ fact(['a1:Employee', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Employee', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Professor', X],O1,_,_) \ fact(['a1:Faculty', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:listedCourse', _, X1],O1,_,_) \ fact(['a1:Course', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Course', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:AssociateProfessor', X],O1,_,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:member', _, X1],O1,_,_) \ fact(['a1:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:AssistantProfessor', X],O1,_,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:orgPublication', X, _],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Chair', X],O1,_,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:TechnicalReport', X],O1,_,_) \ fact(['a1:Article', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Article', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:colleagues', Y, X],O1,_,_) \ fact(['a1:colleagues', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:colleagues', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:headOf', X, Y],O1,_,_) \ fact(['a1:worksFor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:worksFor', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:age', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', _, X1],O1,_,_) \ fact(['a1:University', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Specification', X],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:SystemsStaff', X],O1,_,_) \ fact(['a1:AdministrativeStaff', X],add,_,U) <=> member(del,[O1]) | fact(['a1:AdministrativeStaff', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', _, X1],O1,_,_) \ fact(['a1:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:softwareDocumentation', _, X1],O1,_,_) \ fact(['a1:Publication', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:PostDoc', X],O1,_,_) \ fact(['a1:Faculty', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X0, X1],O1,_,_), fact(['a1:connectedCourses', X1, X2],O2,_,_), fact(['a1:teacherOf', X3, X2],O3,_,_) \ fact(['a1:colleagues', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:colleagues', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:softwareVersion', X, _],O1,_,_) \ fact(['a1:Software', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Software', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:ConferencePaper', X],O1,_,_) \ fact(['a1:Article', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Article', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_,_), fact(['a1:teachingAssistantOf', X, X1],O2,_,_), fact(['a1:Course', X1],O3,_,_) \ fact(['a1:TeachingAssistant', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:TeachingAssistant', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:affiliateOf', _, X1],O1,_,_) \ fact(['a1:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_,_), fact(['a1:headOf', X, X1],O2,_,_), fact(['a1:Department', X1],O3,_,_) \ fact(['a1:Chair', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Chair', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:connectedCourses', X, Y],O1,_,_), fact(['a1:connectedCourses', Y, Z],O2,_,_) \ fact(['a1:connectedCourses', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:connectedCourses', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_,_), fact(['a1:headOf', X, X1],O2,_,_), fact(['a1:Program', X1],O3,_,_) \ fact(['a1:Director', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Director', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:member', Y, X],O1,_,_) \ fact(['a1:memberOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:memberOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:memberOf', Y, X],O1,_,_) \ fact(['a1:member', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:member', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:tenured', X, _],O1,_,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:takesCourse', X1, X0],O1,_,_), fact(['a1:takesCourse', X1, X2],O2,_,_) \ fact(['a1:connectedCourses', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:connectedCourses', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', _, X1],O1,_,_) \ fact(['a1:Course', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Course', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', X, _],O1,_,_) \ fact(['a1:University', X],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', X1, X0],O1,_,_), fact(['a1:takesCourse', X1, X2],O2,_,_) \ fact(['a1:advisor_takesCourse', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:advisor_takesCourse', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Research', X],O1,_,_) \ fact(['a1:Work', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Work', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:telephone', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Institute', X],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', _, X1],O1,_,_) \ fact(['a1:Organization', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:worksFor', X, Y],O1,_,_) \ fact(['a1:memberOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:memberOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Employee', X],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:softwareDocumentation', X, _],O1,_,_) \ fact(['a1:Software', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Software', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X0, X1],O1,_,_), fact(['a1:takesCourse', X2, X1],O2,_,_), fact(['a1:advisor', X2, X3],O3,_,_) \ fact(['a1:colleagues', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:colleagues', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:member', X, _],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Department', X],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Article', X],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Lecturer', X],O1,_,_) \ fact(['a1:Faculty', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:publicationAuthor', _, X1],O1,_,_) \ fact(['a1:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:researchProject', _, X1],O1,_,_) \ fact(['a1:Research', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Research', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Software', X],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:advisor_takesCourse', X0, X1],O1,_,_), fact(['a1:advisor_takesCourse', X2, X1],O2,_,_) \ fact(['a1:colleagues', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:colleagues', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Program', X],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:AdministrativeStaff', X],O1,_,_) \ fact(['a1:Employee', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Employee', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', _, X1],O1,_,_) \ fact(['a1:Professor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Course', X],O1,_,_) \ fact(['a1:Work', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Work', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Book', X],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:FullProfessor', X],O1,_,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:publicationResearch', X, _],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', X, Y],O1,_,_) \ fact(['a1:degreeFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:ClericalStaff', X],O1,_,_) \ fact(['a1:AdministrativeStaff', X],add,_,U) <=> member(del,[O1]) | fact(['a1:AdministrativeStaff', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:affiliatedOrganizationOf', X, _],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:teachingAssistantOf', X, _],O1,_,_) \ fact(['a1:TeachingAssistant', X],add,_,U) <=> member(del,[O1]) | fact(['a1:TeachingAssistant', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:VisitingProfessor', X],O1,_,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:University', X],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:JournalArticle', X],O1,_,_) \ fact(['a1:Article', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Article', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:publicationResearch', _, X1],O1,_,_) \ fact(['a1:Research', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Research', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Director', X],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:publicationDate', X, _],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:affiliatedOrganizationOf', _, X1],O1,_,_) \ fact(['a1:Organization', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', _, X1],O1,_,_) \ fact(['a1:University', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', _, X1],O1,_,_) \ fact(['a1:University', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:teachingAssistantOf', _, X1],O1,_,_) \ fact(['a1:Course', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Course', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', X, Y],O1,_,_) \ fact(['a1:degreeFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:listedCourse', X, _],O1,_,_) \ fact(['a1:Schedule', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Schedule', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:GraduateStudent', X],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:ResearchAssistant', X],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:UndergraduateStudent', X],O1,_,_) \ fact(['a1:Student', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Student', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', X, Y],O1,_,_) \ fact(['a1:degreeFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:publicationAuthor', X, _],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:College', X],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X, _],O1,_,_) \ fact(['a1:Faculty', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:ResearchGroup', X],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:UnofficialPublication', X],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:researchProject', X, _],O1,_,_) \ fact(['a1:ResearchGroup', X],add,_,U) <=> member(del,[O1]) | fact(['a1:ResearchGroup', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_,_), fact(['a1:worksFor', X, X1],O2,_,_), fact(['a1:Organization', X1],O3,_,_) \ fact(['a1:Employee', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Employee', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Chair', X],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:affiliateOf', X, _],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:GraduateCourse', X],O1,_,_) \ fact(['a1:Course', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Course', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_,_), fact(['a1:takesCourse', X, X1],O2,_,_), fact(['a1:Course', X1],O3,_,_) \ fact(['a1:Student', X],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Student', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Dean', X],O1,_,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:orgPublication', _, X1],O1,_,_) \ fact(['a1:Publication', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Manual', X],O1,_,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:headOf', X, X1],O1,_,_), fact(['a1:College', X1],O2,_,_) \ fact(['a1:Dean', X],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:Dean', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:TeachingAssistant', X],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', X, _],O1,_,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:connectedCourses', Y, X],O1,_,_) \ fact(['a1:connectedCourses', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:connectedCourses', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:Student', X],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:emailAddress', X, _],O1,_,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', X, Y],O1,_,_), fact(['a1:subOrganizationOf', Y, Z],O2,_,_) \ fact(['a1:subOrganizationOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:subOrganizationOf', X, Z],chk,_,U), applied_rules(1,del).

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
fact(['a1:colleagues', X, Y],prv,_,_), fact(['a1:colleagues', Y, Z],prv,_,_) \ fact(['a1:colleagues', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:colleagues', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:mastersDegreeFrom', _, X1],prv,M1,_) \ fact(['a1:University', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:title', X, _],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:hasAlumnus', Y, X],prv,_,_) \ fact(['a1:degreeFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:degreeFrom', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:degreeFrom', Y, X],prv,_,_) \ fact(['a1:hasAlumnus', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:hasAlumnus', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:Faculty', X],prv,_,_) \ fact(['a1:Employee', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Employee', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:Professor', X],prv,_,_) \ fact(['a1:Faculty', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Faculty', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:listedCourse', _, X1],prv,M1,_) \ fact(['a1:Course', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Course', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:AssociateProfessor', X],prv,M1,_) \ fact(['a1:Professor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:member', _, X1],prv,_,_) \ fact(['a1:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:AssistantProfessor', X],prv,M1,_) \ fact(['a1:Professor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:orgPublication', X, _],prv,M1,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Chair', X],prv,_,_) \ fact(['a1:Professor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:TechnicalReport', X],prv,M1,_) \ fact(['a1:Article', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Article', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:colleagues', Y, X],prv,_,_) \ fact(['a1:colleagues', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:colleagues', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:headOf', X, Y],prv,M1,_) \ fact(['a1:worksFor', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:worksFor', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:age', X, _],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:degreeFrom', X, _],prv,_,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:degreeFrom', _, X1],prv,_,_) \ fact(['a1:University', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:Specification', X],prv,M1,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:SystemsStaff', X],prv,M1,_) \ fact(['a1:AdministrativeStaff', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:AdministrativeStaff', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:hasAlumnus', _, X1],prv,_,_) \ fact(['a1:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:softwareDocumentation', _, X1],prv,M1,_) \ fact(['a1:Publication', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:PostDoc', X],prv,M1,_) \ fact(['a1:Faculty', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Faculty', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:teacherOf', X0, X1],prv,M1,_), fact(['a1:connectedCourses', X1, X2],prv,M2,_), fact(['a1:teacherOf', X3, X2],prv,M3,_) \ fact(['a1:colleagues', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:teacherOf',M1),('a1:connectedCourses',M2),('a1:teacherOf',M3)],M), fact(['a1:colleagues', X0, X3],prv,M,U), applied_rules(1,fwd).
fact(['a1:softwareVersion', X, _],prv,M1,_) \ fact(['a1:Software', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Software', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:ConferencePaper', X],prv,M1,_) \ fact(['a1:Article', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Article', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,M1,_), fact(['a1:teachingAssistantOf', X, X1],prv,M2,_), fact(['a1:Course', X1],prv,M3,_) \ fact(['a1:TeachingAssistant', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:Person',M1),('a1:teachingAssistantOf',M2),('a1:Course',M3)],M), fact(['a1:TeachingAssistant', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:affiliateOf', _, X1],prv,M1,_) \ fact(['a1:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,M1,_), fact(['a1:headOf', X, X1],prv,M2,_), fact(['a1:Department', X1],prv,M3,_) \ fact(['a1:Chair', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:Person',M1),('a1:headOf',M2),('a1:Department',M3)],M), fact(['a1:Chair', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:connectedCourses', X, Y],prv,_,_), fact(['a1:connectedCourses', Y, Z],prv,_,_) \ fact(['a1:connectedCourses', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:connectedCourses', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,M1,_), fact(['a1:headOf', X, X1],prv,M2,_), fact(['a1:Program', X1],prv,M3,_) \ fact(['a1:Director', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:Person',M1),('a1:headOf',M2),('a1:Program',M3)],M), fact(['a1:Director', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:member', Y, X],prv,_,_) \ fact(['a1:memberOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:memberOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:memberOf', Y, X],prv,_,_) \ fact(['a1:member', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:member', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:tenured', X, _],prv,M1,_) \ fact(['a1:Professor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:takesCourse', X1, X0],prv,M1,_), fact(['a1:takesCourse', X1, X2],prv,M2,_) \ fact(['a1:connectedCourses', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:takesCourse',M1),('a1:takesCourse',M2)],M), fact(['a1:connectedCourses', X0, X2],prv,M,U), applied_rules(1,fwd).
fact(['a1:teacherOf', _, X1],prv,M1,_) \ fact(['a1:Course', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Course', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:hasAlumnus', X, _],prv,_,_) \ fact(['a1:University', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:advisor', X1, X0],prv,M1,_), fact(['a1:takesCourse', X1, X2],prv,M2,_) \ fact(['a1:advisor_takesCourse', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:advisor',M1),('a1:takesCourse',M2)],M), fact(['a1:advisor_takesCourse', X0, X2],prv,M,U), applied_rules(1,fwd).
fact(['a1:Research', X],prv,_,_) \ fact(['a1:Work', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Work', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:telephone', X, _],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Institute', X],prv,M1,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:subOrganizationOf', _, X1],prv,_,_) \ fact(['a1:Organization', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:worksFor', X, Y],prv,_,_) \ fact(['a1:memberOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:memberOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:Employee', X],prv,_,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:softwareDocumentation', X, _],prv,M1,_) \ fact(['a1:Software', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Software', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:advisor', X, _],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:teacherOf', X0, X1],prv,M1,_), fact(['a1:takesCourse', X2, X1],prv,M2,_), fact(['a1:advisor', X2, X3],prv,M3,_) \ fact(['a1:colleagues', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:teacherOf',M1),('a1:takesCourse',M2),('a1:advisor',M3)],M), fact(['a1:colleagues', X0, X3],prv,M,U), applied_rules(1,fwd).
fact(['a1:member', X, _],prv,_,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:Department', X],prv,M1,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Article', X],prv,_,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:Lecturer', X],prv,M1,_) \ fact(['a1:Faculty', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Faculty', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:publicationAuthor', _, X1],prv,M1,_) \ fact(['a1:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:researchProject', _, X1],prv,M1,_) \ fact(['a1:Research', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Research', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Software', X],prv,_,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:advisor_takesCourse', X0, X1],prv,_,_), fact(['a1:advisor_takesCourse', X2, X1],prv,_,_) \ fact(['a1:colleagues', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:colleagues', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:Program', X],prv,M1,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:AdministrativeStaff', X],prv,_,_) \ fact(['a1:Employee', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Employee', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:advisor', _, X1],prv,M1,_) \ fact(['a1:Professor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Course', X],prv,_,_) \ fact(['a1:Work', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Work', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:Book', X],prv,M1,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:FullProfessor', X],prv,M1,_) \ fact(['a1:Professor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:publicationResearch', X, _],prv,M1,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:doctoralDegreeFrom', X, Y],prv,M1,_) \ fact(['a1:degreeFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:degreeFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:ClericalStaff', X],prv,M1,_) \ fact(['a1:AdministrativeStaff', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:AdministrativeStaff', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:affiliatedOrganizationOf', X, _],prv,M1,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:teachingAssistantOf', X, _],prv,M1,_) \ fact(['a1:TeachingAssistant', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:TeachingAssistant', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:VisitingProfessor', X],prv,M1,_) \ fact(['a1:Professor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:undergraduateDegreeFrom', X, _],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:University', X],prv,_,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:JournalArticle', X],prv,M1,_) \ fact(['a1:Article', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Article', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:publicationResearch', _, X1],prv,M1,_) \ fact(['a1:Research', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Research', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Director', X],prv,_,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:doctoralDegreeFrom', X, _],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:publicationDate', X, _],prv,M1,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:affiliatedOrganizationOf', _, X1],prv,M1,_) \ fact(['a1:Organization', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:doctoralDegreeFrom', _, X1],prv,M1,_) \ fact(['a1:University', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:undergraduateDegreeFrom', _, X1],prv,M1,_) \ fact(['a1:University', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:teachingAssistantOf', _, X1],prv,M1,_) \ fact(['a1:Course', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Course', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:mastersDegreeFrom', X, Y],prv,M1,_) \ fact(['a1:degreeFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:degreeFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:listedCourse', X, _],prv,M1,_) \ fact(['a1:Schedule', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Schedule', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:GraduateStudent', X],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:ResearchAssistant', X],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:UndergraduateStudent', X],prv,M1,_) \ fact(['a1:Student', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Student', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:undergraduateDegreeFrom', X, Y],prv,M1,_) \ fact(['a1:degreeFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:degreeFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:publicationAuthor', X, _],prv,M1,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:mastersDegreeFrom', X, _],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:College', X],prv,M1,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:teacherOf', X, _],prv,M1,_) \ fact(['a1:Faculty', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Faculty', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:ResearchGroup', X],prv,_,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:UnofficialPublication', X],prv,M1,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:researchProject', X, _],prv,M1,_) \ fact(['a1:ResearchGroup', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:ResearchGroup', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,_,_), fact(['a1:worksFor', X, X1],prv,_,_), fact(['a1:Organization', X1],prv,_,_) \ fact(['a1:Employee', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Employee', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:Chair', X],prv,_,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:affiliateOf', X, _],prv,M1,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:GraduateCourse', X],prv,M1,_) \ fact(['a1:Course', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Course', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,M1,_), fact(['a1:takesCourse', X, X1],prv,M2,_), fact(['a1:Course', X1],prv,M3,_) \ fact(['a1:Student', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:Person',M1),('a1:takesCourse',M2),('a1:Course',M3)],M), fact(['a1:Student', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:Dean', X],prv,_,_) \ fact(['a1:Professor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:orgPublication', _, X1],prv,M1,_) \ fact(['a1:Publication', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:Manual', X],prv,M1,_) \ fact(['a1:Publication', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:headOf', X, X1],prv,M1,_), fact(['a1:College', X1],prv,M2,_) \ fact(['a1:Dean', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a1:headOf',M1),('a1:College',M2)],M), fact(['a1:Dean', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:TeachingAssistant', X],prv,_,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:subOrganizationOf', X, _],prv,_,_) \ fact(['a1:Organization', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:connectedCourses', Y, X],prv,_,_) \ fact(['a1:connectedCourses', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:connectedCourses', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:Student', X],prv,_,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:emailAddress', X, _],prv,M1,_) \ fact(['a1:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:subOrganizationOf', X, Y],prv,_,_), fact(['a1:subOrganizationOf', Y, Z],prv,_,_) \ fact(['a1:subOrganizationOf', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:subOrganizationOf', X, Z],prv,_,U), applied_rules(1,fwd).


% - backward -
fact(['a1:colleagues', X, Z],chk1,_,_), fact(['a1:colleagues', X, Y],O1,M1,U1), fact(['a1:colleagues', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:colleagues', X, Y],chk1,M1,U1), fact(['a1:colleagues', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:University', X1],chk1,_,_), fact(['a1:mastersDegreeFrom', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:mastersDegreeFrom', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:title', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:title', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:degreeFrom', X, Y],chk1,_,_), fact(['a1:hasAlumnus', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:hasAlumnus', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:hasAlumnus', X, Y],chk1,_,_), fact(['a1:degreeFrom', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:degreeFrom', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Employee', X],chk1,_,_), fact(['a1:Faculty', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Faculty', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Faculty', X],chk1,_,_), fact(['a1:Professor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Professor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Course', X1],chk1,_,_), fact(['a1:listedCourse', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:listedCourse', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_,_), fact(['a1:AssociateProfessor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:AssociateProfessor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X1],chk1,_,_), fact(['a1:member', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:member', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_,_), fact(['a1:AssistantProfessor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:AssistantProfessor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:orgPublication', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:orgPublication', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_,_), fact(['a1:Chair', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Chair', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Article', X],chk1,_,_), fact(['a1:TechnicalReport', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:TechnicalReport', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:colleagues', X, Y],chk1,_,_), fact(['a1:colleagues', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:colleagues', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:worksFor', X, Y],chk1,_,_), fact(['a1:headOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:headOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:age', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:age', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:degreeFrom', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:degreeFrom', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:University', X1],chk1,_,_), fact(['a1:degreeFrom', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:degreeFrom', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:Specification', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Specification', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:AdministrativeStaff', X],chk1,_,_), fact(['a1:SystemsStaff', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:SystemsStaff', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X1],chk1,_,_), fact(['a1:hasAlumnus', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:hasAlumnus', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X1],chk1,_,_), fact(['a1:softwareDocumentation', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:softwareDocumentation', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Faculty', X],chk1,_,_), fact(['a1:PostDoc', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:PostDoc', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:colleagues', X0, X3],chk1,_,_), fact(['a1:teacherOf', X0, X1],O1,M1,U1), fact(['a1:connectedCourses', X1, X2],O2,M2,U2), fact(['a1:teacherOf', X3, X2],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:teacherOf', X0, X1],chk1,M1,U1), fact(['a1:connectedCourses', X1, X2],chk1,M2,U2), fact(['a1:teacherOf', X3, X2],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:Software', X],chk1,_,_), fact(['a1:softwareVersion', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:softwareVersion', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Article', X],chk1,_,_), fact(['a1:ConferencePaper', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:ConferencePaper', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:TeachingAssistant', X],chk1,_,_), fact(['a1:Person', X],O1,M1,U1), fact(['a1:teachingAssistantOf', X, X1],O2,M2,U2), fact(['a1:Course', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,M1,U1), fact(['a1:teachingAssistantOf', X, X1],chk1,M2,U2), fact(['a1:Course', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:Person', X1],chk1,_,_), fact(['a1:affiliateOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:affiliateOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Chair', X],chk1,_,_), fact(['a1:Person', X],O1,M1,U1), fact(['a1:headOf', X, X1],O2,M2,U2), fact(['a1:Department', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,M1,U1), fact(['a1:headOf', X, X1],chk1,M2,U2), fact(['a1:Department', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:connectedCourses', X, Z],chk1,_,_), fact(['a1:connectedCourses', X, Y],O1,M1,U1), fact(['a1:connectedCourses', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:connectedCourses', X, Y],chk1,M1,U1), fact(['a1:connectedCourses', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:Director', X],chk1,_,_), fact(['a1:Person', X],O1,M1,U1), fact(['a1:headOf', X, X1],O2,M2,U2), fact(['a1:Program', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,M1,U1), fact(['a1:headOf', X, X1],chk1,M2,U2), fact(['a1:Program', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:memberOf', X, Y],chk1,_,_), fact(['a1:member', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:member', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:member', X, Y],chk1,_,_), fact(['a1:memberOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:memberOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_,_), fact(['a1:tenured', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:tenured', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:connectedCourses', X0, X2],chk1,_,_), fact(['a1:takesCourse', X1, X0],O1,M1,U1), fact(['a1:takesCourse', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:takesCourse', X1, X0],chk1,M1,U1), fact(['a1:takesCourse', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:Course', X1],chk1,_,_), fact(['a1:teacherOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:teacherOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:University', X],chk1,_,_), fact(['a1:hasAlumnus', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:hasAlumnus', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:advisor_takesCourse', X0, X2],chk1,_,_), fact(['a1:advisor', X1, X0],O1,M1,U1), fact(['a1:takesCourse', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:advisor', X1, X0],chk1,M1,U1), fact(['a1:takesCourse', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:Work', X],chk1,_,_), fact(['a1:Research', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Research', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:telephone', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:telephone', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:Institute', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Institute', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X1],chk1,_,_), fact(['a1:subOrganizationOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:subOrganizationOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:memberOf', X, Y],chk1,_,_), fact(['a1:worksFor', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:worksFor', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:Employee', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Employee', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Software', X],chk1,_,_), fact(['a1:softwareDocumentation', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:softwareDocumentation', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:advisor', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:advisor', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:colleagues', X0, X3],chk1,_,_), fact(['a1:teacherOf', X0, X1],O1,M1,U1), fact(['a1:takesCourse', X2, X1],O2,M2,U2), fact(['a1:advisor', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:teacherOf', X0, X1],chk1,M1,U1), fact(['a1:takesCourse', X2, X1],chk1,M2,U2), fact(['a1:advisor', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:member', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:member', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:Department', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Department', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:Article', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Article', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Faculty', X],chk1,_,_), fact(['a1:Lecturer', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Lecturer', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X1],chk1,_,_), fact(['a1:publicationAuthor', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationAuthor', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Research', X1],chk1,_,_), fact(['a1:researchProject', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:researchProject', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:Software', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Software', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:colleagues', X0, X2],chk1,_,_), fact(['a1:advisor_takesCourse', X0, X1],O1,M1,U1), fact(['a1:advisor_takesCourse', X2, X1],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:advisor_takesCourse', X0, X1],chk1,M1,U1), fact(['a1:advisor_takesCourse', X2, X1],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:Program', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Program', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Employee', X],chk1,_,_), fact(['a1:AdministrativeStaff', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:AdministrativeStaff', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X1],chk1,_,_), fact(['a1:advisor', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:advisor', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Work', X],chk1,_,_), fact(['a1:Course', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Course', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:Book', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Book', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_,_), fact(['a1:FullProfessor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:FullProfessor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:publicationResearch', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationResearch', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:degreeFrom', X, Y],chk1,_,_), fact(['a1:doctoralDegreeFrom', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:doctoralDegreeFrom', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:AdministrativeStaff', X],chk1,_,_), fact(['a1:ClericalStaff', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:ClericalStaff', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:affiliatedOrganizationOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:affiliatedOrganizationOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:TeachingAssistant', X],chk1,_,_), fact(['a1:teachingAssistantOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:teachingAssistantOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_,_), fact(['a1:VisitingProfessor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:VisitingProfessor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:undergraduateDegreeFrom', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:undergraduateDegreeFrom', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:University', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:University', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Article', X],chk1,_,_), fact(['a1:JournalArticle', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:JournalArticle', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Research', X1],chk1,_,_), fact(['a1:publicationResearch', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationResearch', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:Director', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Director', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:doctoralDegreeFrom', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:doctoralDegreeFrom', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:publicationDate', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationDate', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X1],chk1,_,_), fact(['a1:affiliatedOrganizationOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:affiliatedOrganizationOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:University', X1],chk1,_,_), fact(['a1:doctoralDegreeFrom', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:doctoralDegreeFrom', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:University', X1],chk1,_,_), fact(['a1:undergraduateDegreeFrom', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:undergraduateDegreeFrom', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Course', X1],chk1,_,_), fact(['a1:teachingAssistantOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:teachingAssistantOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:degreeFrom', X, Y],chk1,_,_), fact(['a1:mastersDegreeFrom', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:mastersDegreeFrom', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Schedule', X],chk1,_,_), fact(['a1:listedCourse', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:listedCourse', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:GraduateStudent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:GraduateStudent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:ResearchAssistant', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:ResearchAssistant', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Student', X],chk1,_,_), fact(['a1:UndergraduateStudent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:UndergraduateStudent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:degreeFrom', X, Y],chk1,_,_), fact(['a1:undergraduateDegreeFrom', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:undergraduateDegreeFrom', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:publicationAuthor', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationAuthor', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:mastersDegreeFrom', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:mastersDegreeFrom', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:College', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:College', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Faculty', X],chk1,_,_), fact(['a1:teacherOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:teacherOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:ResearchGroup', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:ResearchGroup', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:UnofficialPublication', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:UnofficialPublication', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:ResearchGroup', X],chk1,_,_), fact(['a1:researchProject', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:researchProject', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Employee', X],chk1,_,_), fact(['a1:Person', X],O1,M1,U1), fact(['a1:worksFor', X, X1],O2,M2,U2), fact(['a1:Organization', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,M1,U1), fact(['a1:worksFor', X, X1],chk1,M2,U2), fact(['a1:Organization', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:Chair', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Chair', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:affiliateOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:affiliateOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Course', X],chk1,_,_), fact(['a1:GraduateCourse', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:GraduateCourse', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Student', X],chk1,_,_), fact(['a1:Person', X],O1,M1,U1), fact(['a1:takesCourse', X, X1],O2,M2,U2), fact(['a1:Course', X1],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,M1,U1), fact(['a1:takesCourse', X, X1],chk1,M2,U2), fact(['a1:Course', X1],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_,_), fact(['a1:Dean', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Dean', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X1],chk1,_,_), fact(['a1:orgPublication', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:orgPublication', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_,_), fact(['a1:Manual', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Manual', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Dean', X],chk1,_,_), fact(['a1:headOf', X, X1],O1,M1,U1), fact(['a1:College', X1],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:headOf', X, X1],chk1,M1,U1), fact(['a1:College', X1],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:TeachingAssistant', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:TeachingAssistant', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_,_), fact(['a1:subOrganizationOf', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:subOrganizationOf', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:connectedCourses', X, Y],chk1,_,_), fact(['a1:connectedCourses', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:connectedCourses', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:Student', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:Student', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_,_), fact(['a1:emailAddress', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:emailAddress', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:subOrganizationOf', X, Z],chk1,_,_), fact(['a1:subOrganizationOf', X, Y],O1,M1,U1), fact(['a1:subOrganizationOf', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:subOrganizationOf', X, Y],chk1,M1,U1), fact(['a1:subOrganizationOf', Y, Z],chk1,M2,U2), applied_rules(1,bwd).

	
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
phase(5), fact(['a1:colleagues', X, Y],add,M1,U1), fact(['a1:colleagues', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:colleagues',M1),('a1:colleagues',M2)],M), fact(['a1:colleagues', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:mastersDegreeFrom', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:University', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:title', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:hasAlumnus', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:degreeFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:degreeFrom', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:hasAlumnus', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Faculty', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Employee', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Professor', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:listedCourse', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Course', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:AssociateProfessor', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:member', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:AssistantProfessor', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:orgPublication', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Chair', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:TechnicalReport', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Article', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:colleagues', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:colleagues', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:headOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:worksFor', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:age', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:degreeFrom', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:degreeFrom', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:University', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Specification', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:SystemsStaff', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:AdministrativeStaff', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:hasAlumnus', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:softwareDocumentation', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:PostDoc', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', X0, X1],add,M1,U1), fact(['a1:connectedCourses', X1, X2],add,M2,U2), fact(['a1:teacherOf', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:teacherOf',M1),('a1:connectedCourses',M2),('a1:teacherOf',M3)],M), fact(['a1:colleagues', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:softwareVersion', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Software', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:ConferencePaper', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Article', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:teachingAssistantOf', X, X1],add,M2,U2), fact(['a1:Course', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:Person',M1),('a1:teachingAssistantOf',M2),('a1:Course',M3)],M), fact(['a1:TeachingAssistant', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliateOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:headOf', X, X1],add,M2,U2), fact(['a1:Department', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:Person',M1),('a1:headOf',M2),('a1:Department',M3)],M), fact(['a1:Chair', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:connectedCourses', X, Y],add,M1,U1), fact(['a1:connectedCourses', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:connectedCourses',M1),('a1:connectedCourses',M2)],M), fact(['a1:connectedCourses', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:headOf', X, X1],add,M2,U2), fact(['a1:Program', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:Person',M1),('a1:headOf',M2),('a1:Program',M3)],M), fact(['a1:Director', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:member', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:memberOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:memberOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:member', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:tenured', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:takesCourse', X1, X0],add,M1,U1), fact(['a1:takesCourse', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:takesCourse',M1),('a1:takesCourse',M2)],M), fact(['a1:connectedCourses', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Course', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:hasAlumnus', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:University', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor', X1, X0],add,M1,U1), fact(['a1:takesCourse', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:advisor',M1),('a1:takesCourse',M2)],M), fact(['a1:advisor_takesCourse', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Research', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Work', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:telephone', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Institute', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:worksFor', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:memberOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Employee', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:softwareDocumentation', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Software', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', X0, X1],add,M1,U1), fact(['a1:takesCourse', X2, X1],add,M2,U2), fact(['a1:advisor', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:teacherOf',M1),('a1:takesCourse',M2),('a1:advisor',M3)],M), fact(['a1:colleagues', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:member', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Department', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Article', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Lecturer', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationAuthor', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:researchProject', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Research', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Software', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor_takesCourse', X0, X1],add,M1,U1), fact(['a1:advisor_takesCourse', X2, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:advisor_takesCourse',M1),('a1:advisor_takesCourse',M2)],M), fact(['a1:colleagues', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Program', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:AdministrativeStaff', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Employee', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Course', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Work', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Book', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:FullProfessor', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationResearch', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:doctoralDegreeFrom', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:degreeFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:ClericalStaff', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:AdministrativeStaff', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliatedOrganizationOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:teachingAssistantOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:TeachingAssistant', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:VisitingProfessor', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:undergraduateDegreeFrom', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:University', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:JournalArticle', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Article', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationResearch', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Research', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Director', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:doctoralDegreeFrom', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationDate', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliatedOrganizationOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:doctoralDegreeFrom', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:University', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:undergraduateDegreeFrom', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:University', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:teachingAssistantOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Course', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:mastersDegreeFrom', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:degreeFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:listedCourse', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Schedule', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:GraduateStudent', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:ResearchAssistant', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:UndergraduateStudent', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Student', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:undergraduateDegreeFrom', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:degreeFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationAuthor', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:mastersDegreeFrom', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:College', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:ResearchGroup', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:UnofficialPublication', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:researchProject', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:ResearchGroup', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:worksFor', X, X1],add,M2,U2), fact(['a1:Organization', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:Person',M1),('a1:worksFor',M2),('a1:Organization',M3)],M), fact(['a1:Employee', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Chair', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliateOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:GraduateCourse', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Course', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:takesCourse', X, X1],add,M2,U2), fact(['a1:Course', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:Person',M1),('a1:takesCourse',M2),('a1:Course',M3)],M), fact(['a1:Student', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Dean', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:orgPublication', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Manual', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:headOf', X, X1],add,M1,U1), fact(['a1:College', X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:headOf',M1),('a1:College',M2)],M), fact(['a1:Dean', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:TeachingAssistant', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:connectedCourses', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:connectedCourses', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Student', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:emailAddress', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', X, Y],add,M1,U1), fact(['a1:subOrganizationOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:subOrganizationOf',M1),('a1:subOrganizationOf',M2)],M), fact(['a1:subOrganizationOf', X, Z],add,M,U), applied_rules(1,ins).

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
explicit('a1:mastersDegreeFrom').
explicit('a1:title').
explicit('a1:listedCourse').
explicit('a1:AssociateProfessor').
explicit('a1:AssistantProfessor').
explicit('a1:orgPublication').
explicit('a1:TechnicalReport').
explicit('a1:headOf').
explicit('a1:age').
explicit('a1:Specification').
explicit('a1:SystemsStaff').
explicit('a1:softwareDocumentation').
explicit('a1:PostDoc').
explicit('a1:teacherOf').
explicit('a1:softwareVersion').
explicit('a1:ConferencePaper').
explicit('a1:teachingAssistantOf').
explicit('a1:affiliateOf').
explicit('a1:Department').
explicit('a1:Program').
explicit('a1:tenured').
explicit('a1:takesCourse').
explicit('a1:advisor').
explicit('a1:telephone').
explicit('a1:Institute').
explicit('a1:Lecturer').
explicit('a1:publicationAuthor').
explicit('a1:researchProject').
explicit('a1:Book').
explicit('a1:FullProfessor').
explicit('a1:publicationResearch').
explicit('a1:doctoralDegreeFrom').
explicit('a1:ClericalStaff').
explicit('a1:affiliatedOrganizationOf').
explicit('a1:VisitingProfessor').
explicit('a1:undergraduateDegreeFrom').
explicit('a1:JournalArticle').
explicit('a1:publicationDate').
explicit('a1:GraduateStudent').
explicit('a1:ResearchAssistant').
explicit('a1:UndergraduateStudent').
explicit('a1:College').
explicit('a1:UnofficialPublication').
explicit('a1:GraduateCourse').
explicit('a1:Manual').
explicit('a1:emailAddress').
