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
phase(1), fact(['a1:colleagues', X, Y],O1,_), fact(['a1:colleagues', Y, Z],O2,_) \ fact(['a1:colleagues', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:colleagues', X, Z],chk,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', _, X1],O1,_) \ fact(['a1:University', X1],add,U) <=> member(del,[O1]) | fact(['a1:University', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:title', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', Y, X],O1,_) \ fact(['a1:degreeFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', Y, X],O1,_) \ fact(['a1:hasAlumnus', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:hasAlumnus', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Faculty', X],O1,_) \ fact(['a1:Employee', X],add,U) <=> member(del,[O1]) | fact(['a1:Employee', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Professor', X],O1,_) \ fact(['a1:Faculty', X],add,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:listedCourse', _, X1],O1,_) \ fact(['a1:Course', X1],add,U) <=> member(del,[O1]) | fact(['a1:Course', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:AssociateProfessor', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:member', _, X1],O1,_) \ fact(['a1:Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:Person', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:AssistantProfessor', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:orgPublication', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Chair', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:TechnicalReport', X],O1,_) \ fact(['a1:Article', X],add,U) <=> member(del,[O1]) | fact(['a1:Article', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:colleagues', Y, X],O1,_) \ fact(['a1:colleagues', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:colleagues', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:headOf', X, Y],O1,_) \ fact(['a1:worksFor', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:worksFor', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:age', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', _, X1],O1,_) \ fact(['a1:University', X1],add,U) <=> member(del,[O1]) | fact(['a1:University', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Specification', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:SystemsStaff', X],O1,_) \ fact(['a1:AdministrativeStaff', X],add,U) <=> member(del,[O1]) | fact(['a1:AdministrativeStaff', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', _, X1],O1,_) \ fact(['a1:Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:Person', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:softwareDocumentation', _, X1],O1,_) \ fact(['a1:Publication', X1],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:PostDoc', X],O1,_) \ fact(['a1:Faculty', X],add,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X0, X1],O1,_), fact(['a1:connectedCourses', X1, X2],O2,_), fact(['a1:teacherOf', X3, X2],O3,_) \ fact(['a1:colleagues', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:colleagues', X0, X3],chk,U), applied_rules(1,del).
phase(1), fact(['a1:softwareVersion', X, _],O1,_) \ fact(['a1:Software', X],add,U) <=> member(del,[O1]) | fact(['a1:Software', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:ConferencePaper', X],O1,_) \ fact(['a1:Article', X],add,U) <=> member(del,[O1]) | fact(['a1:Article', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:teachingAssistantOf', X, X1],O2,_), fact(['a1:Course', X1],O3,_) \ fact(['a1:TeachingAssistant', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:TeachingAssistant', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:affiliateOf', _, X1],O1,_) \ fact(['a1:Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:Person', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:headOf', X, X1],O2,_), fact(['a1:Department', X1],O3,_) \ fact(['a1:Chair', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Chair', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:connectedCourses', X, Y],O1,_), fact(['a1:connectedCourses', Y, Z],O2,_) \ fact(['a1:connectedCourses', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:connectedCourses', X, Z],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:headOf', X, X1],O2,_), fact(['a1:Program', X1],O3,_) \ fact(['a1:Director', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Director', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:member', Y, X],O1,_) \ fact(['a1:memberOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:memberOf', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:memberOf', Y, X],O1,_) \ fact(['a1:member', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:member', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:tenured', X, _],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:takesCourse', X1, X0],O1,_), fact(['a1:takesCourse', X1, X2],O2,_) \ fact(['a1:connectedCourses', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:connectedCourses', X0, X2],chk,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', _, X1],O1,_) \ fact(['a1:Course', X1],add,U) <=> member(del,[O1]) | fact(['a1:Course', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', X, _],O1,_) \ fact(['a1:University', X],add,U) <=> member(del,[O1]) | fact(['a1:University', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', X1, X0],O1,_), fact(['a1:takesCourse', X1, X2],O2,_) \ fact(['a1:advisor_takesCourse', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:advisor_takesCourse', X0, X2],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Research', X],O1,_) \ fact(['a1:Work', X],add,U) <=> member(del,[O1]) | fact(['a1:Work', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:telephone', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Institute', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', _, X1],O1,_) \ fact(['a1:Organization', X1],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:worksFor', X, Y],O1,_) \ fact(['a1:memberOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:memberOf', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Employee', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:softwareDocumentation', X, _],O1,_) \ fact(['a1:Software', X],add,U) <=> member(del,[O1]) | fact(['a1:Software', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X0, X1],O1,_), fact(['a1:takesCourse', X2, X1],O2,_), fact(['a1:advisor', X2, X3],O3,_) \ fact(['a1:colleagues', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:colleagues', X0, X3],chk,U), applied_rules(1,del).
phase(1), fact(['a1:member', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Department', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Article', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Lecturer', X],O1,_) \ fact(['a1:Faculty', X],add,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:publicationAuthor', _, X1],O1,_) \ fact(['a1:Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:Person', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:researchProject', _, X1],O1,_) \ fact(['a1:Research', X1],add,U) <=> member(del,[O1]) | fact(['a1:Research', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Software', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:advisor_takesCourse', X0, X1],O1,_), fact(['a1:advisor_takesCourse', X2, X1],O2,_) \ fact(['a1:colleagues', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:colleagues', X0, X2],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Program', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:AdministrativeStaff', X],O1,_) \ fact(['a1:Employee', X],add,U) <=> member(del,[O1]) | fact(['a1:Employee', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', _, X1],O1,_) \ fact(['a1:Professor', X1],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Course', X],O1,_) \ fact(['a1:Work', X],add,U) <=> member(del,[O1]) | fact(['a1:Work', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Book', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:FullProfessor', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:publicationResearch', X, _],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', X, Y],O1,_) \ fact(['a1:degreeFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:ClericalStaff', X],O1,_) \ fact(['a1:AdministrativeStaff', X],add,U) <=> member(del,[O1]) | fact(['a1:AdministrativeStaff', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:affiliatedOrganizationOf', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:teachingAssistantOf', X, _],O1,_) \ fact(['a1:TeachingAssistant', X],add,U) <=> member(del,[O1]) | fact(['a1:TeachingAssistant', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:VisitingProfessor', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:University', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:JournalArticle', X],O1,_) \ fact(['a1:Article', X],add,U) <=> member(del,[O1]) | fact(['a1:Article', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:publicationResearch', _, X1],O1,_) \ fact(['a1:Research', X1],add,U) <=> member(del,[O1]) | fact(['a1:Research', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Director', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:publicationDate', X, _],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:affiliatedOrganizationOf', _, X1],O1,_) \ fact(['a1:Organization', X1],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', _, X1],O1,_) \ fact(['a1:University', X1],add,U) <=> member(del,[O1]) | fact(['a1:University', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', _, X1],O1,_) \ fact(['a1:University', X1],add,U) <=> member(del,[O1]) | fact(['a1:University', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:teachingAssistantOf', _, X1],O1,_) \ fact(['a1:Course', X1],add,U) <=> member(del,[O1]) | fact(['a1:Course', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', X, Y],O1,_) \ fact(['a1:degreeFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:listedCourse', X, _],O1,_) \ fact(['a1:Schedule', X],add,U) <=> member(del,[O1]) | fact(['a1:Schedule', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:GraduateStudent', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:ResearchAssistant', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:UndergraduateStudent', X],O1,_) \ fact(['a1:Student', X],add,U) <=> member(del,[O1]) | fact(['a1:Student', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', X, Y],O1,_) \ fact(['a1:degreeFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:publicationAuthor', X, _],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:College', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X, _],O1,_) \ fact(['a1:Faculty', X],add,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:ResearchGroup', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:UnofficialPublication', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:researchProject', X, _],O1,_) \ fact(['a1:ResearchGroup', X],add,U) <=> member(del,[O1]) | fact(['a1:ResearchGroup', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:worksFor', X, X1],O2,_), fact(['a1:Organization', X1],O3,_) \ fact(['a1:Employee', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Employee', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Chair', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:affiliateOf', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:GraduateCourse', X],O1,_) \ fact(['a1:Course', X],add,U) <=> member(del,[O1]) | fact(['a1:Course', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:takesCourse', X, X1],O2,_), fact(['a1:Course', X1],O3,_) \ fact(['a1:Student', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Student', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Dean', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:orgPublication', _, X1],O1,_) \ fact(['a1:Publication', X1],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X1],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Manual', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:headOf', X, X1],O1,_), fact(['a1:College', X1],O2,_) \ fact(['a1:Dean', X],add,U) <=> member(del,[O1,O2]) | fact(['a1:Dean', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:TeachingAssistant', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:connectedCourses', Y, X],O1,_) \ fact(['a1:connectedCourses', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:connectedCourses', X, Y],chk,U), applied_rules(1,del).
phase(1), fact(['a1:Student', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:emailAddress', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],chk,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', X, Y],O1,_), fact(['a1:subOrganizationOf', Y, Z],O2,_) \ fact(['a1:subOrganizationOf', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:subOrganizationOf', X, Z],chk,U), applied_rules(1,del).

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
fact(['a1:colleagues', X, Y],prv,_), fact(['a1:colleagues', Y, Z],prv,_) \ fact(['a1:colleagues', X, Z],O,U) <=> member(O,[chk,chk1]) | fact(['a1:colleagues', X, Z],prv,U), applied_rules(1,fwd).
fact(['a1:mastersDegreeFrom', _, X1],prv,_) \ fact(['a1:University', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X1],prv,U), applied_rules(1,fwd).
fact(['a1:title', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:hasAlumnus', Y, X],prv,_) \ fact(['a1:degreeFrom', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:degreeFrom', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:degreeFrom', Y, X],prv,_) \ fact(['a1:hasAlumnus', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:hasAlumnus', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:Faculty', X],prv,_) \ fact(['a1:Employee', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Employee', X],prv,U), applied_rules(1,fwd).
fact(['a1:Professor', X],prv,_) \ fact(['a1:Faculty', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Faculty', X],prv,U), applied_rules(1,fwd).
fact(['a1:listedCourse', _, X1],prv,_) \ fact(['a1:Course', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Course', X1],prv,U), applied_rules(1,fwd).
fact(['a1:AssociateProfessor', X],prv,_) \ fact(['a1:Professor', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,U), applied_rules(1,fwd).
fact(['a1:member', _, X1],prv,_) \ fact(['a1:Person', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X1],prv,U), applied_rules(1,fwd).
fact(['a1:AssistantProfessor', X],prv,_) \ fact(['a1:Professor', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,U), applied_rules(1,fwd).
fact(['a1:orgPublication', X, _],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:Chair', X],prv,_) \ fact(['a1:Professor', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,U), applied_rules(1,fwd).
fact(['a1:TechnicalReport', X],prv,_) \ fact(['a1:Article', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Article', X],prv,U), applied_rules(1,fwd).
fact(['a1:colleagues', Y, X],prv,_) \ fact(['a1:colleagues', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:colleagues', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:headOf', X, Y],prv,_) \ fact(['a1:worksFor', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:worksFor', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:age', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:degreeFrom', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:degreeFrom', _, X1],prv,_) \ fact(['a1:University', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X1],prv,U), applied_rules(1,fwd).
fact(['a1:Specification', X],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:SystemsStaff', X],prv,_) \ fact(['a1:AdministrativeStaff', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:AdministrativeStaff', X],prv,U), applied_rules(1,fwd).
fact(['a1:hasAlumnus', _, X1],prv,_) \ fact(['a1:Person', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X1],prv,U), applied_rules(1,fwd).
fact(['a1:softwareDocumentation', _, X1],prv,_) \ fact(['a1:Publication', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X1],prv,U), applied_rules(1,fwd).
fact(['a1:PostDoc', X],prv,_) \ fact(['a1:Faculty', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Faculty', X],prv,U), applied_rules(1,fwd).
fact(['a1:teacherOf', X0, X1],prv,_), fact(['a1:connectedCourses', X1, X2],prv,_), fact(['a1:teacherOf', X3, X2],prv,_) \ fact(['a1:colleagues', X0, X3],O,U) <=> member(O,[chk,chk1]) | fact(['a1:colleagues', X0, X3],prv,U), applied_rules(1,fwd).
fact(['a1:softwareVersion', X, _],prv,_) \ fact(['a1:Software', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Software', X],prv,U), applied_rules(1,fwd).
fact(['a1:ConferencePaper', X],prv,_) \ fact(['a1:Article', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Article', X],prv,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,_), fact(['a1:teachingAssistantOf', X, X1],prv,_), fact(['a1:Course', X1],prv,_) \ fact(['a1:TeachingAssistant', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:TeachingAssistant', X],prv,U), applied_rules(1,fwd).
fact(['a1:affiliateOf', _, X1],prv,_) \ fact(['a1:Person', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X1],prv,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,_), fact(['a1:headOf', X, X1],prv,_), fact(['a1:Department', X1],prv,_) \ fact(['a1:Chair', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Chair', X],prv,U), applied_rules(1,fwd).
fact(['a1:connectedCourses', X, Y],prv,_), fact(['a1:connectedCourses', Y, Z],prv,_) \ fact(['a1:connectedCourses', X, Z],O,U) <=> member(O,[chk,chk1]) | fact(['a1:connectedCourses', X, Z],prv,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,_), fact(['a1:headOf', X, X1],prv,_), fact(['a1:Program', X1],prv,_) \ fact(['a1:Director', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Director', X],prv,U), applied_rules(1,fwd).
fact(['a1:member', Y, X],prv,_) \ fact(['a1:memberOf', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:memberOf', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:memberOf', Y, X],prv,_) \ fact(['a1:member', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:member', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:tenured', X, _],prv,_) \ fact(['a1:Professor', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,U), applied_rules(1,fwd).
fact(['a1:takesCourse', X1, X0],prv,_), fact(['a1:takesCourse', X1, X2],prv,_) \ fact(['a1:connectedCourses', X0, X2],O,U) <=> member(O,[chk,chk1]) | fact(['a1:connectedCourses', X0, X2],prv,U), applied_rules(1,fwd).
fact(['a1:teacherOf', _, X1],prv,_) \ fact(['a1:Course', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Course', X1],prv,U), applied_rules(1,fwd).
fact(['a1:hasAlumnus', X, _],prv,_) \ fact(['a1:University', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X],prv,U), applied_rules(1,fwd).
fact(['a1:advisor', X1, X0],prv,_), fact(['a1:takesCourse', X1, X2],prv,_) \ fact(['a1:advisor_takesCourse', X0, X2],O,U) <=> member(O,[chk,chk1]) | fact(['a1:advisor_takesCourse', X0, X2],prv,U), applied_rules(1,fwd).
fact(['a1:Research', X],prv,_) \ fact(['a1:Work', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Work', X],prv,U), applied_rules(1,fwd).
fact(['a1:telephone', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:Institute', X],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:subOrganizationOf', _, X1],prv,_) \ fact(['a1:Organization', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X1],prv,U), applied_rules(1,fwd).
fact(['a1:worksFor', X, Y],prv,_) \ fact(['a1:memberOf', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:memberOf', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:Employee', X],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:softwareDocumentation', X, _],prv,_) \ fact(['a1:Software', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Software', X],prv,U), applied_rules(1,fwd).
fact(['a1:advisor', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:teacherOf', X0, X1],prv,_), fact(['a1:takesCourse', X2, X1],prv,_), fact(['a1:advisor', X2, X3],prv,_) \ fact(['a1:colleagues', X0, X3],O,U) <=> member(O,[chk,chk1]) | fact(['a1:colleagues', X0, X3],prv,U), applied_rules(1,fwd).
fact(['a1:member', X, _],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:Department', X],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:Article', X],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:Lecturer', X],prv,_) \ fact(['a1:Faculty', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Faculty', X],prv,U), applied_rules(1,fwd).
fact(['a1:publicationAuthor', _, X1],prv,_) \ fact(['a1:Person', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X1],prv,U), applied_rules(1,fwd).
fact(['a1:researchProject', _, X1],prv,_) \ fact(['a1:Research', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Research', X1],prv,U), applied_rules(1,fwd).
fact(['a1:Software', X],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:advisor_takesCourse', X0, X1],prv,_), fact(['a1:advisor_takesCourse', X2, X1],prv,_) \ fact(['a1:colleagues', X0, X2],O,U) <=> member(O,[chk,chk1]) | fact(['a1:colleagues', X0, X2],prv,U), applied_rules(1,fwd).
fact(['a1:Program', X],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:AdministrativeStaff', X],prv,_) \ fact(['a1:Employee', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Employee', X],prv,U), applied_rules(1,fwd).
fact(['a1:advisor', _, X1],prv,_) \ fact(['a1:Professor', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X1],prv,U), applied_rules(1,fwd).
fact(['a1:Course', X],prv,_) \ fact(['a1:Work', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Work', X],prv,U), applied_rules(1,fwd).
fact(['a1:Book', X],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:FullProfessor', X],prv,_) \ fact(['a1:Professor', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,U), applied_rules(1,fwd).
fact(['a1:publicationResearch', X, _],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:doctoralDegreeFrom', X, Y],prv,_) \ fact(['a1:degreeFrom', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:degreeFrom', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:ClericalStaff', X],prv,_) \ fact(['a1:AdministrativeStaff', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:AdministrativeStaff', X],prv,U), applied_rules(1,fwd).
fact(['a1:affiliatedOrganizationOf', X, _],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:teachingAssistantOf', X, _],prv,_) \ fact(['a1:TeachingAssistant', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:TeachingAssistant', X],prv,U), applied_rules(1,fwd).
fact(['a1:VisitingProfessor', X],prv,_) \ fact(['a1:Professor', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,U), applied_rules(1,fwd).
fact(['a1:undergraduateDegreeFrom', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:University', X],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:JournalArticle', X],prv,_) \ fact(['a1:Article', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Article', X],prv,U), applied_rules(1,fwd).
fact(['a1:publicationResearch', _, X1],prv,_) \ fact(['a1:Research', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Research', X1],prv,U), applied_rules(1,fwd).
fact(['a1:Director', X],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:doctoralDegreeFrom', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:publicationDate', X, _],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:affiliatedOrganizationOf', _, X1],prv,_) \ fact(['a1:Organization', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X1],prv,U), applied_rules(1,fwd).
fact(['a1:doctoralDegreeFrom', _, X1],prv,_) \ fact(['a1:University', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X1],prv,U), applied_rules(1,fwd).
fact(['a1:undergraduateDegreeFrom', _, X1],prv,_) \ fact(['a1:University', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:University', X1],prv,U), applied_rules(1,fwd).
fact(['a1:teachingAssistantOf', _, X1],prv,_) \ fact(['a1:Course', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Course', X1],prv,U), applied_rules(1,fwd).
fact(['a1:mastersDegreeFrom', X, Y],prv,_) \ fact(['a1:degreeFrom', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:degreeFrom', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:listedCourse', X, _],prv,_) \ fact(['a1:Schedule', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Schedule', X],prv,U), applied_rules(1,fwd).
fact(['a1:GraduateStudent', X],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:ResearchAssistant', X],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:UndergraduateStudent', X],prv,_) \ fact(['a1:Student', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Student', X],prv,U), applied_rules(1,fwd).
fact(['a1:undergraduateDegreeFrom', X, Y],prv,_) \ fact(['a1:degreeFrom', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:degreeFrom', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:publicationAuthor', X, _],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:mastersDegreeFrom', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:College', X],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:teacherOf', X, _],prv,_) \ fact(['a1:Faculty', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Faculty', X],prv,U), applied_rules(1,fwd).
fact(['a1:ResearchGroup', X],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:UnofficialPublication', X],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:researchProject', X, _],prv,_) \ fact(['a1:ResearchGroup', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:ResearchGroup', X],prv,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,_), fact(['a1:worksFor', X, X1],prv,_), fact(['a1:Organization', X1],prv,_) \ fact(['a1:Employee', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Employee', X],prv,U), applied_rules(1,fwd).
fact(['a1:Chair', X],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:affiliateOf', X, _],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:GraduateCourse', X],prv,_) \ fact(['a1:Course', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Course', X],prv,U), applied_rules(1,fwd).
fact(['a1:Person', X],prv,_), fact(['a1:takesCourse', X, X1],prv,_), fact(['a1:Course', X1],prv,_) \ fact(['a1:Student', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Student', X],prv,U), applied_rules(1,fwd).
fact(['a1:Dean', X],prv,_) \ fact(['a1:Professor', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Professor', X],prv,U), applied_rules(1,fwd).
fact(['a1:orgPublication', _, X1],prv,_) \ fact(['a1:Publication', X1],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X1],prv,U), applied_rules(1,fwd).
fact(['a1:Manual', X],prv,_) \ fact(['a1:Publication', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Publication', X],prv,U), applied_rules(1,fwd).
fact(['a1:headOf', X, X1],prv,_), fact(['a1:College', X1],prv,_) \ fact(['a1:Dean', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Dean', X],prv,U), applied_rules(1,fwd).
fact(['a1:TeachingAssistant', X],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:subOrganizationOf', X, _],prv,_) \ fact(['a1:Organization', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Organization', X],prv,U), applied_rules(1,fwd).
fact(['a1:connectedCourses', Y, X],prv,_) \ fact(['a1:connectedCourses', X, Y],O,U) <=> member(O,[chk,chk1]) | fact(['a1:connectedCourses', X, Y],prv,U), applied_rules(1,fwd).
fact(['a1:Student', X],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:emailAddress', X, _],prv,_) \ fact(['a1:Person', X],O,U) <=> member(O,[chk,chk1]) | fact(['a1:Person', X],prv,U), applied_rules(1,fwd).
fact(['a1:subOrganizationOf', X, Y],prv,_), fact(['a1:subOrganizationOf', Y, Z],prv,_) \ fact(['a1:subOrganizationOf', X, Z],O,U) <=> member(O,[chk,chk1]) | fact(['a1:subOrganizationOf', X, Z],prv,U), applied_rules(1,fwd).


% - backward -
fact(['a1:colleagues', X, Z],chk1,_), fact(['a1:colleagues', X, Y],O1,U1), fact(['a1:colleagues', Y, Z],O2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:colleagues', X, Y],chk1,U1), fact(['a1:colleagues', Y, Z],chk1,U2), applied_rules(1,bwd).
fact(['a1:University', X1],chk1,_), fact(['a1:mastersDegreeFrom', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:mastersDegreeFrom', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:title', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:title', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:degreeFrom', X, Y],chk1,_), fact(['a1:hasAlumnus', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:hasAlumnus', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['a1:hasAlumnus', X, Y],chk1,_), fact(['a1:degreeFrom', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:degreeFrom', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Employee', X],chk1,_), fact(['a1:Faculty', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Faculty', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Faculty', X],chk1,_), fact(['a1:Professor', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Professor', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Course', X1],chk1,_), fact(['a1:listedCourse', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:listedCourse', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_), fact(['a1:AssociateProfessor', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:AssociateProfessor', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X1],chk1,_), fact(['a1:member', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:member', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_), fact(['a1:AssistantProfessor', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:AssistantProfessor', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:orgPublication', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:orgPublication', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_), fact(['a1:Chair', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Chair', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Article', X],chk1,_), fact(['a1:TechnicalReport', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:TechnicalReport', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:colleagues', X, Y],chk1,_), fact(['a1:colleagues', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:colleagues', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['a1:worksFor', X, Y],chk1,_), fact(['a1:headOf', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['a1:headOf', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:age', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:age', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:degreeFrom', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:degreeFrom', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:University', X1],chk1,_), fact(['a1:degreeFrom', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:degreeFrom', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:Specification', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Specification', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:AdministrativeStaff', X],chk1,_), fact(['a1:SystemsStaff', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:SystemsStaff', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X1],chk1,_), fact(['a1:hasAlumnus', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:hasAlumnus', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X1],chk1,_), fact(['a1:softwareDocumentation', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:softwareDocumentation', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Faculty', X],chk1,_), fact(['a1:PostDoc', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:PostDoc', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:colleagues', X0, X3],chk1,_), fact(['a1:teacherOf', X0, X1],O1,U1), fact(['a1:connectedCourses', X1, X2],O2,U2), fact(['a1:teacherOf', X3, X2],O3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:teacherOf', X0, X1],chk1,U1), fact(['a1:connectedCourses', X1, X2],chk1,U2), fact(['a1:teacherOf', X3, X2],chk1,U3), applied_rules(1,bwd).
fact(['a1:Software', X],chk1,_), fact(['a1:softwareVersion', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:softwareVersion', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Article', X],chk1,_), fact(['a1:ConferencePaper', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:ConferencePaper', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:TeachingAssistant', X],chk1,_), fact(['a1:Person', X],O1,U1), fact(['a1:teachingAssistantOf', X, X1],O2,U2), fact(['a1:Course', X1],O3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,U1), fact(['a1:teachingAssistantOf', X, X1],chk1,U2), fact(['a1:Course', X1],chk1,U3), applied_rules(1,bwd).
fact(['a1:Person', X1],chk1,_), fact(['a1:affiliateOf', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:affiliateOf', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Chair', X],chk1,_), fact(['a1:Person', X],O1,U1), fact(['a1:headOf', X, X1],O2,U2), fact(['a1:Department', X1],O3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,U1), fact(['a1:headOf', X, X1],chk1,U2), fact(['a1:Department', X1],chk1,U3), applied_rules(1,bwd).
fact(['a1:connectedCourses', X, Z],chk1,_), fact(['a1:connectedCourses', X, Y],O1,U1), fact(['a1:connectedCourses', Y, Z],O2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:connectedCourses', X, Y],chk1,U1), fact(['a1:connectedCourses', Y, Z],chk1,U2), applied_rules(1,bwd).
fact(['a1:Director', X],chk1,_), fact(['a1:Person', X],O1,U1), fact(['a1:headOf', X, X1],O2,U2), fact(['a1:Program', X1],O3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,U1), fact(['a1:headOf', X, X1],chk1,U2), fact(['a1:Program', X1],chk1,U3), applied_rules(1,bwd).
fact(['a1:memberOf', X, Y],chk1,_), fact(['a1:member', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:member', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['a1:member', X, Y],chk1,_), fact(['a1:memberOf', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:memberOf', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_), fact(['a1:tenured', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:tenured', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:connectedCourses', X0, X2],chk1,_), fact(['a1:takesCourse', X1, X0],O1,U1), fact(['a1:takesCourse', X1, X2],O2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:takesCourse', X1, X0],chk1,U1), fact(['a1:takesCourse', X1, X2],chk1,U2), applied_rules(1,bwd).
fact(['a1:Course', X1],chk1,_), fact(['a1:teacherOf', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:teacherOf', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:University', X],chk1,_), fact(['a1:hasAlumnus', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:hasAlumnus', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:advisor_takesCourse', X0, X2],chk1,_), fact(['a1:advisor', X1, X0],O1,U1), fact(['a1:takesCourse', X1, X2],O2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:advisor', X1, X0],chk1,U1), fact(['a1:takesCourse', X1, X2],chk1,U2), applied_rules(1,bwd).
fact(['a1:Work', X],chk1,_), fact(['a1:Research', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Research', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:telephone', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:telephone', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:Institute', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Institute', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X1],chk1,_), fact(['a1:subOrganizationOf', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:subOrganizationOf', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:memberOf', X, Y],chk1,_), fact(['a1:worksFor', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['a1:worksFor', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:Employee', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Employee', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Software', X],chk1,_), fact(['a1:softwareDocumentation', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:softwareDocumentation', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:advisor', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:advisor', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:colleagues', X0, X3],chk1,_), fact(['a1:teacherOf', X0, X1],O1,U1), fact(['a1:takesCourse', X2, X1],O2,U2), fact(['a1:advisor', X2, X3],O3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:teacherOf', X0, X1],chk1,U1), fact(['a1:takesCourse', X2, X1],chk1,U2), fact(['a1:advisor', X2, X3],chk1,U3), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:member', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:member', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:Department', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Department', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:Article', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Article', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Faculty', X],chk1,_), fact(['a1:Lecturer', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Lecturer', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X1],chk1,_), fact(['a1:publicationAuthor', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationAuthor', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Research', X1],chk1,_), fact(['a1:researchProject', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:researchProject', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:Software', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Software', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:colleagues', X0, X2],chk1,_), fact(['a1:advisor_takesCourse', X0, X1],O1,U1), fact(['a1:advisor_takesCourse', X2, X1],O2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:advisor_takesCourse', X0, X1],chk1,U1), fact(['a1:advisor_takesCourse', X2, X1],chk1,U2), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:Program', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Program', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Employee', X],chk1,_), fact(['a1:AdministrativeStaff', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:AdministrativeStaff', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X1],chk1,_), fact(['a1:advisor', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:advisor', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Work', X],chk1,_), fact(['a1:Course', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Course', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:Book', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Book', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_), fact(['a1:FullProfessor', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:FullProfessor', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:publicationResearch', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationResearch', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:degreeFrom', X, Y],chk1,_), fact(['a1:doctoralDegreeFrom', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['a1:doctoralDegreeFrom', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['a1:AdministrativeStaff', X],chk1,_), fact(['a1:ClericalStaff', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:ClericalStaff', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:affiliatedOrganizationOf', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:affiliatedOrganizationOf', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:TeachingAssistant', X],chk1,_), fact(['a1:teachingAssistantOf', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:teachingAssistantOf', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_), fact(['a1:VisitingProfessor', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:VisitingProfessor', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:undergraduateDegreeFrom', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:undergraduateDegreeFrom', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:University', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:University', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Article', X],chk1,_), fact(['a1:JournalArticle', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:JournalArticle', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Research', X1],chk1,_), fact(['a1:publicationResearch', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationResearch', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:Director', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Director', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:doctoralDegreeFrom', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:doctoralDegreeFrom', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:publicationDate', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationDate', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X1],chk1,_), fact(['a1:affiliatedOrganizationOf', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:affiliatedOrganizationOf', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:University', X1],chk1,_), fact(['a1:doctoralDegreeFrom', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:doctoralDegreeFrom', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:University', X1],chk1,_), fact(['a1:undergraduateDegreeFrom', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:undergraduateDegreeFrom', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Course', X1],chk1,_), fact(['a1:teachingAssistantOf', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:teachingAssistantOf', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:degreeFrom', X, Y],chk1,_), fact(['a1:mastersDegreeFrom', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['a1:mastersDegreeFrom', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['a1:Schedule', X],chk1,_), fact(['a1:listedCourse', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:listedCourse', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:GraduateStudent', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:GraduateStudent', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:ResearchAssistant', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:ResearchAssistant', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Student', X],chk1,_), fact(['a1:UndergraduateStudent', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:UndergraduateStudent', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:degreeFrom', X, Y],chk1,_), fact(['a1:undergraduateDegreeFrom', X, Y],O1,U1) ==> \+member(del,[O1]) | fact(['a1:undergraduateDegreeFrom', X, Y],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:publicationAuthor', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:publicationAuthor', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:mastersDegreeFrom', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:mastersDegreeFrom', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:College', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:College', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Faculty', X],chk1,_), fact(['a1:teacherOf', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:teacherOf', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:ResearchGroup', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:ResearchGroup', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:UnofficialPublication', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:UnofficialPublication', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:ResearchGroup', X],chk1,_), fact(['a1:researchProject', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:researchProject', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Employee', X],chk1,_), fact(['a1:Person', X],O1,U1), fact(['a1:worksFor', X, X1],O2,U2), fact(['a1:Organization', X1],O3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,U1), fact(['a1:worksFor', X, X1],chk1,U2), fact(['a1:Organization', X1],chk1,U3), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:Chair', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Chair', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:affiliateOf', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:affiliateOf', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:Course', X],chk1,_), fact(['a1:GraduateCourse', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:GraduateCourse', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Student', X],chk1,_), fact(['a1:Person', X],O1,U1), fact(['a1:takesCourse', X, X1],O2,U2), fact(['a1:Course', X1],O3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:Person', X],chk1,U1), fact(['a1:takesCourse', X, X1],chk1,U2), fact(['a1:Course', X1],chk1,U3), applied_rules(1,bwd).
fact(['a1:Professor', X],chk1,_), fact(['a1:Dean', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Dean', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X1],chk1,_), fact(['a1:orgPublication', Anon0, X1],O1,U1) ==> \+member(del,[O1]) | fact(['a1:orgPublication', Anon0, X1],chk1,U1), applied_rules(1,bwd).
fact(['a1:Publication', X],chk1,_), fact(['a1:Manual', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Manual', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Dean', X],chk1,_), fact(['a1:headOf', X, X1],O1,U1), fact(['a1:College', X1],O2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:headOf', X, X1],chk1,U1), fact(['a1:College', X1],chk1,U2), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:TeachingAssistant', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:TeachingAssistant', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Organization', X],chk1,_), fact(['a1:subOrganizationOf', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:subOrganizationOf', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:connectedCourses', X, Y],chk1,_), fact(['a1:connectedCourses', Y, X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:connectedCourses', Y, X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:Student', X],O1,U1) ==> \+member(del,[O1]) | fact(['a1:Student', X],chk1,U1), applied_rules(1,bwd).
fact(['a1:Person', X],chk1,_), fact(['a1:emailAddress', X, Anon0],O1,U1) ==> \+member(del,[O1]) | fact(['a1:emailAddress', X, Anon0],chk1,U1), applied_rules(1,bwd).
fact(['a1:subOrganizationOf', X, Z],chk1,_), fact(['a1:subOrganizationOf', X, Y],O1,U1), fact(['a1:subOrganizationOf', Y, Z],O2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:subOrganizationOf', X, Y],chk1,U1), fact(['a1:subOrganizationOf', Y, Z],chk1,U2), applied_rules(1,bwd).

	
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
phase(5), fact(['a1:colleagues', X, Y],add,U1), fact(['a1:colleagues', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:colleagues', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:mastersDegreeFrom', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:University', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:title', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:hasAlumnus', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:degreeFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:degreeFrom', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:hasAlumnus', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Faculty', X],add,U1) ==> member(U,[U1]) | fact(['a1:Employee', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Professor', X],add,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:listedCourse', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Course', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:AssociateProfessor', X],add,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:member', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:AssistantProfessor', X],add,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:orgPublication', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Chair', X],add,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:TechnicalReport', X],add,U1) ==> member(U,[U1]) | fact(['a1:Article', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:colleagues', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:colleagues', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:headOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:worksFor', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:age', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:degreeFrom', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:degreeFrom', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:University', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Specification', X],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:SystemsStaff', X],add,U1) ==> member(U,[U1]) | fact(['a1:AdministrativeStaff', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:hasAlumnus', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:softwareDocumentation', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:PostDoc', X],add,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', X0, X1],add,U1), fact(['a1:connectedCourses', X1, X2],add,U2), fact(['a1:teacherOf', X3, X2],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:colleagues', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:softwareVersion', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Software', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:ConferencePaper', X],add,U1) ==> member(U,[U1]) | fact(['a1:Article', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,U1), fact(['a1:teachingAssistantOf', X, X1],add,U2), fact(['a1:Course', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:TeachingAssistant', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliateOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,U1), fact(['a1:headOf', X, X1],add,U2), fact(['a1:Department', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:Chair', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:connectedCourses', X, Y],add,U1), fact(['a1:connectedCourses', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:connectedCourses', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,U1), fact(['a1:headOf', X, X1],add,U2), fact(['a1:Program', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:Director', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:member', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:memberOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:memberOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:member', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:tenured', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:takesCourse', X1, X0],add,U1), fact(['a1:takesCourse', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['a1:connectedCourses', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Course', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:hasAlumnus', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:University', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor', X1, X0],add,U1), fact(['a1:takesCourse', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['a1:advisor_takesCourse', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Research', X],add,U1) ==> member(U,[U1]) | fact(['a1:Work', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:telephone', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Institute', X],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:worksFor', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:memberOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Employee', X],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:softwareDocumentation', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Software', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', X0, X1],add,U1), fact(['a1:takesCourse', X2, X1],add,U2), fact(['a1:advisor', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:colleagues', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:member', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Department', X],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Article', X],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Lecturer', X],add,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationAuthor', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:researchProject', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Research', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Software', X],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor_takesCourse', X0, X1],add,U1), fact(['a1:advisor_takesCourse', X2, X1],add,U2) ==> member(U,[U1,U2]) | fact(['a1:colleagues', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Program', X],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:AdministrativeStaff', X],add,U1) ==> member(U,[U1]) | fact(['a1:Employee', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Professor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Course', X],add,U1) ==> member(U,[U1]) | fact(['a1:Work', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Book', X],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:FullProfessor', X],add,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationResearch', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:doctoralDegreeFrom', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:degreeFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:ClericalStaff', X],add,U1) ==> member(U,[U1]) | fact(['a1:AdministrativeStaff', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliatedOrganizationOf', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:teachingAssistantOf', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:TeachingAssistant', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:VisitingProfessor', X],add,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:undergraduateDegreeFrom', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:University', X],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:JournalArticle', X],add,U1) ==> member(U,[U1]) | fact(['a1:Article', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationResearch', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Research', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Director', X],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:doctoralDegreeFrom', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationDate', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliatedOrganizationOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:doctoralDegreeFrom', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:University', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:undergraduateDegreeFrom', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:University', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:teachingAssistantOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Course', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:mastersDegreeFrom', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:degreeFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:listedCourse', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Schedule', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:GraduateStudent', X],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:ResearchAssistant', X],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:UndergraduateStudent', X],add,U1) ==> member(U,[U1]) | fact(['a1:Student', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:undergraduateDegreeFrom', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:degreeFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationAuthor', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:mastersDegreeFrom', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:College', X],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:ResearchGroup', X],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:UnofficialPublication', X],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:researchProject', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:ResearchGroup', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,U1), fact(['a1:worksFor', X, X1],add,U2), fact(['a1:Organization', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:Employee', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Chair', X],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliateOf', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:GraduateCourse', X],add,U1) ==> member(U,[U1]) | fact(['a1:Course', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,U1), fact(['a1:takesCourse', X, X1],add,U2), fact(['a1:Course', X1],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:Student', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Dean', X],add,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:orgPublication', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Manual', X],add,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:headOf', X, X1],add,U1), fact(['a1:College', X1],add,U2) ==> member(U,[U1,U2]) | fact(['a1:Dean', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:TeachingAssistant', X],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:connectedCourses', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:connectedCourses', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:Student', X],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:emailAddress', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', X, Y],add,U1), fact(['a1:subOrganizationOf', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:subOrganizationOf', X, Z],add,U), applied_rules(1,ins).

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
