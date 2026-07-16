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
phase(1), fact(['a1:colleagues', X, Y],O1,_), fact(['a1:colleagues', Y, Z],O2,_) \ fact(['a1:colleagues', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:colleagues', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', _, X1],O1,_) \ fact(['a1:University', X1],add,U) <=> member(del,[O1]) | fact(['a1:University', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:title', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', Y, X],O1,_) \ fact(['a1:degreeFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', Y, X],O1,_) \ fact(['a1:hasAlumnus', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:hasAlumnus', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:Faculty', X],O1,_) \ fact(['a1:Employee', X],add,U) <=> member(del,[O1]) | fact(['a1:Employee', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Professor', X],O1,_) \ fact(['a1:Faculty', X],add,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:listedCourse', _, X1],O1,_) \ fact(['a1:Course', X1],add,U) <=> member(del,[O1]) | fact(['a1:Course', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:AssociateProfessor', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:member', _, X1],O1,_) \ fact(['a1:Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:AssistantProfessor', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:orgPublication', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Chair', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:TechnicalReport', X],O1,_) \ fact(['a1:Article', X],add,U) <=> member(del,[O1]) | fact(['a1:Article', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:colleagues', Y, X],O1,_) \ fact(['a1:colleagues', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:colleagues', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:headOf', X, Y],O1,_) \ fact(['a1:worksFor', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:worksFor', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:age', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', _, X1],O1,_) \ fact(['a1:University', X1],add,U) <=> member(del,[O1]) | fact(['a1:University', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:Specification', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:SystemsStaff', X],O1,_) \ fact(['a1:AdministrativeStaff', X],add,U) <=> member(del,[O1]) | fact(['a1:AdministrativeStaff', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', _, X1],O1,_) \ fact(['a1:Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:softwareDocumentation', _, X1],O1,_) \ fact(['a1:Publication', X1],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:PostDoc', X],O1,_) \ fact(['a1:Faculty', X],add,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X0, X1],O1,_), fact(['a1:connectedCourses', X1, X2],O2,_), fact(['a1:teacherOf', X3, X2],O3,_) \ fact(['a1:colleagues', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:colleagues', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:softwareVersion', X, _],O1,_) \ fact(['a1:Software', X],add,U) <=> member(del,[O1]) | fact(['a1:Software', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:ConferencePaper', X],O1,_) \ fact(['a1:Article', X],add,U) <=> member(del,[O1]) | fact(['a1:Article', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:teachingAssistantOf', X, X1],O2,_), fact(['a1:Course', X1],O3,_) \ fact(['a1:TeachingAssistant', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:TeachingAssistant', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:affiliateOf', _, X1],O1,_) \ fact(['a1:Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:headOf', X, X1],O2,_), fact(['a1:Department', X1],O3,_) \ fact(['a1:Chair', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Chair', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:connectedCourses', X, Y],O1,_), fact(['a1:connectedCourses', Y, Z],O2,_) \ fact(['a1:connectedCourses', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:connectedCourses', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:headOf', X, X1],O2,_), fact(['a1:Program', X1],O3,_) \ fact(['a1:Director', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Director', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:member', Y, X],O1,_) \ fact(['a1:memberOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:memberOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:memberOf', Y, X],O1,_) \ fact(['a1:member', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:member', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:tenured', X, _],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:takesCourse', X1, X0],O1,_), fact(['a1:takesCourse', X1, X2],O2,_) \ fact(['a1:connectedCourses', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:connectedCourses', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', _, X1],O1,_) \ fact(['a1:Course', X1],add,U) <=> member(del,[O1]) | fact(['a1:Course', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', X, _],O1,_) \ fact(['a1:University', X],add,U) <=> member(del,[O1]) | fact(['a1:University', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', X1, X0],O1,_), fact(['a1:takesCourse', X1, X2],O2,_) \ fact(['a1:advisor_takesCourse', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:advisor_takesCourse', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:Research', X],O1,_) \ fact(['a1:Work', X],add,U) <=> member(del,[O1]) | fact(['a1:Work', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:telephone', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Institute', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', _, X1],O1,_) \ fact(['a1:Organization', X1],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:worksFor', X, Y],O1,_) \ fact(['a1:memberOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:memberOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:Employee', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:softwareDocumentation', X, _],O1,_) \ fact(['a1:Software', X],add,U) <=> member(del,[O1]) | fact(['a1:Software', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X0, X1],O1,_), fact(['a1:takesCourse', X2, X1],O2,_), fact(['a1:advisor', X2, X3],O3,_) \ fact(['a1:colleagues', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:colleagues', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:member', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Department', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Article', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Lecturer', X],O1,_) \ fact(['a1:Faculty', X],add,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:publicationAuthor', _, X1],O1,_) \ fact(['a1:Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:researchProject', _, X1],O1,_) \ fact(['a1:Research', X1],add,U) <=> member(del,[O1]) | fact(['a1:Research', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:Software', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:advisor_takesCourse', X0, X1],O1,_), fact(['a1:advisor_takesCourse', X2, X1],O2,_) \ fact(['a1:colleagues', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:colleagues', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:Program', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:AdministrativeStaff', X],O1,_) \ fact(['a1:Employee', X],add,U) <=> member(del,[O1]) | fact(['a1:Employee', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', _, X1],O1,_) \ fact(['a1:Professor', X1],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:Course', X],O1,_) \ fact(['a1:Work', X],add,U) <=> member(del,[O1]) | fact(['a1:Work', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Book', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:FullProfessor', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:publicationResearch', X, _],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', X, Y],O1,_) \ fact(['a1:degreeFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:ClericalStaff', X],O1,_) \ fact(['a1:AdministrativeStaff', X],add,U) <=> member(del,[O1]) | fact(['a1:AdministrativeStaff', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:affiliatedOrganizationOf', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:teachingAssistantOf', X, _],O1,_) \ fact(['a1:TeachingAssistant', X],add,U) <=> member(del,[O1]) | fact(['a1:TeachingAssistant', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:VisitingProfessor', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:University', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:JournalArticle', X],O1,_) \ fact(['a1:Article', X],add,U) <=> member(del,[O1]) | fact(['a1:Article', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:publicationResearch', _, X1],O1,_) \ fact(['a1:Research', X1],add,U) <=> member(del,[O1]) | fact(['a1:Research', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:Director', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:publicationDate', X, _],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:affiliatedOrganizationOf', _, X1],O1,_) \ fact(['a1:Organization', X1],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', _, X1],O1,_) \ fact(['a1:University', X1],add,U) <=> member(del,[O1]) | fact(['a1:University', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', _, X1],O1,_) \ fact(['a1:University', X1],add,U) <=> member(del,[O1]) | fact(['a1:University', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:teachingAssistantOf', _, X1],O1,_) \ fact(['a1:Course', X1],add,U) <=> member(del,[O1]) | fact(['a1:Course', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', X, Y],O1,_) \ fact(['a1:degreeFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:listedCourse', X, _],O1,_) \ fact(['a1:Schedule', X],add,U) <=> member(del,[O1]) | fact(['a1:Schedule', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:GraduateStudent', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:ResearchAssistant', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:UndergraduateStudent', X],O1,_) \ fact(['a1:Student', X],add,U) <=> member(del,[O1]) | fact(['a1:Student', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', X, Y],O1,_) \ fact(['a1:degreeFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:publicationAuthor', X, _],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:College', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X, _],O1,_) \ fact(['a1:Faculty', X],add,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:ResearchGroup', X],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:UnofficialPublication', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:researchProject', X, _],O1,_) \ fact(['a1:ResearchGroup', X],add,U) <=> member(del,[O1]) | fact(['a1:ResearchGroup', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:worksFor', X, X1],O2,_), fact(['a1:Organization', X1],O3,_) \ fact(['a1:Employee', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Employee', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Chair', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:affiliateOf', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:GraduateCourse', X],O1,_) \ fact(['a1:Course', X],add,U) <=> member(del,[O1]) | fact(['a1:Course', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,_), fact(['a1:takesCourse', X, X1],O2,_), fact(['a1:Course', X1],O3,_) \ fact(['a1:Student', X],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:Student', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:Dean', X],O1,_) \ fact(['a1:Professor', X],add,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:orgPublication', _, X1],O1,_) \ fact(['a1:Publication', X1],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:Manual', X],O1,_) \ fact(['a1:Publication', X],add,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:headOf', X, X1],O1,_), fact(['a1:College', X1],O2,_) \ fact(['a1:Dean', X],add,U) <=> member(del,[O1,O2]) | fact(['a1:Dean', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:TeachingAssistant', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', X, _],O1,_) \ fact(['a1:Organization', X],add,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:connectedCourses', Y, X],O1,_) \ fact(['a1:connectedCourses', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:connectedCourses', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:Student', X],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:emailAddress', X, _],O1,_) \ fact(['a1:Person', X],add,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', X, Y],O1,_), fact(['a1:subOrganizationOf', Y, Z],O2,_) \ fact(['a1:subOrganizationOf', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:subOrganizationOf', X, Z],del,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact(['a1:colleagues', X, Y],add,_), fact(['a1:colleagues', Y, Z],add,_) \ fact(['a1:colleagues', X, Z],del,U) <=> true | fact(['a1:colleagues', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:mastersDegreeFrom', _, X1],add,_) \ fact(['a1:University', X1],del,U) <=> true | fact(['a1:University', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:title', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:hasAlumnus', Y, X],add,_) \ fact(['a1:degreeFrom', X, Y],del,U) <=> true | fact(['a1:degreeFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:degreeFrom', Y, X],add,_) \ fact(['a1:hasAlumnus', X, Y],del,U) <=> true | fact(['a1:hasAlumnus', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:Faculty', X],add,_) \ fact(['a1:Employee', X],del,U) <=> true | fact(['a1:Employee', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Professor', X],add,_) \ fact(['a1:Faculty', X],del,U) <=> true | fact(['a1:Faculty', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:listedCourse', _, X1],add,_) \ fact(['a1:Course', X1],del,U) <=> true | fact(['a1:Course', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:AssociateProfessor', X],add,_) \ fact(['a1:Professor', X],del,U) <=> true | fact(['a1:Professor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:member', _, X1],add,_) \ fact(['a1:Person', X1],del,U) <=> true | fact(['a1:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:AssistantProfessor', X],add,_) \ fact(['a1:Professor', X],del,U) <=> true | fact(['a1:Professor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:orgPublication', X, _],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Chair', X],add,_) \ fact(['a1:Professor', X],del,U) <=> true | fact(['a1:Professor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:TechnicalReport', X],add,_) \ fact(['a1:Article', X],del,U) <=> true | fact(['a1:Article', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:colleagues', Y, X],add,_) \ fact(['a1:colleagues', X, Y],del,U) <=> true | fact(['a1:colleagues', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:headOf', X, Y],add,_) \ fact(['a1:worksFor', X, Y],del,U) <=> true | fact(['a1:worksFor', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:age', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:degreeFrom', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:degreeFrom', _, X1],add,_) \ fact(['a1:University', X1],del,U) <=> true | fact(['a1:University', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:Specification', X],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:SystemsStaff', X],add,_) \ fact(['a1:AdministrativeStaff', X],del,U) <=> true | fact(['a1:AdministrativeStaff', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:hasAlumnus', _, X1],add,_) \ fact(['a1:Person', X1],del,U) <=> true | fact(['a1:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:softwareDocumentation', _, X1],add,_) \ fact(['a1:Publication', X1],del,U) <=> true | fact(['a1:Publication', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:PostDoc', X],add,_) \ fact(['a1:Faculty', X],del,U) <=> true | fact(['a1:Faculty', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:teacherOf', X0, X1],add,_), fact(['a1:connectedCourses', X1, X2],add,_), fact(['a1:teacherOf', X3, X2],add,_) \ fact(['a1:colleagues', X0, X3],del,U) <=> true | fact(['a1:colleagues', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:softwareVersion', X, _],add,_) \ fact(['a1:Software', X],del,U) <=> true | fact(['a1:Software', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:ConferencePaper', X],add,_) \ fact(['a1:Article', X],del,U) <=> true | fact(['a1:Article', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,_), fact(['a1:teachingAssistantOf', X, X1],add,_), fact(['a1:Course', X1],add,_) \ fact(['a1:TeachingAssistant', X],del,U) <=> true | fact(['a1:TeachingAssistant', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:affiliateOf', _, X1],add,_) \ fact(['a1:Person', X1],del,U) <=> true | fact(['a1:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,_), fact(['a1:headOf', X, X1],add,_), fact(['a1:Department', X1],add,_) \ fact(['a1:Chair', X],del,U) <=> true | fact(['a1:Chair', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:connectedCourses', X, Y],add,_), fact(['a1:connectedCourses', Y, Z],add,_) \ fact(['a1:connectedCourses', X, Z],del,U) <=> true | fact(['a1:connectedCourses', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,_), fact(['a1:headOf', X, X1],add,_), fact(['a1:Program', X1],add,_) \ fact(['a1:Director', X],del,U) <=> true | fact(['a1:Director', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:member', Y, X],add,_) \ fact(['a1:memberOf', X, Y],del,U) <=> true | fact(['a1:memberOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:memberOf', Y, X],add,_) \ fact(['a1:member', X, Y],del,U) <=> true | fact(['a1:member', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:tenured', X, _],add,_) \ fact(['a1:Professor', X],del,U) <=> true | fact(['a1:Professor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:takesCourse', X1, X0],add,_), fact(['a1:takesCourse', X1, X2],add,_) \ fact(['a1:connectedCourses', X0, X2],del,U) <=> true | fact(['a1:connectedCourses', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:teacherOf', _, X1],add,_) \ fact(['a1:Course', X1],del,U) <=> true | fact(['a1:Course', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:hasAlumnus', X, _],add,_) \ fact(['a1:University', X],del,U) <=> true | fact(['a1:University', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:advisor', X1, X0],add,_), fact(['a1:takesCourse', X1, X2],add,_) \ fact(['a1:advisor_takesCourse', X0, X2],del,U) <=> true | fact(['a1:advisor_takesCourse', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:Research', X],add,_) \ fact(['a1:Work', X],del,U) <=> true | fact(['a1:Work', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:telephone', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Institute', X],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:subOrganizationOf', _, X1],add,_) \ fact(['a1:Organization', X1],del,U) <=> true | fact(['a1:Organization', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:worksFor', X, Y],add,_) \ fact(['a1:memberOf', X, Y],del,U) <=> true | fact(['a1:memberOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:Employee', X],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:softwareDocumentation', X, _],add,_) \ fact(['a1:Software', X],del,U) <=> true | fact(['a1:Software', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:advisor', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:teacherOf', X0, X1],add,_), fact(['a1:takesCourse', X2, X1],add,_), fact(['a1:advisor', X2, X3],add,_) \ fact(['a1:colleagues', X0, X3],del,U) <=> true | fact(['a1:colleagues', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:member', X, _],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Department', X],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Article', X],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Lecturer', X],add,_) \ fact(['a1:Faculty', X],del,U) <=> true | fact(['a1:Faculty', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:publicationAuthor', _, X1],add,_) \ fact(['a1:Person', X1],del,U) <=> true | fact(['a1:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:researchProject', _, X1],add,_) \ fact(['a1:Research', X1],del,U) <=> true | fact(['a1:Research', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:Software', X],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:advisor_takesCourse', X0, X1],add,_), fact(['a1:advisor_takesCourse', X2, X1],add,_) \ fact(['a1:colleagues', X0, X2],del,U) <=> true | fact(['a1:colleagues', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:Program', X],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:AdministrativeStaff', X],add,_) \ fact(['a1:Employee', X],del,U) <=> true | fact(['a1:Employee', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:advisor', _, X1],add,_) \ fact(['a1:Professor', X1],del,U) <=> true | fact(['a1:Professor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:Course', X],add,_) \ fact(['a1:Work', X],del,U) <=> true | fact(['a1:Work', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Book', X],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:FullProfessor', X],add,_) \ fact(['a1:Professor', X],del,U) <=> true | fact(['a1:Professor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:publicationResearch', X, _],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:doctoralDegreeFrom', X, Y],add,_) \ fact(['a1:degreeFrom', X, Y],del,U) <=> true | fact(['a1:degreeFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:ClericalStaff', X],add,_) \ fact(['a1:AdministrativeStaff', X],del,U) <=> true | fact(['a1:AdministrativeStaff', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:affiliatedOrganizationOf', X, _],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:teachingAssistantOf', X, _],add,_) \ fact(['a1:TeachingAssistant', X],del,U) <=> true | fact(['a1:TeachingAssistant', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:VisitingProfessor', X],add,_) \ fact(['a1:Professor', X],del,U) <=> true | fact(['a1:Professor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:undergraduateDegreeFrom', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:University', X],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:JournalArticle', X],add,_) \ fact(['a1:Article', X],del,U) <=> true | fact(['a1:Article', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:publicationResearch', _, X1],add,_) \ fact(['a1:Research', X1],del,U) <=> true | fact(['a1:Research', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:Director', X],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:doctoralDegreeFrom', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:publicationDate', X, _],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:affiliatedOrganizationOf', _, X1],add,_) \ fact(['a1:Organization', X1],del,U) <=> true | fact(['a1:Organization', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:doctoralDegreeFrom', _, X1],add,_) \ fact(['a1:University', X1],del,U) <=> true | fact(['a1:University', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:undergraduateDegreeFrom', _, X1],add,_) \ fact(['a1:University', X1],del,U) <=> true | fact(['a1:University', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:teachingAssistantOf', _, X1],add,_) \ fact(['a1:Course', X1],del,U) <=> true | fact(['a1:Course', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:mastersDegreeFrom', X, Y],add,_) \ fact(['a1:degreeFrom', X, Y],del,U) <=> true | fact(['a1:degreeFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:listedCourse', X, _],add,_) \ fact(['a1:Schedule', X],del,U) <=> true | fact(['a1:Schedule', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:GraduateStudent', X],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:ResearchAssistant', X],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:UndergraduateStudent', X],add,_) \ fact(['a1:Student', X],del,U) <=> true | fact(['a1:Student', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:undergraduateDegreeFrom', X, Y],add,_) \ fact(['a1:degreeFrom', X, Y],del,U) <=> true | fact(['a1:degreeFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:publicationAuthor', X, _],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:mastersDegreeFrom', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:College', X],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:teacherOf', X, _],add,_) \ fact(['a1:Faculty', X],del,U) <=> true | fact(['a1:Faculty', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:ResearchGroup', X],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:UnofficialPublication', X],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:researchProject', X, _],add,_) \ fact(['a1:ResearchGroup', X],del,U) <=> true | fact(['a1:ResearchGroup', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,_), fact(['a1:worksFor', X, X1],add,_), fact(['a1:Organization', X1],add,_) \ fact(['a1:Employee', X],del,U) <=> true | fact(['a1:Employee', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Chair', X],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:affiliateOf', X, _],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:GraduateCourse', X],add,_) \ fact(['a1:Course', X],del,U) <=> true | fact(['a1:Course', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,_), fact(['a1:takesCourse', X, X1],add,_), fact(['a1:Course', X1],add,_) \ fact(['a1:Student', X],del,U) <=> true | fact(['a1:Student', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:Dean', X],add,_) \ fact(['a1:Professor', X],del,U) <=> true | fact(['a1:Professor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:orgPublication', _, X1],add,_) \ fact(['a1:Publication', X1],del,U) <=> true | fact(['a1:Publication', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:Manual', X],add,_) \ fact(['a1:Publication', X],del,U) <=> true | fact(['a1:Publication', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:headOf', X, X1],add,_), fact(['a1:College', X1],add,_) \ fact(['a1:Dean', X],del,U) <=> true | fact(['a1:Dean', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:TeachingAssistant', X],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:subOrganizationOf', X, _],add,_) \ fact(['a1:Organization', X],del,U) <=> true | fact(['a1:Organization', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:connectedCourses', Y, X],add,_) \ fact(['a1:connectedCourses', X, Y],del,U) <=> true | fact(['a1:connectedCourses', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:Student', X],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:emailAddress', X, _],add,_) \ fact(['a1:Person', X],del,U) <=> true | fact(['a1:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:subOrganizationOf', X, Y],add,_), fact(['a1:subOrganizationOf', Y, Z],add,_) \ fact(['a1:subOrganizationOf', X, Z],del,U) <=> true | fact(['a1:subOrganizationOf', X, Z],add,U), applied_rules(1,red).

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
