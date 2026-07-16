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
phase(1), fact(['a1:colleagues', X, Y],O1,M1,_), fact(['a1:colleagues', Y, Z],O2,M2,_) \ fact(['a1:colleagues', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('a1:colleagues',O1,M1),('a1:colleagues',O2,M2)],M), fact(['a1:colleagues', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', _, X1],O1,M1,_) \ fact(['a1:University', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:title', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', Y, X],O1,M1,_) \ fact(['a1:degreeFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', Y, X],O1,M1,_) \ fact(['a1:hasAlumnus', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:hasAlumnus', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Faculty', X],O1,M1,_) \ fact(['a1:Employee', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Employee', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Professor', X],O1,M1,_) \ fact(['a1:Faculty', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:listedCourse', _, X1],O1,M1,_) \ fact(['a1:Course', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Course', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:AssociateProfessor', X],O1,M1,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:member', _, X1],O1,M1,_) \ fact(['a1:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:AssistantProfessor', X],O1,M1,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:orgPublication', X, _],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Chair', X],O1,M1,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:TechnicalReport', X],O1,M1,_) \ fact(['a1:Article', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Article', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:colleagues', Y, X],O1,M1,_) \ fact(['a1:colleagues', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:colleagues', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:headOf', X, Y],O1,M1,_) \ fact(['a1:worksFor', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:worksFor', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:age', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:degreeFrom', _, X1],O1,M1,_) \ fact(['a1:University', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Specification', X],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:SystemsStaff', X],O1,M1,_) \ fact(['a1:AdministrativeStaff', X],add,_,U) <=> member(del,[O1]) | fact(['a1:AdministrativeStaff', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', _, X1],O1,M1,_) \ fact(['a1:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:softwareDocumentation', _, X1],O1,M1,_) \ fact(['a1:Publication', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:PostDoc', X],O1,M1,_) \ fact(['a1:Faculty', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X0, X1],O1,M1,_), fact(['a1:connectedCourses', X1, X2],O2,M2,_), fact(['a1:teacherOf', X3, X2],O3,M3,_) \ fact(['a1:colleagues', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('a1:teacherOf',O1,M1),('a1:connectedCourses',O2,M2),('a1:teacherOf',O3,M3)],M), fact(['a1:colleagues', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:softwareVersion', X, _],O1,M1,_) \ fact(['a1:Software', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Software', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:ConferencePaper', X],O1,M1,_) \ fact(['a1:Article', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Article', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,M1,_), fact(['a1:teachingAssistantOf', X, X1],O2,M2,_), fact(['a1:Course', X1],O3,M3,_) \ fact(['a1:TeachingAssistant', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('a1:Person',O1,M1),('a1:teachingAssistantOf',O2,M2),('a1:Course',O3,M3)],M), fact(['a1:TeachingAssistant', X],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:affiliateOf', _, X1],O1,M1,_) \ fact(['a1:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,M1,_), fact(['a1:headOf', X, X1],O2,M2,_), fact(['a1:Department', X1],O3,M3,_) \ fact(['a1:Chair', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('a1:Person',O1,M1),('a1:headOf',O2,M2),('a1:Department',O3,M3)],M), fact(['a1:Chair', X],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:connectedCourses', X, Y],O1,M1,_), fact(['a1:connectedCourses', Y, Z],O2,M2,_) \ fact(['a1:connectedCourses', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('a1:connectedCourses',O1,M1),('a1:connectedCourses',O2,M2)],M), fact(['a1:connectedCourses', X, Z],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,M1,_), fact(['a1:headOf', X, X1],O2,M2,_), fact(['a1:Program', X1],O3,M3,_) \ fact(['a1:Director', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('a1:Person',O1,M1),('a1:headOf',O2,M2),('a1:Program',O3,M3)],M), fact(['a1:Director', X],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:member', Y, X],O1,M1,_) \ fact(['a1:memberOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:memberOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:memberOf', Y, X],O1,M1,_) \ fact(['a1:member', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:member', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:tenured', X, _],O1,M1,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:takesCourse', X1, X0],O1,M1,_), fact(['a1:takesCourse', X1, X2],O2,M2,_) \ fact(['a1:connectedCourses', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('a1:takesCourse',O1,M1),('a1:takesCourse',O2,M2)],M), fact(['a1:connectedCourses', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', _, X1],O1,M1,_) \ fact(['a1:Course', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Course', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:hasAlumnus', X, _],O1,M1,_) \ fact(['a1:University', X],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', X1, X0],O1,M1,_), fact(['a1:takesCourse', X1, X2],O2,M2,_) \ fact(['a1:advisor_takesCourse', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('a1:advisor',O1,M1),('a1:takesCourse',O2,M2)],M), fact(['a1:advisor_takesCourse', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:Research', X],O1,M1,_) \ fact(['a1:Work', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Work', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:telephone', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Institute', X],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', _, X1],O1,M1,_) \ fact(['a1:Organization', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:worksFor', X, Y],O1,M1,_) \ fact(['a1:memberOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:memberOf', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Employee', X],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:softwareDocumentation', X, _],O1,M1,_) \ fact(['a1:Software', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Software', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X0, X1],O1,M1,_), fact(['a1:takesCourse', X2, X1],O2,M2,_), fact(['a1:advisor', X2, X3],O3,M3,_) \ fact(['a1:colleagues', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('a1:teacherOf',O1,M1),('a1:takesCourse',O2,M2),('a1:advisor',O3,M3)],M), fact(['a1:colleagues', X0, X3],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:member', X, _],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Department', X],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Article', X],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Lecturer', X],O1,M1,_) \ fact(['a1:Faculty', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:publicationAuthor', _, X1],O1,M1,_) \ fact(['a1:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:researchProject', _, X1],O1,M1,_) \ fact(['a1:Research', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Research', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Software', X],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:advisor_takesCourse', X0, X1],O1,M1,_), fact(['a1:advisor_takesCourse', X2, X1],O2,M2,_) \ fact(['a1:colleagues', X0, X2],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('a1:advisor_takesCourse',O1,M1),('a1:advisor_takesCourse',O2,M2)],M), fact(['a1:colleagues', X0, X2],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:Program', X],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:AdministrativeStaff', X],O1,M1,_) \ fact(['a1:Employee', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Employee', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:advisor', _, X1],O1,M1,_) \ fact(['a1:Professor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Course', X],O1,M1,_) \ fact(['a1:Work', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Work', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Book', X],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:FullProfessor', X],O1,M1,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:publicationResearch', X, _],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', X, Y],O1,M1,_) \ fact(['a1:degreeFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:ClericalStaff', X],O1,M1,_) \ fact(['a1:AdministrativeStaff', X],add,_,U) <=> member(del,[O1]) | fact(['a1:AdministrativeStaff', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:affiliatedOrganizationOf', X, _],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:teachingAssistantOf', X, _],O1,M1,_) \ fact(['a1:TeachingAssistant', X],add,_,U) <=> member(del,[O1]) | fact(['a1:TeachingAssistant', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:VisitingProfessor', X],O1,M1,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:University', X],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:JournalArticle', X],O1,M1,_) \ fact(['a1:Article', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Article', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:publicationResearch', _, X1],O1,M1,_) \ fact(['a1:Research', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Research', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Director', X],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:publicationDate', X, _],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:affiliatedOrganizationOf', _, X1],O1,M1,_) \ fact(['a1:Organization', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:doctoralDegreeFrom', _, X1],O1,M1,_) \ fact(['a1:University', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', _, X1],O1,M1,_) \ fact(['a1:University', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:University', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:teachingAssistantOf', _, X1],O1,M1,_) \ fact(['a1:Course', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Course', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', X, Y],O1,M1,_) \ fact(['a1:degreeFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:listedCourse', X, _],O1,M1,_) \ fact(['a1:Schedule', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Schedule', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:GraduateStudent', X],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:ResearchAssistant', X],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:UndergraduateStudent', X],O1,M1,_) \ fact(['a1:Student', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Student', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:undergraduateDegreeFrom', X, Y],O1,M1,_) \ fact(['a1:degreeFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:degreeFrom', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:publicationAuthor', X, _],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:mastersDegreeFrom', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:College', X],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:teacherOf', X, _],O1,M1,_) \ fact(['a1:Faculty', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Faculty', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:ResearchGroup', X],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:UnofficialPublication', X],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:researchProject', X, _],O1,M1,_) \ fact(['a1:ResearchGroup', X],add,_,U) <=> member(del,[O1]) | fact(['a1:ResearchGroup', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,M1,_), fact(['a1:worksFor', X, X1],O2,M2,_), fact(['a1:Organization', X1],O3,M3,_) \ fact(['a1:Employee', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('a1:Person',O1,M1),('a1:worksFor',O2,M2),('a1:Organization',O3,M3)],M), fact(['a1:Employee', X],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:Chair', X],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:affiliateOf', X, _],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:GraduateCourse', X],O1,M1,_) \ fact(['a1:Course', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Course', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Person', X],O1,M1,_), fact(['a1:takesCourse', X, X1],O2,M2,_), fact(['a1:Course', X1],O3,M3,_) \ fact(['a1:Student', X],add,_,U) <=> member(del,[O1,O2,O3]) | check_pos_mark([('a1:Person',O1,M1),('a1:takesCourse',O2,M2),('a1:Course',O3,M3)],M), fact(['a1:Student', X],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:Dean', X],O1,M1,_) \ fact(['a1:Professor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Professor', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:orgPublication', _, X1],O1,M1,_) \ fact(['a1:Publication', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X1],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Manual', X],O1,M1,_) \ fact(['a1:Publication', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Publication', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:headOf', X, X1],O1,M1,_), fact(['a1:College', X1],O2,M2,_) \ fact(['a1:Dean', X],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('a1:headOf',O1,M1),('a1:College',O2,M2)],M), fact(['a1:Dean', X],del,M,U), applied_rules(1,del).
phase(1), fact(['a1:TeachingAssistant', X],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', X, _],O1,M1,_) \ fact(['a1:Organization', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Organization', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:connectedCourses', Y, X],O1,M1,_) \ fact(['a1:connectedCourses', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:connectedCourses', X, Y],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:Student', X],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:emailAddress', X, _],O1,M1,_) \ fact(['a1:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:Person', X],del,M1,U), applied_rules(1,del).
phase(1), fact(['a1:subOrganizationOf', X, Y],O1,M1,_), fact(['a1:subOrganizationOf', Y, Z],O2,M2,_) \ fact(['a1:subOrganizationOf', X, Z],add,_,U) <=> member(del,[O1,O2]) | check_pos_mark([('a1:subOrganizationOf',O1,M1),('a1:subOrganizationOf',O2,M2)],M), fact(['a1:subOrganizationOf', X, Z],del,M,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact(['a1:colleagues', X, Y],add,M1,_), fact(['a1:colleagues', Y, Z],add,M2,_) \ fact(['a1:colleagues', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['a1:colleagues', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:mastersDegreeFrom', _, X1],add,M1,_) \ fact(['a1:University', X1],del,_,U) <=> true | fact(['a1:University', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:title', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:hasAlumnus', Y, X],add,M1,_) \ fact(['a1:degreeFrom', X, Y],del,_,U) <=> true | fact(['a1:degreeFrom', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:degreeFrom', Y, X],add,M1,_) \ fact(['a1:hasAlumnus', X, Y],del,_,U) <=> true | fact(['a1:hasAlumnus', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Faculty', X],add,M1,_) \ fact(['a1:Employee', X],del,_,U) <=> true | fact(['a1:Employee', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Professor', X],add,M1,_) \ fact(['a1:Faculty', X],del,_,U) <=> true | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:listedCourse', _, X1],add,M1,_) \ fact(['a1:Course', X1],del,_,U) <=> true | fact(['a1:Course', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:AssociateProfessor', X],add,M1,_) \ fact(['a1:Professor', X],del,_,U) <=> true | fact(['a1:Professor', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:member', _, X1],add,M1,_) \ fact(['a1:Person', X1],del,_,U) <=> true | fact(['a1:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:AssistantProfessor', X],add,M1,_) \ fact(['a1:Professor', X],del,_,U) <=> true | fact(['a1:Professor', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:orgPublication', X, _],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Chair', X],add,M1,_) \ fact(['a1:Professor', X],del,_,U) <=> true | fact(['a1:Professor', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:TechnicalReport', X],add,M1,_) \ fact(['a1:Article', X],del,_,U) <=> true | fact(['a1:Article', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:colleagues', Y, X],add,M1,_) \ fact(['a1:colleagues', X, Y],del,_,U) <=> true | fact(['a1:colleagues', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:headOf', X, Y],add,M1,_) \ fact(['a1:worksFor', X, Y],del,_,U) <=> true | fact(['a1:worksFor', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:age', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:degreeFrom', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:degreeFrom', _, X1],add,M1,_) \ fact(['a1:University', X1],del,_,U) <=> true | fact(['a1:University', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Specification', X],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:SystemsStaff', X],add,M1,_) \ fact(['a1:AdministrativeStaff', X],del,_,U) <=> true | fact(['a1:AdministrativeStaff', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:hasAlumnus', _, X1],add,M1,_) \ fact(['a1:Person', X1],del,_,U) <=> true | fact(['a1:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:softwareDocumentation', _, X1],add,M1,_) \ fact(['a1:Publication', X1],del,_,U) <=> true | fact(['a1:Publication', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:PostDoc', X],add,M1,_) \ fact(['a1:Faculty', X],del,_,U) <=> true | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:teacherOf', X0, X1],add,M1,_), fact(['a1:connectedCourses', X1, X2],add,M2,_), fact(['a1:teacherOf', X3, X2],add,M3,_) \ fact(['a1:colleagues', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['a1:colleagues', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:softwareVersion', X, _],add,M1,_) \ fact(['a1:Software', X],del,_,U) <=> true | fact(['a1:Software', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:ConferencePaper', X],add,M1,_) \ fact(['a1:Article', X],del,_,U) <=> true | fact(['a1:Article', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,M1,_), fact(['a1:teachingAssistantOf', X, X1],add,M2,_), fact(['a1:Course', X1],add,M3,_) \ fact(['a1:TeachingAssistant', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['a1:TeachingAssistant', X],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:affiliateOf', _, X1],add,M1,_) \ fact(['a1:Person', X1],del,_,U) <=> true | fact(['a1:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,M1,_), fact(['a1:headOf', X, X1],add,M2,_), fact(['a1:Department', X1],add,M3,_) \ fact(['a1:Chair', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['a1:Chair', X],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:connectedCourses', X, Y],add,M1,_), fact(['a1:connectedCourses', Y, Z],add,M2,_) \ fact(['a1:connectedCourses', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['a1:connectedCourses', X, Z],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,M1,_), fact(['a1:headOf', X, X1],add,M2,_), fact(['a1:Program', X1],add,M3,_) \ fact(['a1:Director', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['a1:Director', X],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:member', Y, X],add,M1,_) \ fact(['a1:memberOf', X, Y],del,_,U) <=> true | fact(['a1:memberOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:memberOf', Y, X],add,M1,_) \ fact(['a1:member', X, Y],del,_,U) <=> true | fact(['a1:member', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:tenured', X, _],add,M1,_) \ fact(['a1:Professor', X],del,_,U) <=> true | fact(['a1:Professor', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:takesCourse', X1, X0],add,M1,_), fact(['a1:takesCourse', X1, X2],add,M2,_) \ fact(['a1:connectedCourses', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['a1:connectedCourses', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:teacherOf', _, X1],add,M1,_) \ fact(['a1:Course', X1],del,_,U) <=> true | fact(['a1:Course', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:hasAlumnus', X, _],add,M1,_) \ fact(['a1:University', X],del,_,U) <=> true | fact(['a1:University', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:advisor', X1, X0],add,M1,_), fact(['a1:takesCourse', X1, X2],add,M2,_) \ fact(['a1:advisor_takesCourse', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['a1:advisor_takesCourse', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:Research', X],add,M1,_) \ fact(['a1:Work', X],del,_,U) <=> true | fact(['a1:Work', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:telephone', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Institute', X],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:subOrganizationOf', _, X1],add,M1,_) \ fact(['a1:Organization', X1],del,_,U) <=> true | fact(['a1:Organization', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:worksFor', X, Y],add,M1,_) \ fact(['a1:memberOf', X, Y],del,_,U) <=> true | fact(['a1:memberOf', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Employee', X],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:softwareDocumentation', X, _],add,M1,_) \ fact(['a1:Software', X],del,_,U) <=> true | fact(['a1:Software', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:advisor', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:teacherOf', X0, X1],add,M1,_), fact(['a1:takesCourse', X2, X1],add,M2,_), fact(['a1:advisor', X2, X3],add,M3,_) \ fact(['a1:colleagues', X0, X3],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['a1:colleagues', X0, X3],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:member', X, _],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Department', X],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Article', X],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Lecturer', X],add,M1,_) \ fact(['a1:Faculty', X],del,_,U) <=> true | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:publicationAuthor', _, X1],add,M1,_) \ fact(['a1:Person', X1],del,_,U) <=> true | fact(['a1:Person', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:researchProject', _, X1],add,M1,_) \ fact(['a1:Research', X1],del,_,U) <=> true | fact(['a1:Research', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Software', X],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:advisor_takesCourse', X0, X1],add,M1,_), fact(['a1:advisor_takesCourse', X2, X1],add,M2,_) \ fact(['a1:colleagues', X0, X2],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['a1:colleagues', X0, X2],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:Program', X],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:AdministrativeStaff', X],add,M1,_) \ fact(['a1:Employee', X],del,_,U) <=> true | fact(['a1:Employee', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:advisor', _, X1],add,M1,_) \ fact(['a1:Professor', X1],del,_,U) <=> true | fact(['a1:Professor', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Course', X],add,M1,_) \ fact(['a1:Work', X],del,_,U) <=> true | fact(['a1:Work', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Book', X],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:FullProfessor', X],add,M1,_) \ fact(['a1:Professor', X],del,_,U) <=> true | fact(['a1:Professor', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:publicationResearch', X, _],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:doctoralDegreeFrom', X, Y],add,M1,_) \ fact(['a1:degreeFrom', X, Y],del,_,U) <=> true | fact(['a1:degreeFrom', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:ClericalStaff', X],add,M1,_) \ fact(['a1:AdministrativeStaff', X],del,_,U) <=> true | fact(['a1:AdministrativeStaff', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:affiliatedOrganizationOf', X, _],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:teachingAssistantOf', X, _],add,M1,_) \ fact(['a1:TeachingAssistant', X],del,_,U) <=> true | fact(['a1:TeachingAssistant', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:VisitingProfessor', X],add,M1,_) \ fact(['a1:Professor', X],del,_,U) <=> true | fact(['a1:Professor', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:undergraduateDegreeFrom', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:University', X],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:JournalArticle', X],add,M1,_) \ fact(['a1:Article', X],del,_,U) <=> true | fact(['a1:Article', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:publicationResearch', _, X1],add,M1,_) \ fact(['a1:Research', X1],del,_,U) <=> true | fact(['a1:Research', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Director', X],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:doctoralDegreeFrom', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:publicationDate', X, _],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:affiliatedOrganizationOf', _, X1],add,M1,_) \ fact(['a1:Organization', X1],del,_,U) <=> true | fact(['a1:Organization', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:doctoralDegreeFrom', _, X1],add,M1,_) \ fact(['a1:University', X1],del,_,U) <=> true | fact(['a1:University', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:undergraduateDegreeFrom', _, X1],add,M1,_) \ fact(['a1:University', X1],del,_,U) <=> true | fact(['a1:University', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:teachingAssistantOf', _, X1],add,M1,_) \ fact(['a1:Course', X1],del,_,U) <=> true | fact(['a1:Course', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:mastersDegreeFrom', X, Y],add,M1,_) \ fact(['a1:degreeFrom', X, Y],del,_,U) <=> true | fact(['a1:degreeFrom', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:listedCourse', X, _],add,M1,_) \ fact(['a1:Schedule', X],del,_,U) <=> true | fact(['a1:Schedule', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:GraduateStudent', X],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:ResearchAssistant', X],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:UndergraduateStudent', X],add,M1,_) \ fact(['a1:Student', X],del,_,U) <=> true | fact(['a1:Student', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:undergraduateDegreeFrom', X, Y],add,M1,_) \ fact(['a1:degreeFrom', X, Y],del,_,U) <=> true | fact(['a1:degreeFrom', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:publicationAuthor', X, _],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:mastersDegreeFrom', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:College', X],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:teacherOf', X, _],add,M1,_) \ fact(['a1:Faculty', X],del,_,U) <=> true | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:ResearchGroup', X],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:UnofficialPublication', X],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:researchProject', X, _],add,M1,_) \ fact(['a1:ResearchGroup', X],del,_,U) <=> true | fact(['a1:ResearchGroup', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,M1,_), fact(['a1:worksFor', X, X1],add,M2,_), fact(['a1:Organization', X1],add,M3,_) \ fact(['a1:Employee', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['a1:Employee', X],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:Chair', X],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:affiliateOf', X, _],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:GraduateCourse', X],add,M1,_) \ fact(['a1:Course', X],del,_,U) <=> true | fact(['a1:Course', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Person', X],add,M1,_), fact(['a1:takesCourse', X, X1],add,M2,_), fact(['a1:Course', X1],add,M3,_) \ fact(['a1:Student', X],del,_,U) <=> true | check_neg_mark([M1,M2,M3],M), fact(['a1:Student', X],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:Dean', X],add,M1,_) \ fact(['a1:Professor', X],del,_,U) <=> true | fact(['a1:Professor', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:orgPublication', _, X1],add,M1,_) \ fact(['a1:Publication', X1],del,_,U) <=> true | fact(['a1:Publication', X1],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Manual', X],add,M1,_) \ fact(['a1:Publication', X],del,_,U) <=> true | fact(['a1:Publication', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:headOf', X, X1],add,M1,_), fact(['a1:College', X1],add,M2,_) \ fact(['a1:Dean', X],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['a1:Dean', X],add,M,U), applied_rules(1,red).
phase(2), fact(['a1:TeachingAssistant', X],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:subOrganizationOf', X, _],add,M1,_) \ fact(['a1:Organization', X],del,_,U) <=> true | fact(['a1:Organization', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:connectedCourses', Y, X],add,M1,_) \ fact(['a1:connectedCourses', X, Y],del,_,U) <=> true | fact(['a1:connectedCourses', X, Y],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:Student', X],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:emailAddress', X, _],add,M1,_) \ fact(['a1:Person', X],del,_,U) <=> true | fact(['a1:Person', X],add,M1,U), applied_rules(1,red).
phase(2), fact(['a1:subOrganizationOf', X, Y],add,M1,_), fact(['a1:subOrganizationOf', Y, Z],add,M2,_) \ fact(['a1:subOrganizationOf', X, Z],del,_,U) <=> true | check_neg_mark([M1,M2],M), fact(['a1:subOrganizationOf', X, Z],add,M,U), applied_rules(1,red).

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
phase(5), fact(['a1:colleagues', X, Y],add,M1,U1), fact(['a1:colleagues', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['a1:colleagues', X, Z],add,M,U), applied_rules(1,ins).
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
phase(5), fact(['a1:teacherOf', X0, X1],add,M1,U1), fact(['a1:connectedCourses', X1, X2],add,M2,U2), fact(['a1:teacherOf', X3, X2],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['a1:colleagues', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:softwareVersion', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Software', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:ConferencePaper', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Article', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:teachingAssistantOf', X, X1],add,M2,U2), fact(['a1:Course', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['a1:TeachingAssistant', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliateOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:headOf', X, X1],add,M2,U2), fact(['a1:Department', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['a1:Chair', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:connectedCourses', X, Y],add,M1,U1), fact(['a1:connectedCourses', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['a1:connectedCourses', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:headOf', X, X1],add,M2,U2), fact(['a1:Program', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['a1:Director', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:member', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:memberOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:memberOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:member', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:tenured', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:takesCourse', X1, X0],add,M1,U1), fact(['a1:takesCourse', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['a1:connectedCourses', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Course', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:hasAlumnus', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:University', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor', X1, X0],add,M1,U1), fact(['a1:takesCourse', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['a1:advisor_takesCourse', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Research', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Work', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:telephone', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Institute', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:worksFor', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:memberOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Employee', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:softwareDocumentation', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Software', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:teacherOf', X0, X1],add,M1,U1), fact(['a1:takesCourse', X2, X1],add,M2,U2), fact(['a1:advisor', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['a1:colleagues', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:member', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Department', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Article', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Lecturer', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Faculty', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:publicationAuthor', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:researchProject', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Research', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Software', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:advisor_takesCourse', X0, X1],add,M1,U1), fact(['a1:advisor_takesCourse', X2, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['a1:colleagues', X0, X2],add,M,U), applied_rules(1,ins).
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
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:worksFor', X, X1],add,M2,U2), fact(['a1:Organization', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['a1:Employee', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Chair', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:affiliateOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:GraduateCourse', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Course', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Person', X],add,M1,U1), fact(['a1:takesCourse', X, X1],add,M2,U2), fact(['a1:Course', X1],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([M1,M2,M3],M), fact(['a1:Student', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:Dean', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Professor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:orgPublication', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Manual', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Publication', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:headOf', X, X1],add,M1,U1), fact(['a1:College', X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['a1:Dean', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:TeachingAssistant', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Organization', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:connectedCourses', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:connectedCourses', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:Student', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:emailAddress', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:subOrganizationOf', X, Y],add,M1,U1), fact(['a1:subOrganizationOf', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact(['a1:subOrganizationOf', X, Z],add,M,U), applied_rules(1,ins).

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
