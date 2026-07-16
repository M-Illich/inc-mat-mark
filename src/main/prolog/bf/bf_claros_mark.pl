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
phase(1), fact(['a1:P22i_acquired_title_through', _, X1],O1,_,_) \ fact(['a1:E8_Acquisition', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P24_transferred_title_of', X, _],O1,_,_) \ fact(['a1:E8_Acquisition', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P110i_was_augmented_by', _, X1],O1,_,_) \ fact(['a1:E79_Part_Addition', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E79_Part_Addition', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', X, X2],O1,_,_), fact(['a1:P41_classified', X, X1],O2,_,_), fact(['a1:E17_Type_Assignment', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P33_used_specific_technique', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P116_starts', X, Y],O1,_,_), fact(['a1:P116_starts', Y, Z],O2,_,_) \ fact(['a1:P116_starts', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P116_starts', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P124i_was_transformed_by', _, X1],O1,_,_) \ fact(['a1:E81_Transformation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E81_Transformation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P104_is_subject_to', X, _],O1,_,_) \ fact(['a1:E72_Legal_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P114_is_equal_in_time_to', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P127_has_broader_term', Y, X],O1,_,_) \ fact(['a1:P127i_has_narrower_term', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P127i_has_narrower_term', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P127i_has_narrower_term', Y, X],O1,_,_) \ fact(['a1:P127_has_broader_term', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P127_has_broader_term', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:followingEvent', X, Y],O1,_,_), fact(['a2:followingEvent', Y, Z],O2,_,_) \ fact(['a2:followingEvent', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a2:followingEvent', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E34_Inscription', X],O1,_,_) \ fact(['a1:E37_Mark', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E37_Mark', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P94i_was_created_by', _, X1],O1,_,_) \ fact(['a1:E65_Creation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E65_Creation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:aimChatID', _, X1],O1,_,_) \ fact(['rdfs:Literal', X1],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E7_Activity', X],O1,_,_) \ fact(['a1:E5_Event', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:depiction', _, X1],O1,_,_) \ fact(['a3:Image', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Image', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P23_transferred_title_from', X, _],O1,_,_) \ fact(['a1:E8_Acquisition', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Murder', X],O1,_,_) \ fact(['a2:Death', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Death', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E14_Condition_Assessment', X],O1,_,_) \ fact(['a1:E13_Attribute_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', X, Y],O1,_,_) \ fact(['a1:P31_has_modified', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', X, Y],O1,_,_) \ fact(['a1:P15i_influenced', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P123i_resulted_from', _, X1],O1,_,_) \ fact(['a1:E81_Transformation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E81_Transformation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:homepage', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P96_by_mother', Y, X],O1,_,_) \ fact(['a1:P96i_gave_birth', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P96i_gave_birth', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P96i_gave_birth', Y, X],O1,_,_) \ fact(['a1:P96_by_mother', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P96_by_mother', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P100_was_death_of', X, _],O1,_,_) \ fact(['a1:E69_Death', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E69_Death', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41i_was_classified_by', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P71i_is_listed_in', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41i_was_classified_by', Y, X],O1,_,_) \ fact(['a1:P41_classified', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P41_classified', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', Y, X],O1,_,_) \ fact(['a1:P41i_was_classified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P41i_was_classified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P14_carried_out_by', X, Y],O1,_,_) \ fact(['a1:P11_had_participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P93_took_out_of_existence', X, Y],O1,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P54_has_current_permanent_location', X, X2],O1,_,_), fact(['a1:P54_has_current_permanent_location', X, X1],O2,_,_), fact(['a1:E19_Physical_Object', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P146_separated_from', X, Y],O1,_,_) \ fact(['a1:P11_had_participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P17_was_motivated_by', Y, X],O1,_,_) \ fact(['a1:P17i_motivated', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P17i_motivated', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P17i_motivated', Y, X],O1,_,_) \ fact(['a1:P17_was_motivated_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P17_was_motivated_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39i_was_measured_by', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P113_removed', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73_has_translation', Y, X],O1,_,_) \ fact(['a1:P73i_is_translation_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P73i_is_translation_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', Y, X],O1,_,_) \ fact(['a1:P73_has_translation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P73_has_translation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P2i_is_type_of', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P141i_was_assigned_by', _, X1],O1,_,_) \ fact(['a1:E13_Attribute_Assignment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P102_has_title', X, Y],O1,_,_) \ fact(['a1:P1_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P38_deassigned', _, X1],O1,_,_) \ fact(['a1:E42_Identifier', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P54_has_current_permanent_location', Y, X],O1,_,_) \ fact(['a1:P54i_is_current_permanent_location_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P54i_is_current_permanent_location_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P54i_is_current_permanent_location_of', Y, X],O1,_,_) \ fact(['a1:P54_has_current_permanent_location', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P54_has_current_permanent_location', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E21_Person', X],O1,_,_) \ fact(['a1:E20_Biological_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E20_Biological_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['rdfs:Container', X],O1,_,_) \ fact(['rdfs:Resource', X],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Resource', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:publications', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:relatedInformationObjects', Y, X],O1,_,_) \ fact(['a1:relatedInformationObjects', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:relatedInformationObjects', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P126_employed', X, _],O1,_,_) \ fact(['a1:E11_Modification', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:death', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Divorce', X],O1,_,_) \ fact(['a2:GroupEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:GroupEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', X, _],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P136_was_based_on', X, _],O1,_,_) \ fact(['a1:E83_Type_Creation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E83_Type_Creation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Graduation', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P29i_received_custody_through', Y, X],O1,_,_) \ fact(['a1:P29_custody_received_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P29_custody_received_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P29_custody_received_by', Y, X],O1,_,_) \ fact(['a1:P29i_received_custody_through', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P29i_received_custody_through', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P10_falls_within', Y, X],O1,_,_) \ fact(['a1:P10i_contains', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P10i_contains', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P10i_contains', Y, X],O1,_,_) \ fact(['a1:P10_falls_within', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P10_falls_within', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P142_used_constituent', X, Y],O1,_,_) \ fact(['a1:P16_used_specific_object', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P147i_was_curated_by', X, _],O1,_,_) \ fact(['a1:E78_Collection', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E78_Collection', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E53_Place', X],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P72i_is_language_of', _, X1],O1,_,_) \ fact(['a1:E33_Linguistic_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P70_documents', X, Y],O1,_,_) \ fact(['a1:P67_refers_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P124_transformed', X, Y],O1,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Person', X],O1,_,_) \ fact(['a4:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a4:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E24_Physical_Man-Made_Thing', X],O1,_,_) \ fact(['a1:E71_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P148i_is_component_of', Y, X],O1,_,_) \ fact(['a1:P148_has_component', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P148_has_component', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P148_has_component', Y, X],O1,_,_) \ fact(['a1:P148i_is_component_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P148i_is_component_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P15_was_influenced_by', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P107_has_current_or_former_member', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:made', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P30_transferred_custody_of', Y, X],O1,_,_) \ fact(['a1:P30i_custody_transferred_through', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P30i_custody_transferred_through', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P30i_custody_transferred_through', Y, X],O1,_,_) \ fact(['a1:P30_transferred_custody_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P30_transferred_custody_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P125_used_object_of_type', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:birth', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E65_Creation', X],O1,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E81_Transformation', X],O1,_,_) \ fact(['a1:E64_End_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P24i_changed_ownership_through', Y, X],O1,_,_) \ fact(['a1:P24_transferred_title_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P24_transferred_title_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P24_transferred_title_of', Y, X],O1,_,_) \ fact(['a1:P24i_changed_ownership_through', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P24i_changed_ownership_through', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Annulment', X],O1,_,_) \ fact(['a2:GroupEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:GroupEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Promotion', X],O1,_,_) \ fact(['a2:PositionChange', X],add,_,U) <=> member(del,[O1]) | fact(['a2:PositionChange', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P31_has_modified', X, Y],O1,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Ordination', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P130_shows_features_of', _, X1],O1,_,_) \ fact(['a1:E70_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P118_overlaps_in_time_with', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P144i_gained_member_by', _, X1],O1,_,_) \ fact(['a1:E85_Joining', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E85_Joining', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P124i_was_transformed_by', X, Y],O1,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P15_was_influenced_by', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E79_Part_Addition', X],O1,_,_), fact(['a1:E80_Part_Removal', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135_created_type', X, Y],O1,_,_) \ fact(['a1:P94_has_created', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P94_has_created', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P7_took_place_at', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:Jurisdiction', X],O1,_,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],add,_,U) <=> member(del,[O1]) | fact(['a5:LocationPeriodOrJurisdiction', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P56i_is_found_on', X, _],O1,_,_) \ fact(['a1:E26_Physical_Feature', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E26_Physical_Feature', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P1_is_identified_by', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P126i_was_employed_in', Y, X],O1,_,_) \ fact(['a1:P126_employed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P126_employed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P126_employed', Y, X],O1,_,_) \ fact(['a1:P126i_was_employed_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P126i_was_employed_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:principal', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:myersBriggs', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Demotion', X],O1,_,_) \ fact(['a2:PositionChange', X],add,_,U) <=> member(del,[O1]) | fact(['a2:PositionChange', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:relationship', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P112_diminished', Y, X],O1,_,_) \ fact(['a1:P112i_was_diminished_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P112i_was_diminished_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P112i_was_diminished_by', Y, X],O1,_,_) \ fact(['a1:P112_diminished', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P112_diminished', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:openid', X, Y],O1,_,_) \ fact(['a3:isPrimaryTopicOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:isPrimaryTopicOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P141_assigned', Y, X],O1,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P141i_was_assigned_by', Y, X],O1,_,_) \ fact(['a1:P141_assigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P44_has_condition', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P45_consists_of', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P50i_is_current_keeper_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P26_moved_to', Y, X],O1,_,_) \ fact(['a1:P26i_was_destination_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P26i_was_destination_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P26i_was_destination_of', Y, X],O1,_,_) \ fact(['a1:P26_moved_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P26_moved_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:img', X, Y],O1,_,_) \ fact(['a3:depiction', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:depiction', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P24_transferred_title_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P133_is_separated_from', X, _],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P94_has_created', Y, X],O1,_,_) \ fact(['a1:P94i_was_created_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P94i_was_created_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P94i_was_created_by', Y, X],O1,_,_) \ fact(['a1:P94_has_created', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P94_has_created', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67i_is_referred_to_by', _, X1],O1,_,_) \ fact(['a1:E89_Propositional_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P9_consists_of', Y, X],O1,_,_) \ fact(['a1:P9i_forms_part_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P9i_forms_part_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P9i_forms_part_of', Y, X],O1,_,_) \ fact(['a1:P9_consists_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P9_consists_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P51_has_former_or_current_owner', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P68i_use_foreseen_by', X, _],O1,_,_) \ fact(['a1:E57_Material', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:IndividualEvent', X],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P138i_has_representation', Y, X],O1,_,_) \ fact(['a1:P138_represents', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P138_represents', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P138_represents', Y, X],O1,_,_) \ fact(['a1:P138i_has_representation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P138i_has_representation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P51_has_former_or_current_owner', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Organization', X],O1,_,_), fact(['a3:Person', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:state', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, Y],O1,_,_) \ fact(['a6:childOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a6:childOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55i_currently_holds', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P19_was_intended_use_of', _, X1],O1,_,_) \ fact(['a1:E71_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E47_Spatial_Coordinates', X],O1,_,_) \ fact(['a1:E44_Place_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:workInfoHomepage', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:depicts', Y, X],O1,_,_) \ fact(['a3:depiction', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:depiction', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:depiction', Y, X],O1,_,_) \ fact(['a3:depicts', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:depicts', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['rdfs:Literal', X],O1,_,_) \ fact(['rdfs:Resource', X],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Resource', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P52_has_current_owner', X, Y],O1,_,_) \ fact(['a1:P105_right_held_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P105_right_held_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:concurrentEvent', _, X1],O1,_,_) \ fact(['a2:Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P58_has_section_definition', _, X1],O1,_,_) \ fact(['a1:E46_Section_Definition', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E46_Section_Definition', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', X, _],O1,_,_) \ fact(['a1:E21_Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:surname', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P56i_is_found_on', _, X1],O1,_,_) \ fact(['a1:E19_Physical_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P144_joined_with', X, _],O1,_,_) \ fact(['a1:E85_Joining', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E85_Joining', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P130i_features_are_also_found_on', X, _],O1,_,_) \ fact(['a1:E70_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:event', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P43_has_dimension', X, _],O1,_,_) \ fact(['a1:E70_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P56_bears_feature', Y, X],O1,_,_) \ fact(['a1:P56i_is_found_on', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P56i_is_found_on', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P56i_is_found_on', Y, X],O1,_,_) \ fact(['a1:P56_bears_feature', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P56_bears_feature', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P83_had_at_least_duration', X, X2],O1,_,_), fact(['a1:P83_had_at_least_duration', X, X1],O2,_,_), fact(['a1:E52_Time-Span', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:participant', X, _],O1,_,_) \ fact(['a2:Relationship', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Relationship', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P140_assigned_attribute_to', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P4_has_time-span', _, X1],O1,_,_) \ fact(['a1:E52_Time-Span', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13_destroyed', Y, X],O1,_,_) \ fact(['a1:P13i_was_destroyed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P13i_was_destroyed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', Y, X],O1,_,_) \ fact(['a1:P13_destroyed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P13_destroyed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P107i_is_current_or_former_member_of', _, X1],O1,_,_) \ fact(['a1:E74_Group', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E12_Production', X],O1,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:employer', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E15_Identifier_Assignment', X],O1,_,_) \ fact(['a1:E13_Attribute_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P117_occurs_during', X, Y],O1,_,_), fact(['a1:P117_occurs_during', Y, Z],O2,_,_) \ fact(['a1:P117_occurs_during', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P117_occurs_during', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E63_Beginning_of_Existence', X],O1,_,_) \ fact(['a1:E5_Event', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P117i_includes', Y, X],O1,_,_) \ fact(['a1:P117_occurs_during', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P117_occurs_during', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P117_occurs_during', Y, X],O1,_,_) \ fact(['a1:P117i_includes', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P117i_includes', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P10i_contains', X, _],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P120i_occurs_after', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P28_custody_surrendered_by', X, Y],O1,_,_) \ fact(['a1:P14_carried_out_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P84i_was_maximum_duration_of', _, X1],O1,_,_) \ fact(['a1:E52_Time-Span', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P37i_was_assigned_by', _, X1],O1,_,_) \ fact(['a1:E15_Identifier_Assignment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', X, X2],O1,_,_), fact(['a1:P39_measured', X, X1],O2,_,_), fact(['a1:E16_Measurement', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P147_curated', _, X1],O1,_,_) \ fact(['a1:E78_Collection', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E78_Collection', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', _, X1],O1,_,_) \ fact(['a1:E68_Dissolution', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E68_Dissolution', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P65i_is_shown_by', Y, X],O1,_,_) \ fact(['a1:P65_shows_visual_item', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P65_shows_visual_item', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P65_shows_visual_item', Y, X],O1,_,_) \ fact(['a1:P65i_is_shown_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P65i_is_shown_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P56_bears_feature', X, _],O1,_,_) \ fact(['a1:E19_Physical_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E90_Symbolic_Object', X],O1,_,_) \ fact(['a1:E72_Legal_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P120_occurs_before', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E24_Physical_Man-Made_Thing', X],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E85_Joining', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P58_has_section_definition', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P146i_lost_member_by', _, X1],O1,_,_) \ fact(['a1:E86_Leaving', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E86_Leaving', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P8i_witnessed', _, X1],O1,_,_) \ fact(['a1:E4_Period', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P37_assigned', X, _],O1,_,_) \ fact(['a1:E15_Identifier_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P118_overlaps_in_time_with', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E4_Period', X],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Event', X],O1,_,_) \ fact(['a7:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a7:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:officiator', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P62i_is_depicted_by', _, X1],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P72_has_language', _, X1],O1,_,_) \ fact(['a1:E56_Language', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E56_Language', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P138_represents', X, Y],O1,_,_) \ fact(['a1:P67_refers_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P70i_is_documented_in', _, X1],O1,_,_) \ fact(['a1:E31_Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E31_Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P32_used_general_technique', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:aimChatID', X, Y],O1,_,_) \ fact(['a3:nick', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P105i_has_right_on', _, X1],O1,_,_) \ fact(['a1:E72_Legal_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:age', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P100_was_death_of', Y, X],O1,_,_) \ fact(['a1:P100i_died_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P100i_died_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P100i_died_in', Y, X],O1,_,_) \ fact(['a1:P100_was_death_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P100_was_death_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:skypeID', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:participant', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P11_had_participant', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:father', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P82_at_some_time_within', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P31i_was_modified_by', _, X1],O1,_,_) \ fact(['a1:E11_Modification', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:gender', X, Y1],O1,_,_), fact(['a3:gender', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:relatedPlaces', X, Y],O1,_,_), fact(['a1:relatedPlaces', Y, Z],O2,_,_) \ fact(['a1:relatedPlaces', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:relatedPlaces', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P141_assigned', X, _],O1,_,_) \ fact(['a1:E13_Attribute_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Document', X],O1,_,_), fact(['a3:Organization', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P72_has_language', X, _],O1,_,_) \ fact(['a1:E33_Linguistic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P105i_has_right_on', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P97_from_father', X, _],O1,_,_) \ fact(['a1:E67_Birth', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P110i_was_augmented_by', X, _],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P136_was_based_on', Y, X],O1,_,_) \ fact(['a1:P136i_supported_type_creation', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P136i_supported_type_creation', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P136i_supported_type_creation', Y, X],O1,_,_) \ fact(['a1:P136_was_based_on', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P136_was_based_on', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P22i_acquired_title_through', Y1, X],O1,_,_), fact(['a1:P22i_acquired_title_through', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P100_was_death_of', X, Y],O1,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P45_consists_of', Y, X],O1,_,_) \ fact(['a1:P45i_is_incorporated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P45i_is_incorporated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P45i_is_incorporated_in', Y, X],O1,_,_) \ fact(['a1:P45_consists_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P45_consists_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:jabberID', _, X1],O1,_,_) \ fact(['rdfs:Literal', X1],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P78i_identifies', _, X1],O1,_,_) \ fact(['a1:E52_Time-Span', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:primaryTopic', X, _],O1,_,_) \ fact(['a3:Document', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P53_has_former_or_current_location', Y, X],O1,_,_) \ fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P53i_is_former_or_current_location_of', Y, X],O1,_,_) \ fact(['a1:P53_has_former_or_current_location', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P53_has_former_or_current_location', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P37_assigned', Y, X],O1,_,_) \ fact(['a1:P37i_was_assigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P37i_was_assigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P37i_was_assigned_by', Y, X],O1,_,_) \ fact(['a1:P37_assigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P37_assigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:lastName', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P84i_was_maximum_duration_of', X, _],O1,_,_) \ fact(['a1:E54_Dimension', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P32_used_general_technique', X, Y],O1,_,_) \ fact(['a1:P125_used_object_of_type', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P125_used_object_of_type', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P32_used_general_technique', Y, X],O1,_,_) \ fact(['a1:P32i_was_technique_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P32i_was_technique_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P32i_was_technique_of', Y, X],O1,_,_) \ fact(['a1:P32_used_general_technique', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P32_used_general_technique', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P59i_is_located_on_or_within', Y, X],O1,_,_) \ fact(['a1:P59_has_section', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P59_has_section', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P59_has_section', Y, X],O1,_,_) \ fact(['a1:P59i_is_located_on_or_within', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P59i_is_located_on_or_within', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:mbox', Y1, X],O1,_,_), fact(['a3:mbox', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Marriage', X],O1,_,_) \ fact(['a2:GroupEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:GroupEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E79_Part_Addition', X],O1,_,_) \ fact(['a1:E11_Modification', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P35_has_identified', Y, X],O1,_,_) \ fact(['a1:P35i_was_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P35i_was_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P35i_was_identified_by', Y, X],O1,_,_) \ fact(['a1:P35_has_identified', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P35_has_identified', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:focus', X, _],O1,_,_) \ fact(['a8:Concept', X],add,_,U) <=> member(del,[O1]) | fact(['a8:Concept', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:img', _, X1],O1,_,_) \ fact(['a3:Image', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Image', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Organization', X],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:topic_interest', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:eventInterval', _, X1],O1,_,_) \ fact(['a2:Interval', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Interval', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P116i_is_started_by', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', X, Y],O1,_,_) \ fact(['a1:P31i_was_modified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:birth', _, X1],O1,_,_) \ fact(['a2:Birth', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Birth', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P132_overlaps_with', Y, X],O1,_,_) \ fact(['a1:P132_overlaps_with', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P132_overlaps_with', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E71_Man-Made_Thing', X],O1,_,_) \ fact(['a1:P_E71_Man-Made_Thing', X, X],add,_,U) <=> member(del,[O1]) | fact(['a1:P_E71_Man-Made_Thing', X, X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E66_Formation', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P40_observed_dimension', X, _],O1,_,_) \ fact(['a1:E16_Measurement', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E16_Measurement', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyPrecedingEvent', _, X1],O1,_,_) \ fact(['a2:Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P70_documents', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P131_is_identified_by', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P102i_is_title_of', _, X1],O1,_,_) \ fact(['a1:E71_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P11i_participated_in', X, Y],O1,_,_) \ fact(['a1:P12i_was_present_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P29_custody_received_by', X, _],O1,_,_) \ fact(['a1:E10_Transfer_of_Custody', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:event', Y, X],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:agent', Y, X],O1,_,_) \ fact(['a2:event', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:event', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P109_has_current_or_former_curator', X, _],O1,_,_) \ fact(['a1:E78_Collection', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E78_Collection', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P136_was_based_on', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P30_transferred_custody_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyFollowingEvent', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P124i_was_transformed_by', X, _],O1,_,_) \ fact(['a1:E77_Persistent_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P132_overlaps_with', X, _],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P110_augmented', Y, X],O1,_,_) \ fact(['a1:P110i_was_augmented_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P110i_was_augmented_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P110i_was_augmented_by', Y, X],O1,_,_) \ fact(['a1:P110_augmented', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P110_augmented', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P142i_was_used_in', X, _],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E21_Person', X],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P44_has_condition', _, X1],O1,_,_) \ fact(['a1:E3_Condition_State', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P78_is_identified_by', Y, X],O1,_,_) \ fact(['a1:P78i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P78i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P78i_identifies', Y, X],O1,_,_) \ fact(['a1:P78_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P78_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P112_diminished', _, X1],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P8i_witnessed', X, _],O1,_,_) \ fact(['a1:E19_Physical_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P5i_forms_part_of', Y, X],O1,_,_) \ fact(['a1:P5_consists_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P5_consists_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P5_consists_of', Y, X],O1,_,_) \ fact(['a1:P5i_forms_part_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P5i_forms_part_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P116_starts', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39i_was_measured_by', _, X1],O1,_,_) \ fact(['a1:E16_Measurement', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E16_Measurement', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:precedingEvent', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,_,_), fact(['a1:referToSame', X1, X2],O2,_,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,_,_) \ fact(['a1:relatedManMadeThings', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedManMadeThings', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P5i_forms_part_of', X, X2],O1,_,_), fact(['a1:P5i_forms_part_of', X, X1],O2,_,_), fact(['a1:E3_Condition_State', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P10i_contains', _, X1],O1,_,_) \ fact(['a1:E4_Period', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P125i_was_type_of_object_used_in', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P138_represents', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P10_falls_within', X, _],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P56_bears_feature', _, X1],O1,_,_) \ fact(['a1:E26_Physical_Feature', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E26_Physical_Feature', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', X, Y],O1,_,_) \ fact(['a1:P11i_participated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E44_Place_Appellation', X],O1,_,_), fact(['a1:E49_Time_Appellation', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P71_lists', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyPrecedingEvent', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:child', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Event', X],O1,_,_) \ fact(['a9:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a9:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P91i_is_unit_of', X, _],O1,_,_) \ fact(['a1:E58_Measurement_Unit', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E58_Measurement_Unit', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E50_Date', X],O1,_,_) \ fact(['a1:E49_Time_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E49_Time_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P23_transferred_title_from', X, Y],O1,_,_) \ fact(['a1:P14_carried_out_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P110_augmented', _, X1],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', Y, X],O1,_,_) \ fact(['a1:P55i_currently_holds', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P55i_currently_holds', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55i_currently_holds', Y, X],O1,_,_) \ fact(['a1:P55_has_current_location', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P55_has_current_location', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E31_Document', X0, X1],O1,_,_), fact(['a1:referredBySame', X1, X2],O2,_,_), fact(['a1:P_E31_Document', X2, X3],O3,_,_) \ fact(['a1:relatedDocuments', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedDocuments', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:relatedManMadeThings', Y, X],O1,_,_) \ fact(['a1:relatedManMadeThings', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:relatedManMadeThings', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P74i_is_current_or_former_residence_of', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P103i_was_intention_of', _, X1],O1,_,_) \ fact(['a1:E71_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P84_had_at_most_duration', X, X2],O1,_,_), fact(['a1:P84_had_at_most_duration', X, X1],O2,_,_), fact(['a1:E52_Time-Span', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P88_consists_of', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', _, X1],O1,_,_) \ fact(['a1:E83_Type_Creation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E83_Type_Creation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P119i_is_met_in_time_by', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', X, _],O1,_,_) \ fact(['a1:E16_Measurement', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E16_Measurement', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P97i_was_father_for', X, _],O1,_,_) \ fact(['a1:E21_Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P42i_was_assigned_by', _, X1],O1,_,_) \ fact(['a1:E17_Type_Assignment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E17_Type_Assignment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', X, Y],O1,_,_) \ fact(['a1:P12i_was_present_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P106_is_composed_of', X, _],O1,_,_) \ fact(['a1:E90_Symbolic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P43_has_dimension', _, X1],O1,_,_) \ fact(['a1:E54_Dimension', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P81_ongoing_throughout', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:family_name', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P140_assigned_attribute_to', X, _],O1,_,_) \ fact(['a1:E13_Attribute_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P70i_is_documented_in', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P7_took_place_at', X, _],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P45i_is_incorporated_in', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E10_Transfer_of_Custody', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73_has_translation', _, X1],O1,_,_) \ fact(['a1:E33_Linguistic_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', X, X2],O1,_,_), fact(['a1:P95i_was_formed_by', X, X1],O2,_,_), fact(['a1:E74_Group', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P134_continued', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P138i_has_representation', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P109_has_current_or_former_curator', Y, X],O1,_,_) \ fact(['a1:P109i_is_current_or_former_curator_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P109i_is_current_or_former_curator_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P109i_is_current_or_former_curator_of', Y, X],O1,_,_) \ fact(['a1:P109_has_current_or_former_curator', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P109_has_current_or_former_curator', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P11_had_participant', X, Y],O1,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P71_lists', X, Y],O1,_,_) \ fact(['a1:P67_refers_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P44_has_condition', Y, X],O1,_,_) \ fact(['a1:P44i_is_condition_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P44i_is_condition_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P44i_is_condition_of', Y, X],O1,_,_) \ fact(['a1:P44_has_condition', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P44_has_condition', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:openid', Y1, X],O1,_,_), fact(['a3:openid', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P132_overlaps_with', _, X1],O1,_,_) \ fact(['a1:E4_Period', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P111i_was_added_by', _, X1],O1,_,_) \ fact(['a1:E79_Part_Addition', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E79_Part_Addition', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P40i_was_observed_in', _, X1],O1,_,_) \ fact(['a1:E16_Measurement', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E16_Measurement', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P102_has_title', _, X1],O1,_,_) \ fact(['a1:E35_Title', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E35_Title', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', Y, X],O1,_,_) \ fact(['a1:P99_dissolved', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P99_dissolved', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', Y, X],O1,_,_) \ fact(['a1:P99i_was_dissolved_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P99i_was_dissolved_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P119_meets_in_time_with', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P144_joined_with', X, Y],O1,_,_) \ fact(['a1:P11_had_participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:parent', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', X, Y],O1,_,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:initiatingEvent', _, X1],O1,_,_) \ fact(['a2:Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P104i_applies_to', _, X1],O1,_,_) \ fact(['a1:E72_Legal_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P71i_is_listed_in', _, X1],O1,_,_) \ fact(['a1:E32_Authority_Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E32_Authority_Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P35i_was_identified_by', X, _],O1,_,_) \ fact(['a1:E3_Condition_State', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E57_Material', X],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E53_Place', X0, X1],O1,_,_), fact(['a1:referredBySame', X1, X2],O2,_,_), fact(['a1:P_E53_Place', X2, X3],O3,_,_) \ fact(['a1:relatedPlaces', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedPlaces', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P34i_was_assessed_by', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P121_overlaps_with', Y, X],O1,_,_) \ fact(['a1:P121_overlaps_with', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P121_overlaps_with', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13_destroyed', X, _],O1,_,_) \ fact(['a1:E6_Destruction', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E6_Destruction', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P84_had_at_most_duration', _, X1],O1,_,_) \ fact(['a1:E54_Dimension', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P45_consists_of', _, X1],O1,_,_) \ fact(['a1:E57_Material', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P100i_died_in', X, Y],O1,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P123_resulted_in', _, X1],O1,_,_) \ fact(['a1:E77_Persistent_Item', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E51_Contact_Point', X],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, X2],O1,_,_), fact(['a2:father', X, X1],O2,_,_), fact(['a3:Person', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, X4],O1,_,_), fact(['a2:mother', X, X3],O2,_,_), fact(['a3:Person', X],O3,_,_) \ fact(['owl:sameAs', X3, X4],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X3, X4],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P9i_forms_part_of', X, X2],O1,_,_), fact(['a1:P9i_forms_part_of', X, X1],O2,_,_), fact(['a1:E4_Period', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', X, Y],O1,_,_) \ fact(['a1:P11_had_participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P15i_influenced', Y, X],O1,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P15_was_influenced_by', Y, X],O1,_,_) \ fact(['a1:P15i_influenced', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X, _],O1,_,_) \ fact(['a1:E89_Propositional_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:parent', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P14i_performed', Y, X],O1,_,_) \ fact(['a1:P14_carried_out_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P14_carried_out_by', Y, X],O1,_,_) \ fact(['a1:P14i_performed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', X, _],O1,_,_) \ fact(['a1:E19_Physical_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95_has_formed', Y, X],O1,_,_) \ fact(['a1:P95i_was_formed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P95i_was_formed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', Y, X],O1,_,_) \ fact(['a1:P95_has_formed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P95_has_formed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', X, _],O1,_,_) \ fact(['a1:E74_Group', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P42i_was_assigned_by', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P94_has_created', _, X1],O1,_,_) \ fact(['a1:E28_Conceptual_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P131_is_identified_by', _, X1],O1,_,_) \ fact(['a1:E82_Actor_Appellation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E82_Actor_Appellation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:based_near', _, X1],O1,_,_) \ fact(['a10:SpatialThing', X1],add,_,U) <=> member(del,[O1]) | fact(['a10:SpatialThing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', Y, X],O1,_,_) \ fact(['a1:P108i_was_produced_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P108i_was_produced_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', Y, X],O1,_,_) \ fact(['a1:P108_has_produced', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P108_has_produced', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P112i_was_diminished_by', X, Y],O1,_,_) \ fact(['a1:P31i_was_modified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E46_Section_Definition', X],O1,_,_) \ fact(['a1:E44_Place_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P58i_defines_section', Y, X],O1,_,_) \ fact(['a1:P58_has_section_definition', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P58_has_section_definition', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P58_has_section_definition', Y, X],O1,_,_) \ fact(['a1:P58i_defines_section', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P58i_defines_section', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:age', X, Y1],O1,_,_), fact(['a3:age', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P23i_surrendered_title_through', _, X1],O1,_,_) \ fact(['a1:E8_Acquisition', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P78_is_identified_by', X, Y],O1,_,_) \ fact(['a1:P1_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', X, Y],O1,_,_) \ fact(['a1:P7i_witnessed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P7i_witnessed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:currentProject', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P119i_is_met_in_time_by', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:aimChatID', Y1, X],O1,_,_), fact(['a3:aimChatID', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', Y, X],O1,_,_) \ fact(['a1:P27_moved_from', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P27_moved_from', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', Y, X],O1,_,_) \ fact(['a1:P27i_was_origin_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P27i_was_origin_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P37_assigned', _, X1],O1,_,_) \ fact(['a1:E42_Identifier', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P116i_is_started_by', Y, X],O1,_,_) \ fact(['a1:P116_starts', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P116_starts', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P116_starts', Y, X],O1,_,_) \ fact(['a1:P116i_is_started_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P116i_is_started_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:sha1', X, _],O1,_,_) \ fact(['a3:Document', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:agent', _, X1],O1,_,_) \ fact(['a3:Agent', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P12_occurred_in_the_presence_of', X, _],O1,_,_) \ fact(['a1:E5_Event', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P117i_includes', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P29i_received_custody_through', X, Y],O1,_,_) \ fact(['a1:P14i_performed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P102_has_title', X, _],O1,_,_) \ fact(['a1:E71_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P118i_is_overlapped_in_time_by', Y, X],O1,_,_) \ fact(['a1:P118_overlaps_in_time_with', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P118_overlaps_in_time_with', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P118_overlaps_in_time_with', Y, X],O1,_,_) \ fact(['a1:P118i_is_overlapped_in_time_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P118i_is_overlapped_in_time_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P89_falls_within', X, Y],O1,_,_), fact(['a1:P89_falls_within', Y, Z],O2,_,_) \ fact(['a1:P89_falls_within', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P89_falls_within', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P138i_has_representation', X, Y],O1,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, Y1],O1,_,_), fact(['a2:father', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:status', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P137_exemplifies', X, Y],O1,_,_) \ fact(['a1:P2_has_type', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P2_has_type', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:event', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:followingEvent', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E49_Time_Appellation', X],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:witness', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P48i_is_preferred_identifier_of', X, Y],O1,_,_) \ fact(['a1:P1i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P26i_was_destination_of', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:openid', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:organization', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P14i_performed', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P48i_is_preferred_identifier_of', X, _],O1,_,_) \ fact(['a1:E42_Identifier', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:plan', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P34i_was_assessed_by', X, Y],O1,_,_) \ fact(['a1:P140i_was_attributed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P131_is_identified_by', Y, X],O1,_,_) \ fact(['a1:P131i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P131i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P131i_identifies', Y, X],O1,_,_) \ fact(['a1:P131_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P131_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P148i_is_component_of', _, X1],O1,_,_) \ fact(['a1:E89_Propositional_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P1_is_identified_by', _, X1],O1,_,_) \ fact(['a1:E41_Appellation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P129_is_about', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P115i_is_finished_by', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P42_assigned', Y, X],O1,_,_) \ fact(['a1:P42i_was_assigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P42i_was_assigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P42i_was_assigned_by', Y, X],O1,_,_) \ fact(['a1:P42_assigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P42_assigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:employer', _, X1],O1,_,_) \ fact(['a3:Agent', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P31_has_modified', X, _],O1,_,_) \ fact(['a1:E11_Modification', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P87_is_identified_by', Y, X],O1,_,_) \ fact(['a1:P87i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P87i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P87i_identifies', Y, X],O1,_,_) \ fact(['a1:P87_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P87_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:spectator', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E28_Conceptual_Object', X],O1,_,_) \ fact(['a1:E71_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', X, _],O1,_,_) \ fact(['a1:E68_Dissolution', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E68_Dissolution', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:birth', X, Y],O1,_,_) \ fact(['a2:event', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:event', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', X, X2],O1,_,_), fact(['a1:P135i_was_created_by', X, X1],O2,_,_), fact(['a1:E55_Type', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E9_Move', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P128i_is_carried_by', _, X1],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P71i_is_listed_in', X, Y],O1,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P5_consists_of', _, X1],O1,_,_) \ fact(['a1:E3_Condition_State', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P78i_identifies', X, _],O1,_,_) \ fact(['a1:E49_Time_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E49_Time_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P65i_is_shown_by', X, Y],O1,_,_) \ fact(['a1:P128i_is_carried_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P128i_is_carried_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E8_Acquisition', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:followingEvent', _, X1],O1,_,_) \ fact(['a2:Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:icqChatID', _, X1],O1,_,_) \ fact(['rdfs:Literal', X1],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:PhysicalMedium', X],O1,_,_) \ fact(['a5:MediaType', X],add,_,U) <=> member(del,[O1]) | fact(['a5:MediaType', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P70i_is_documented_in', Y, X],O1,_,_) \ fact(['a1:P70_documents', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P70_documents', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P70_documents', Y, X],O1,_,_) \ fact(['a1:P70i_is_documented_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P70i_is_documented_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E75_Conceptual_Object_Appellation', X],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P83i_was_minimum_duration_of', X, _],O1,_,_) \ fact(['a1:E54_Dimension', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Group', X],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P126_employed', _, X1],O1,_,_) \ fact(['a1:E57_Material', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P40i_was_observed_in', X, _],O1,_,_) \ fact(['a1:E54_Dimension', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:agent', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P71_lists', X, _],O1,_,_) \ fact(['a1:E32_Authority_Document', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E32_Authority_Document', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P32i_was_technique_of', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E20_Biological_Object', X],O1,_,_) \ fact(['a1:E19_Physical_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P87i_identifies', X, _],O1,_,_) \ fact(['a1:E44_Place_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P130i_features_are_also_found_on', _, X1],O1,_,_) \ fact(['a1:E70_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P119i_is_met_in_time_by', Y, X],O1,_,_) \ fact(['a1:P119_meets_in_time_with', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P119_meets_in_time_with', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P119_meets_in_time_with', Y, X],O1,_,_) \ fact(['a1:P119i_is_met_in_time_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P119i_is_met_in_time_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:interest', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P146i_lost_member_by', X, Y],O1,_,_) \ fact(['a1:P11i_participated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P30i_custody_transferred_through', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P104_is_subject_to', _, X1],O1,_,_) \ fact(['a1:E30_Right', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E30_Right', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P110_augmented', X, _],O1,_,_) \ fact(['a1:E79_Part_Addition', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E79_Part_Addition', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:based_near', X, _],O1,_,_) \ fact(['a10:SpatialThing', X],add,_,U) <=> member(del,[O1]) | fact(['a10:SpatialThing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', _, X1],O1,_,_) \ fact(['a1:E70_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E72_Legal_Object', X],O1,_,_) \ fact(['a1:E70_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67i_is_referred_to_by', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P112_diminished', X, _],O1,_,_) \ fact(['a1:E80_Part_Removal', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E80_Part_Removal', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:NameChange', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E37_Mark', X],O1,_,_) \ fact(['a1:E36_Visual_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E73_Information_Object', X0, X1],O1,_,_), fact(['a1:P67_refers_to', X1, X2],O2,_,_), fact(['a1:P_E73_Information_Object', X2, X3],O3,_,_) \ fact(['a1:relatedInformationObjects', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedInformationObjects', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:depicts', X, _],O1,_,_) \ fact(['a3:Image', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Image', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:isPrimaryTopicOf', X, Y],O1,_,_) \ fact(['a3:page', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P146i_lost_member_by', X, _],O1,_,_) \ fact(['a1:E74_Group', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P59i_is_located_on_or_within', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X1, X0],O1,_,_), fact(['a1:P67_refers_to', X1, X2],O2,_,_) \ fact(['a1:referredBySame', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:referredBySame', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P28i_surrendered_custody_through', _, X1],O1,_,_) \ fact(['a1:E10_Transfer_of_Custody', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P87i_identifies', X, Y],O1,_,_) \ fact(['a1:P1i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P68i_use_foreseen_by', _, X1],O1,_,_) \ fact(['a1:E29_Design_or_Procedure', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P17i_motivated', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P22_transferred_title_to', X, Y1],O1,_,_), fact(['a1:P22_transferred_title_to', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P86i_contains', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P25i_moved_by', X, Y],O1,_,_) \ fact(['a1:P12i_was_present_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P40_observed_dimension', X, Y],O1,_,_) \ fact(['a1:P141_assigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P46_is_composed_of', Y, X],O1,_,_) \ fact(['a1:P46i_forms_part_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P46i_forms_part_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P46i_forms_part_of', Y, X],O1,_,_) \ fact(['a1:P46_is_composed_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P46_is_composed_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P48_has_preferred_identifier', X, Y],O1,_,_) \ fact(['a1:P1_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P91_has_unit', _, X1],O1,_,_) \ fact(['a1:E58_Measurement_Unit', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E58_Measurement_Unit', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P127_has_broader_term', X, Y],O1,_,_), fact(['a1:P127_has_broader_term', Y, Z],O2,_,_) \ fact(['a1:P127_has_broader_term', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P127_has_broader_term', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:event', _, X1],O1,_,_) \ fact(['a2:Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E3_Condition_State', X],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:accountServiceHomepage', X, _],O1,_,_) \ fact(['a3:OnlineAccount', X],add,_,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P70i_is_documented_in', X, Y],O1,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:holdsAccount', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X0, X1],O1,_,_), fact(['a1:P_E31_Document', X1, X2],O2,_,_) \ fact(['a1:refersToDocument', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:refersToDocument', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P146_separated_from', _, X1],O1,_,_) \ fact(['a1:E74_Group', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P45i_is_incorporated_in', X, _],O1,_,_) \ fact(['a1:E57_Material', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P88i_forms_part_of', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P24i_changed_ownership_through', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:jabberID', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:participant', _, X1],O1,_,_) \ fact(['a3:Agent', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P4_has_time-span', X, X2],O1,_,_), fact(['a1:P4_has_time-span', X, X1],O2,_,_), fact(['a1:E2_Temporal_Entity', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', X, X2],O1,_,_), fact(['a1:P55_has_current_location', X, X1],O2,_,_), fact(['a1:E19_Physical_Object', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P120i_occurs_after', X, Y],O1,_,_), fact(['a1:P120i_occurs_after', Y, Z],O2,_,_) \ fact(['a1:P120i_occurs_after', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P120i_occurs_after', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E13_Attribute_Assignment', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:knows', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:weblog', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:PositionChange', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P134_continued', Y, X],O1,_,_) \ fact(['a1:P134i_was_continued_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P134i_was_continued_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P134i_was_continued_by', Y, X],O1,_,_) \ fact(['a1:P134_continued', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P134_continued', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P29_custody_received_by', X, Y],O1,_,_) \ fact(['a1:P14_carried_out_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P43i_is_dimension_of', X, _],O1,_,_) \ fact(['a1:E54_Dimension', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P137_exemplifies', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P65i_is_shown_by', X, _],O1,_,_) \ fact(['a1:E36_Visual_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P91i_is_unit_of', Y, X],O1,_,_) \ fact(['a1:P91_has_unit', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P91_has_unit', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P91_has_unit', Y, X],O1,_,_) \ fact(['a1:P91i_is_unit_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P91i_is_unit_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', X, Y],O1,_,_) \ fact(['a1:P53_has_former_or_current_location', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P53_has_former_or_current_location', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P145i_left_by', Y, X],O1,_,_) \ fact(['a1:P145_separated', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P145_separated', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P145_separated', Y, X],O1,_,_) \ fact(['a1:P145i_left_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P145i_left_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95_has_formed', X, _],O1,_,_) \ fact(['a1:E66_Formation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E66_Formation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P38i_was_deassigned_by', X, _],O1,_,_) \ fact(['a1:E42_Identifier', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyPrecedingEvent', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:isPrimaryTopicOf', Y, X],O1,_,_) \ fact(['a3:primaryTopic', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:primaryTopic', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:primaryTopic', Y, X],O1,_,_) \ fact(['a3:isPrimaryTopicOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:isPrimaryTopicOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P38_deassigned', X, _],O1,_,_) \ fact(['a1:E15_Identifier_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P17_was_motivated_by', X, Y],O1,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P4i_is_time-span_of', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E31_Document', X0, X1],O1,_,_), fact(['a1:referToSame', X1, X2],O2,_,_), fact(['a1:P_E31_Document', X2, X3],O3,_,_) \ fact(['a1:relatedDocuments', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedDocuments', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Performance', X],O1,_,_) \ fact(['a2:GroupEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:GroupEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:PersonalProfileDocument', X],O1,_,_) \ fact(['a3:Document', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P17_was_motivated_by', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P19_was_intended_use_of', Y, X],O1,_,_) \ fact(['a1:P19i_was_made_for', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P19i_was_made_for', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P19i_was_made_for', Y, X],O1,_,_) \ fact(['a1:P19_was_intended_use_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P19_was_intended_use_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P29i_received_custody_through', _, X1],O1,_,_) \ fact(['a1:E10_Transfer_of_Custody', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P30_transferred_custody_of', X, _],O1,_,_) \ fact(['a1:E10_Transfer_of_Custody', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:skypeID', X, Y],O1,_,_) \ fact(['a3:nick', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P101_had_as_general_use', Y, X],O1,_,_) \ fact(['a1:P101i_was_use_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P101i_was_use_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P101i_was_use_of', Y, X],O1,_,_) \ fact(['a1:P101_had_as_general_use', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P101_had_as_general_use', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P131_is_identified_by', X, Y],O1,_,_) \ fact(['a1:P1_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P46i_forms_part_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P76_has_contact_point', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:death', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:followingEvent', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P58i_defines_section', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', X, _],O1,_,_) \ fact(['a1:E70_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', X, Y],O1,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:relatedDocuments', Y, X],O1,_,_) \ fact(['a1:relatedDocuments', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:relatedDocuments', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P75_possesses', _, X1],O1,_,_) \ fact(['a1:E30_Right', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E30_Right', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E5_Event', X],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P131i_identifies', X, _],O1,_,_) \ fact(['a1:E82_Actor_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E82_Actor_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P35_has_identified', X, _],O1,_,_) \ fact(['a1:E14_Condition_Assessment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P143_joined', X, X2],O1,_,_), fact(['a1:P143_joined', X, X1],O2,_,_), fact(['a1:E85_Joining', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P83_had_at_least_duration', Y, X],O1,_,_) \ fact(['a1:P83i_was_minimum_duration_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P83i_was_minimum_duration_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P83i_was_minimum_duration_of', Y, X],O1,_,_) \ fact(['a1:P83_had_at_least_duration', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P83_had_at_least_duration', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P113i_was_removed_by', Y, X],O1,_,_) \ fact(['a1:P113_removed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P113_removed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P113_removed', Y, X],O1,_,_) \ fact(['a1:P113i_was_removed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P113i_was_removed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', X, Y],O1,_,_) \ fact(['a1:P7_took_place_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P7_took_place_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E73_Information_Object', X0, X1],O1,_,_), fact(['a1:referToSame', X1, X2],O2,_,_), fact(['a1:P_E73_Information_Object', X2, X3],O3,_,_) \ fact(['a1:relatedInformationObjects', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedInformationObjects', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', X, Y],O1,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E31_Document', X],O1,_,_) \ fact(['a1:E73_Information_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E40_Legal_Body', X],O1,_,_) \ fact(['a1:E74_Group', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P106_is_composed_of', X, Y],O1,_,_), fact(['a1:P106_is_composed_of', Y, Z],O2,_,_) \ fact(['a1:P106_is_composed_of', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P106_is_composed_of', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P62i_is_depicted_by', Y, X],O1,_,_) \ fact(['a1:P62_depicts', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P62_depicts', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P62_depicts', Y, X],O1,_,_) \ fact(['a1:P62i_is_depicted_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P62i_is_depicted_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:birth', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E39_Actor', X],O1,_,_) \ fact(['a1:E77_Persistent_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E64_End_of_Existence', X],O1,_,_) \ fact(['a1:E5_Event', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P74_has_current_or_former_residence', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P110i_was_augmented_by', X, Y],O1,_,_) \ fact(['a1:P31i_was_modified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P52i_is_current_owner_of', X, Y],O1,_,_) \ fact(['a1:P105i_has_right_on', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P105i_has_right_on', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P101_had_as_general_use', X, _],O1,_,_) \ fact(['a1:E70_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13_destroyed', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P142_used_constituent', X, _],O1,_,_) \ fact(['a1:E15_Identifier_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E45_Address', X],O1,_,_) \ fact(['a1:E51_Contact_Point', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E51_Contact_Point', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P43i_is_dimension_of', Y, X],O1,_,_) \ fact(['a1:P43_has_dimension', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P43_has_dimension', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P43_has_dimension', Y, X],O1,_,_) \ fact(['a1:P43i_is_dimension_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P43i_is_dimension_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P21_had_general_purpose', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:relationship', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:AgentClass', X],O1,_,_) \ fact(['rdfs:Class', X],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Class', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P31i_was_modified_by', Y, X],O1,_,_) \ fact(['a1:P31_has_modified', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P31_has_modified', Y, X],O1,_,_) \ fact(['a1:P31i_was_modified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:partner', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', Y, X],O1,_,_) \ fact(['a1:P98_brought_into_life', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P98_brought_into_life', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98_brought_into_life', Y, X],O1,_,_) \ fact(['a1:P98i_was_born', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P98i_was_born', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyFollowingEvent', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P134_continued', X, Y],O1,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P35_has_identified', _, X1],O1,_,_) \ fact(['a1:E3_Condition_State', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P51i_is_former_or_current_owner_of', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, Y],O1,_,_) \ fact(['a6:childOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a6:childOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P115_finishes', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:thumbnail', _, X1],O1,_,_) \ fact(['a3:Image', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Image', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P2_has_type', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P5i_forms_part_of', _, X1],O1,_,_) \ fact(['a1:E3_Condition_State', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P22i_acquired_title_through', Y, X],O1,_,_) \ fact(['a1:P22_transferred_title_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P22_transferred_title_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P22_transferred_title_to', Y, X],O1,_,_) \ fact(['a1:P22i_acquired_title_through', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P22i_acquired_title_through', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P25_moved', _, X1],O1,_,_) \ fact(['a1:E19_Physical_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P127_has_broader_term', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P69_is_associated_with', Y, X],O1,_,_) \ fact(['a1:P69_is_associated_with', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P69_is_associated_with', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P139_has_alternative_form', _, X1],O1,_,_) \ fact(['a1:E41_Appellation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P26_moved_to', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P123_resulted_in', X, _],O1,_,_) \ fact(['a1:E81_Transformation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E81_Transformation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P92_brought_into_existence', _, X1],O1,_,_) \ fact(['a1:E77_Persistent_Item', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:FileFormat', X],O1,_,_) \ fact(['a5:MediaType', X],add,_,U) <=> member(del,[O1]) | fact(['a5:MediaType', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P50_has_current_keeper', X, Y],O1,_,_) \ fact(['a1:P49_has_former_or_current_keeper', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:firstName', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P2_has_type', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E25_Man-Made_Feature', X],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E73_Information_Object', X],O1,_,_) \ fact(['a1:E89_Propositional_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P96i_gave_birth', X, Y],O1,_,_) \ fact(['a1:P11i_participated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P28_custody_surrendered_by', X, _],O1,_,_) \ fact(['a1:E10_Transfer_of_Custody', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55i_currently_holds', X, Y],O1,_,_) \ fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P87_is_identified_by', X, Y],O1,_,_) \ fact(['a1:P1_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P37_assigned', X, Y],O1,_,_) \ fact(['a1:P141_assigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:workInfoHomepage', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E22_Man-Made_Object', X],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P109i_is_current_or_former_curator_of', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P15i_influenced', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', X, X2],O1,_,_), fact(['a1:P73i_is_translation_of', X, X1],O2,_,_), fact(['a1:E33_Linguistic_Object', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', _, X1],O1,_,_) \ fact(['a1:E66_Formation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E66_Formation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P129_is_about', X, Y],O1,_,_) \ fact(['a1:P67_refers_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E81_Transformation', X],O1,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E31_Document', X0, X1],O1,_,_), fact(['a1:refersToDocument', X1, X2],O2,_,_), fact(['a1:refersToDocument', X2, X3],O3,_,_) \ fact(['a1:relatedDocuments', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedDocuments', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P33i_was_used_by', Y, X],O1,_,_) \ fact(['a1:P33_used_specific_technique', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P33_used_specific_technique', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P33_used_specific_technique', Y, X],O1,_,_) \ fact(['a1:P33i_was_used_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P33i_was_used_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P111_added', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P129i_is_subject_of', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P9i_forms_part_of', X, _],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P14_carried_out_by', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P126i_was_employed_in', _, X1],O1,_,_) \ fact(['a1:E11_Modification', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,_,_), fact(['a1:referredBySame', X1, X2],O2,_,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,_,_) \ fact(['a1:relatedManMadeThings', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedManMadeThings', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P58i_defines_section', X, _],O1,_,_) \ fact(['a1:E46_Section_Definition', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E46_Section_Definition', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P14i_performed', X, Y],O1,_,_) \ fact(['a1:P11i_participated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P139_has_alternative_form', X, _],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P75_possesses', Y, X],O1,_,_) \ fact(['a1:P75i_is_possessed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P75i_is_possessed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P75i_is_possessed_by', Y, X],O1,_,_) \ fact(['a1:P75_possesses', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P75_possesses', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:position', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P145i_left_by', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P10_falls_within', _, X1],O1,_,_) \ fact(['a1:E4_Period', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E45_Address', X],O1,_,_) \ fact(['a1:E44_Place_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyFollowingEvent', X, Y],O1,_,_) \ fact(['a2:followingEvent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:followingEvent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', _, X1],O1,_,_) \ fact(['a1:E33_Linguistic_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Employment', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:Location', X],O1,_,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],add,_,U) <=> member(del,[O1]) | fact(['a5:LocationPeriodOrJurisdiction', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P33i_was_used_by', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:topic', X, _],O1,_,_) \ fact(['a3:Document', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P12_occurred_in_the_presence_of', Y, X],O1,_,_) \ fact(['a1:P12i_was_present_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P12i_was_present_at', Y, X],O1,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P117_occurs_during', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P76i_provides_access_to', X, _],O1,_,_) \ fact(['a1:E51_Contact_Point', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E51_Contact_Point', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P70_documents', X, _],O1,_,_) \ fact(['a1:E31_Document', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E31_Document', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:MediaType', X],O1,_,_) \ fact(['a5:MediaTypeOrExtent', X],add,_,U) <=> member(del,[O1]) | fact(['a5:MediaTypeOrExtent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:maker', _, X1],O1,_,_) \ fact(['a3:Agent', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:primaryTopic', X, Y1],O1,_,_), fact(['a3:primaryTopic', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:mbox_sha1sum', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', _, X1],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P35i_was_identified_by', _, X1],O1,_,_) \ fact(['a1:E14_Condition_Assessment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P76_has_contact_point', _, X1],O1,_,_) \ fact(['a1:E51_Contact_Point', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E51_Contact_Point', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E84_Information_Carrier', X],O1,_,_) \ fact(['a1:E22_Man-Made_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E22_Man-Made_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P48_has_preferred_identifier', Y, X],O1,_,_) \ fact(['a1:P48i_is_preferred_identifier_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P48i_is_preferred_identifier_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P48i_is_preferred_identifier_of', Y, X],O1,_,_) \ fact(['a1:P48_has_preferred_identifier', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P48_has_preferred_identifier', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:BasMitzvah', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P124i_was_transformed_by', Y, X],O1,_,_) \ fact(['a1:P124_transformed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P124_transformed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P124_transformed', Y, X],O1,_,_) \ fact(['a1:P124i_was_transformed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P124i_was_transformed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P92_brought_into_existence', X, Y],O1,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13_destroyed', X, Y],O1,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P8_took_place_on_or_within', Y, X],O1,_,_) \ fact(['a1:P8i_witnessed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P8i_witnessed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P8i_witnessed', Y, X],O1,_,_) \ fact(['a1:P8_took_place_on_or_within', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P8_took_place_on_or_within', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P76i_provides_access_to', Y, X],O1,_,_) \ fact(['a1:P76_has_contact_point', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P76_has_contact_point', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P76_has_contact_point', Y, X],O1,_,_) \ fact(['a1:P76i_provides_access_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P76i_provides_access_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P106i_forms_part_of', _, X1],O1,_,_) \ fact(['a1:E90_Symbolic_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P56_bears_feature', X, Y],O1,_,_) \ fact(['a1:P46_is_composed_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P46_is_composed_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P145i_left_by', X, Y],O1,_,_) \ fact(['a1:P11i_participated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:mbox', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P53_has_former_or_current_location', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', X, _],O1,_,_) \ fact(['a1:E74_Group', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P25_moved', X, Y],O1,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyFollowingEvent', _, X1],O1,_,_) \ fact(['a2:Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P96_by_mother', _, X1],O1,_,_) \ fact(['a1:E21_Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:msnChatID', X, Y],O1,_,_) \ fact(['a3:nick', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P146i_lost_member_by', Y, X],O1,_,_) \ fact(['a1:P146_separated_from', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P146_separated_from', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P146_separated_from', Y, X],O1,_,_) \ fact(['a1:P146i_lost_member_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P146i_lost_member_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P40_observed_dimension', _, X1],O1,_,_) \ fact(['a1:E54_Dimension', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:mother', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P33_used_specific_technique', _, X1],O1,_,_) \ fact(['a1:E29_Design_or_Procedure', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41i_was_classified_by', X, Y],O1,_,_) \ fact(['a1:P140i_was_attributed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:schoolHomepage', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P52_has_current_owner', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P7_took_place_at', Y, X],O1,_,_) \ fact(['a1:P7i_witnessed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P7i_witnessed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P7i_witnessed', Y, X],O1,_,_) \ fact(['a1:P7_took_place_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P7_took_place_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95_has_formed', _, X1],O1,_,_) \ fact(['a1:E74_Group', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Person', X],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P127i_has_narrower_term', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E6_Destruction', X],O1,_,_) \ fact(['a1:E64_End_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P53i_is_former_or_current_location_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P134_continued', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:account', _, X1],O1,_,_) \ fact(['a3:OnlineAccount', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P127_has_broader_term', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P93_took_out_of_existence', _, X1],O1,_,_) \ fact(['a1:E77_Persistent_Item', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P137_exemplifies', Y, X],O1,_,_) \ fact(['a1:P137i_is_exemplified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P137i_is_exemplified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P137i_is_exemplified_by', Y, X],O1,_,_) \ fact(['a1:P137_exemplifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P137_exemplifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P22_transferred_title_to', X, _],O1,_,_) \ fact(['a1:E8_Acquisition', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:accountName', X, _],O1,_,_) \ fact(['a3:OnlineAccount', X],add,_,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P30i_custody_transferred_through', _, X1],O1,_,_) \ fact(['a1:E10_Transfer_of_Custody', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P86_falls_within', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', X, Y],O1,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P20_had_specific_purpose', Y, X],O1,_,_) \ fact(['a1:P20i_was_purpose_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P20i_was_purpose_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P20i_was_purpose_of', Y, X],O1,_,_) \ fact(['a1:P20_had_specific_purpose', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P20_had_specific_purpose', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P89i_contains', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P5i_forms_part_of', X, _],O1,_,_) \ fact(['a1:E3_Condition_State', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P49i_is_former_or_current_keeper_of', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P128i_is_carried_by', X, _],O1,_,_) \ fact(['a1:E73_Information_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Imprisonment', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:tipjar', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P92i_was_brought_into_existence_by', X, Y],O1,_,_) \ fact(['a1:P12i_was_present_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', X, Y],O1,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:organization', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:concurrentEvent', Y, X],O1,_,_) \ fact(['a2:concurrentEvent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:concurrentEvent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:yahooChatID', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P42_assigned', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P91_has_unit', X, _],O1,_,_) \ fact(['a1:E54_Dimension', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Retirement', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:tipjar', X, Y],O1,_,_) \ fact(['a3:page', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P62_depicts', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:interval', _, X1],O1,_,_) \ fact(['a2:Interval', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Interval', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:olb', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P117i_includes', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P88i_forms_part_of', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', X, Y],O1,_,_) \ fact(['a1:P130i_features_are_also_found_on', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135_created_type', X, _],O1,_,_) \ fact(['a1:E83_Type_Creation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E83_Type_Creation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P59i_is_located_on_or_within', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Dismissal', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P96i_gave_birth', _, X1],O1,_,_) \ fact(['a1:E67_Birth', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E27_Site', X],O1,_,_) \ fact(['a1:E26_Physical_Feature', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E26_Physical_Feature', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:principal', X, X2],O1,_,_), fact(['a2:principal', X, X1],O2,_,_), fact(['a2:IndividualEvent', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:msnChatID', _, X1],O1,_,_) \ fact(['rdfs:Literal', X1],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:homepage', Y1, X],O1,_,_), fact(['a3:homepage', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P1i_identifies', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P10_falls_within', X, Y],O1,_,_), fact(['a1:P10_falls_within', Y, Z],O2,_,_) \ fact(['a1:P10_falls_within', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P10_falls_within', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P96_by_mother', X, _],O1,_,_) \ fact(['a1:E67_Birth', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Enrolment', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P75_possesses', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P93i_was_taken_out_of_existence_by', _, X1],O1,_,_) \ fact(['a1:E64_End_of_Existence', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P100_was_death_of', _, X1],O1,_,_) \ fact(['a1:E21_Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P126i_was_employed_in', X, _],O1,_,_) \ fact(['a1:E57_Material', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P9i_forms_part_of', _, X1],O1,_,_) \ fact(['a1:E4_Period', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Person', X],O1,_,_) \ fact(['a10:SpatialThing', X],add,_,U) <=> member(del,[O1]) | fact(['a10:SpatialThing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', X, Y],O1,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P92i_was_brought_into_existence_by', X, _],O1,_,_) \ fact(['a1:E77_Persistent_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P54i_is_current_permanent_location_of', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P51i_is_former_or_current_owner_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P115i_is_finished_by', X, Y],O1,_,_), fact(['a1:P115i_is_finished_by', Y, Z],O2,_,_) \ fact(['a1:P115i_is_finished_by', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P115i_is_finished_by', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P137i_is_exemplified_by', X, Y],O1,_,_) \ fact(['a1:P2i_is_type_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P2i_is_type_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:concludingEvent', _, X1],O1,_,_) \ fact(['a2:Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:thumbnail', X, _],O1,_,_) \ fact(['a3:Image', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Image', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:parent', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P44i_is_condition_of', X, _],O1,_,_) \ fact(['a1:E3_Condition_State', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P144i_gained_member_by', X, Y],O1,_,_) \ fact(['a1:P11i_participated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P118i_is_overlapped_in_time_by', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P129i_is_subject_of', _, X1],O1,_,_) \ fact(['a1:E89_Propositional_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', _, X1],O1,_,_) \ fact(['a1:E74_Group', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P20_had_specific_purpose', _, X1],O1,_,_) \ fact(['a1:E5_Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', _, X1],O1,_,_) \ fact(['a1:E67_Birth', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P32i_was_technique_of', X, Y],O1,_,_) \ fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', X, Y],O1,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P65_shows_visual_item', X, _],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P129i_is_subject_of', X, Y],O1,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P134i_was_continued_by', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:msnChatID', Y1, X],O1,_,_), fact(['a3:msnChatID', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P87_is_identified_by', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Person', X],O1,_,_), fact(['a3:Project', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E33_Linguistic_Object', X],O1,_,_) \ fact(['a1:E73_Information_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:geekcode', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:officiator', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P114_is_equal_in_time_to', Y, X],O1,_,_) \ fact(['a1:P114_is_equal_in_time_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P114_is_equal_in_time_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:partner', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:spectator', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P28i_surrendered_custody_through', X, Y],O1,_,_) \ fact(['a1:P14i_performed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P136i_supported_type_creation', X, Y],O1,_,_) \ fact(['a1:P15i_influenced', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P72i_is_language_of', X, _],O1,_,_) \ fact(['a1:E56_Language', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E56_Language', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P96_by_mother', X, Y],O1,_,_) \ fact(['a1:P11_had_participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P116_starts', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:img', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P100i_died_in', X, _],O1,_,_) \ fact(['a1:E21_Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P96i_gave_birth', X, _],O1,_,_) \ fact(['a1:E21_Person', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', X, Y],O1,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:familyName', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P148_has_component', X, Y],O1,_,_), fact(['a1:P148_has_component', Y, Z],O2,_,_) \ fact(['a1:P148_has_component', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P148_has_component', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P55i_currently_holds', _, X1],O1,_,_) \ fact(['a1:E19_Physical_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Event', X],O1,_,_) \ fact(['a11:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a11:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P97i_was_father_for', Y, X],O1,_,_) \ fact(['a1:P97_from_father', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P97_from_father', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P97_from_father', Y, X],O1,_,_) \ fact(['a1:P97i_was_father_for', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P97i_was_father_for', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P26_moved_to', X, _],O1,_,_) \ fact(['a1:E9_Move', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E52_Time-Span', X],O1,_,_), fact(['a1:E53_Place', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P89_falls_within', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E56_Language', X],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:spectator', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P40i_was_observed_in', Y, X],O1,_,_) \ fact(['a1:P40_observed_dimension', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P40_observed_dimension', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P40_observed_dimension', Y, X],O1,_,_) \ fact(['a1:P40i_was_observed_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P40i_was_observed_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,_,_), fact(['a1:P67_refers_to', X1, X2],O2,_,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,_,_) \ fact(['a1:relatedManMadeThings', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedManMadeThings', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Adoption', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P42i_was_assigned_by', X, Y],O1,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P95_has_formed', X, Y],O1,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P31i_was_modified_by', X, Y],O1,_,_) \ fact(['a1:P12i_was_present_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P56i_is_found_on', X, Y],O1,_,_) \ fact(['a1:P46i_forms_part_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P46i_forms_part_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P117_occurs_during', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', X, Y],O1,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:msnChatID', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P89i_contains', X, Y],O1,_,_), fact(['a1:P89i_contains', Y, Z],O2,_,_) \ fact(['a1:P89i_contains', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P89i_contains', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E31_Document', X0, X1],O1,_,_), fact(['a1:P67_refers_to', X1, X2],O2,_,_), fact(['a1:P_E31_Document', X2, X3],O3,_,_) \ fact(['a1:relatedDocuments', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedDocuments', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P137i_is_exemplified_by', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P130_shows_features_of', Y, X],O1,_,_) \ fact(['a1:P130i_features_are_also_found_on', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P130i_features_are_also_found_on', Y, X],O1,_,_) \ fact(['a1:P130_shows_features_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P130_shows_features_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P52i_is_current_owner_of', X, Y],O1,_,_) \ fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P46i_forms_part_of', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P19i_was_made_for', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E17_Type_Assignment', X],O1,_,_) \ fact(['a1:E13_Attribute_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E32_Authority_Document', X],O1,_,_) \ fact(['a1:E31_Document', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E31_Document', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', Y, X],O1,_,_) \ fact(['a1:P135_created_type', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P135_created_type', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135_created_type', Y, X],O1,_,_) \ fact(['a1:P135i_was_created_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P135i_was_created_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P120_occurs_before', Y, X],O1,_,_) \ fact(['a1:P120i_occurs_after', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P120i_occurs_after', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P120i_occurs_after', Y, X],O1,_,_) \ fact(['a1:P120_occurs_before', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P120_occurs_before', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P107i_is_current_or_former_member_of', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:gender', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P19i_was_made_for', X, _],O1,_,_) \ fact(['a1:E71_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P86_falls_within', X, Y],O1,_,_), fact(['a1:P86_falls_within', Y, Z],O2,_,_) \ fact(['a1:P86_falls_within', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P86_falls_within', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P120_occurs_before', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E19_Physical_Object', X],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P7i_witnessed', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P75i_is_possessed_by', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['rdfs:ContainerMembershipProperty', X],O1,_,_) \ fact(['rdf:Property', X],add,_,U) <=> member(del,[O1]) | fact(['rdf:Property', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', _, X1],O1,_,_) \ fact(['a1:E9_Move', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P92i_was_brought_into_existence_by', _, X1],O1,_,_) \ fact(['a1:E63_Beginning_of_Existence', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P113i_was_removed_by', _, X1],O1,_,_) \ fact(['a1:E80_Part_Removal', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E80_Part_Removal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P103_was_intended_for', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:child', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:homepage', X, Y],O1,_,_) \ fact(['a3:page', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:partner', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39i_was_measured_by', X, Y],O1,_,_) \ fact(['a1:P140i_was_attributed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E48_Place_Name', X],O1,_,_) \ fact(['a1:P_E53_Place', X, X],add,_,U) <=> member(del,[O1]) | fact(['a1:P_E53_Place', X, X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:schoolHomepage', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P34_concerned', X, _],O1,_,_) \ fact(['a1:E14_Condition_Assessment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Redundancy', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P28_custody_surrendered_by', Y, X],O1,_,_) \ fact(['a1:P28i_surrendered_custody_through', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P28i_surrendered_custody_through', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P28i_surrendered_custody_through', Y, X],O1,_,_) \ fact(['a1:P28_custody_surrendered_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P28_custody_surrendered_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', X, Y],O1,_,_), fact(['a1:P27_moved_from', Y, Z],O2,_,_) \ fact(['a1:P27_moved_from', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P27_moved_from', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E80_Part_Removal', X],O1,_,_) \ fact(['a1:E11_Modification', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P102i_is_title_of', X, _],O1,_,_) \ fact(['a1:E35_Title', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E35_Title', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P116i_is_started_by', X, Y],O1,_,_), fact(['a1:P116i_is_started_by', Y, Z],O2,_,_) \ fact(['a1:P116i_is_started_by', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P116i_is_started_by', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E44_Place_Appellation', X],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P54_has_current_permanent_location', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P38i_was_deassigned_by', Y, X],O1,_,_) \ fact(['a1:P38_deassigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P38_deassigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P38_deassigned', Y, X],O1,_,_) \ fact(['a1:P38i_was_deassigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P38i_was_deassigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P97i_was_father_for', _, X1],O1,_,_) \ fact(['a1:E67_Birth', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P4_has_time-span', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Formation', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:agent', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P137_exemplifies', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P137i_is_exemplified_by', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P80_end_is_qualified_by', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:knows', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Disbanding', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P148i_is_component_of', X, Y],O1,_,_), fact(['a1:P148i_is_component_of', Y, Z],O2,_,_) \ fact(['a1:P148i_is_component_of', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P148i_is_component_of', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:yahooChatID', X, Y],O1,_,_) \ fact(['a3:nick', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:death', X, Y],O1,_,_) \ fact(['a2:event', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:event', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P89_falls_within', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P115_finishes', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:death', _, X1],O1,_,_) \ fact(['a2:Death', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Death', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P35i_was_identified_by', X, Y],O1,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P111_added', X, _],O1,_,_) \ fact(['a1:E79_Part_Addition', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E79_Part_Addition', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P37i_was_assigned_by', X, _],O1,_,_) \ fact(['a1:E42_Identifier', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P42_assigned', X, _],O1,_,_) \ fact(['a1:E17_Type_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E17_Type_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E73_Information_Object', X],O1,_,_) \ fact(['a1:E90_Symbolic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P110_augmented', X, Y],O1,_,_) \ fact(['a1:P31_has_modified', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P78i_identifies', X, Y],O1,_,_) \ fact(['a1:P1i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P91i_is_unit_of', _, X1],O1,_,_) \ fact(['a1:E54_Dimension', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P146_separated_from', X, _],O1,_,_) \ fact(['a1:E86_Leaving', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E86_Leaving', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:position', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P86i_contains', _, X1],O1,_,_) \ fact(['a1:E52_Time-Span', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:mbox_sha1sum', Y1, X],O1,_,_), fact(['a3:mbox_sha1sum', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E74_Group', X],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P37i_was_assigned_by', X, Y],O1,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:yahooChatID', _, X1],O1,_,_) \ fact(['rdfs:Literal', X1],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P127i_has_narrower_term', X, Y],O1,_,_), fact(['a1:P127i_has_narrower_term', Y, Z],O2,_,_) \ fact(['a1:P127i_has_narrower_term', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P127i_has_narrower_term', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:member', _, X1],O1,_,_) \ fact(['a3:Agent', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P21i_was_purpose_of', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E29_Design_or_Procedure', X],O1,_,_) \ fact(['a1:E73_Information_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Execution', X],O1,_,_) \ fact(['a2:Death', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Death', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P71_lists', Y, X],O1,_,_) \ fact(['a1:P71i_is_listed_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P71i_is_listed_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P71i_is_listed_in', Y, X],O1,_,_) \ fact(['a1:P71_lists', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P71_lists', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P84_had_at_most_duration', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P101i_was_use_of', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P142_used_constituent', Y, X],O1,_,_) \ fact(['a1:P142i_was_used_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P142i_was_used_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P142i_was_used_in', Y, X],O1,_,_) \ fact(['a1:P142_used_constituent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P142_used_constituent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:position', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P147i_was_curated_by', _, X1],O1,_,_) \ fact(['a1:E87_Curation_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E87_Curation_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P49_has_former_or_current_keeper', Y, X],O1,_,_) \ fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P49i_is_former_or_current_keeper_of', Y, X],O1,_,_) \ fact(['a1:P49_has_former_or_current_keeper', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P38i_was_deassigned_by', X, Y],O1,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P145i_left_by', _, X1],O1,_,_) \ fact(['a1:E86_Leaving', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E86_Leaving', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P91_has_unit', X, X2],O1,_,_), fact(['a1:P91_has_unit', X, X1],O2,_,_), fact(['a1:E54_Dimension', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:relationship', _, X1],O1,_,_) \ fact(['a2:Relationship', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Relationship', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', X, _],O1,_,_) \ fact(['a1:E33_Linguistic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P75i_is_possessed_by', X, _],O1,_,_) \ fact(['a1:E30_Right', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E30_Right', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:principal', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:OnlineEcommerceAccount', X],O1,_,_) \ fact(['a3:OnlineAccount', X],add,_,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P2i_is_type_of', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E31_Document', X],O1,_,_) \ fact(['a1:P_E31_Document', X, X],add,_,U) <=> member(del,[O1]) | fact(['a1:P_E31_Document', X, X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:principal', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P144i_gained_member_by', X, _],O1,_,_) \ fact(['a1:E74_Group', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P74i_is_current_or_former_residence_of', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:holdsAccount', _, X1],O1,_,_) \ fact(['a3:OnlineAccount', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P90_has_value', X, _],O1,_,_) \ fact(['a1:E54_Dimension', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:weblog', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41i_was_classified_by', _, X1],O1,_,_) \ fact(['a1:E17_Type_Assignment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E17_Type_Assignment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P123_resulted_in', X, Y],O1,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P93_took_out_of_existence', X, _],O1,_,_) \ fact(['a1:E64_End_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:concurrentEvent', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P49i_is_former_or_current_keeper_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['rdfs:Datatype', X],O1,_,_) \ fact(['rdfs:Class', X],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Class', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P111i_was_added_by', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, _],O1,_,_), fact(['a2:mother', X, _],O2,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1,O2]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P125i_was_type_of_object_used_in', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P145_separated', X, Y],O1,_,_) \ fact(['a1:P11_had_participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P57_has_number_of_parts', X, _],O1,_,_) \ fact(['a1:E19_Physical_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Investiture', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P147_curated', X, _],O1,_,_) \ fact(['a1:E87_Curation_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E87_Curation_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P138i_has_representation', _, X1],O1,_,_) \ fact(['a1:E36_Visual_Item', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67i_is_referred_to_by', Y, X],O1,_,_) \ fact(['a1:P67_refers_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', Y, X],O1,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P50_has_current_keeper', Y, X],O1,_,_) \ fact(['a1:P50i_is_current_keeper_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P50i_is_current_keeper_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P50i_is_current_keeper_of', Y, X],O1,_,_) \ fact(['a1:P50_has_current_keeper', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P50_has_current_keeper', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P138_represents', X, _],O1,_,_) \ fact(['a1:E36_Visual_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73_has_translation', X, Y],O1,_,_) \ fact(['a1:P130_shows_features_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P130_shows_features_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:concurrentEvent', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:PeriodOfTime', X],O1,_,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],add,_,U) <=> member(del,[O1]) | fact(['a5:LocationPeriodOrJurisdiction', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P143i_was_joined_by', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P121_overlaps_with', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P34i_was_assessed_by', Y, X],O1,_,_) \ fact(['a1:P34_concerned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P34_concerned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P34_concerned', Y, X],O1,_,_) \ fact(['a1:P34i_was_assessed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P34i_was_assessed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', _, X1],O1,_,_) \ fact(['a1:E12_Production', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E12_Production', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P140i_was_attributed_by', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P117i_includes', X, Y],O1,_,_), fact(['a1:P117i_includes', Y, Z],O2,_,_) \ fact(['a1:P117i_includes', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P117i_includes', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P102i_is_title_of', X, Y],O1,_,_) \ fact(['a1:P1i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X0, X1],O1,_,_), fact(['a1:P67_refers_to', X2, X1],O2,_,_) \ fact(['a1:referToSame', X0, X2],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:referToSame', X0, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E71_Man-Made_Thing', X],O1,_,_) \ fact(['a1:E70_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P141_assigned', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P74_has_current_or_former_residence', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P84i_was_maximum_duration_of', Y, X],O1,_,_) \ fact(['a1:P84_had_at_most_duration', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P84_had_at_most_duration', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P84_had_at_most_duration', Y, X],O1,_,_) \ fact(['a1:P84i_was_maximum_duration_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P84i_was_maximum_duration_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:weblog', X, Y],O1,_,_) \ fact(['a3:page', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E77_Persistent_Item', X],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P104i_applies_to', Y, X],O1,_,_) \ fact(['a1:P104_is_subject_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P104_is_subject_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P104_is_subject_to', Y, X],O1,_,_) \ fact(['a1:P104i_applies_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P104i_applies_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E87_Curation_Activity', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:isPrimaryTopicOf', Y1, X],O1,_,_), fact(['a3:isPrimaryTopicOf', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Relationship', X],O1,_,_) \ fact(['a6:Relationship', X],add,_,U) <=> member(del,[O1]) | fact(['a6:Relationship', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a6:Relationship', X],O1,_,_) \ fact(['a2:Relationship', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Relationship', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:logo', Y1, X],O1,_,_), fact(['a3:logo', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P92_brought_into_existence', X, _],O1,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E48_Place_Name', X],O1,_,_) \ fact(['a1:E44_Place_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P143i_was_joined_by', X, Y],O1,_,_) \ fact(['a1:P11i_participated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E2_Temporal_Entity', X],O1,_,_), fact(['a1:E77_Persistent_Item', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P54i_is_current_permanent_location_of', _, X1],O1,_,_) \ fact(['a1:E19_Physical_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P145_separated', X, X2],O1,_,_), fact(['a1:P145_separated', X, X1],O2,_,_), fact(['a1:E86_Leaving', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', X, Y],O1,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Inauguration', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P125_used_object_of_type', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P25i_moved_by', _, X1],O1,_,_) \ fact(['a1:E9_Move', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P72i_is_language_of', Y, X],O1,_,_) \ fact(['a1:P72_has_language', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P72_has_language', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P72_has_language', Y, X],O1,_,_) \ fact(['a1:P72i_is_language_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P72i_is_language_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P101i_was_use_of', _, X1],O1,_,_) \ fact(['a1:E70_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P123i_resulted_from', X, _],O1,_,_) \ fact(['a1:E77_Persistent_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E66_Formation', X],O1,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P1i_identifies', X, _],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:SizeOrDuration', X],O1,_,_) \ fact(['a5:MediaTypeOrExtent', X],add,_,U) <=> member(del,[O1]) | fact(['a5:MediaTypeOrExtent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P92_brought_into_existence', Y, X],O1,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P92i_was_brought_into_existence_by', Y, X],O1,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:icqChatID', Y1, X],O1,_,_), fact(['a3:icqChatID', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:OnlineChatAccount', X],O1,_,_) \ fact(['a3:OnlineAccount', X],add,_,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P97_from_father', _, X1],O1,_,_) \ fact(['a1:E21_Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P65i_is_shown_by', _, X1],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P86i_contains', X, Y],O1,_,_), fact(['a1:P86i_contains', Y, Z],O2,_,_) \ fact(['a1:P86i_contains', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P86i_contains', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Coronation', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P148i_is_component_of', X, _],O1,_,_) \ fact(['a1:E89_Propositional_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P34i_was_assessed_by', _, X1],O1,_,_) \ fact(['a1:E14_Condition_Assessment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P49_has_former_or_current_keeper', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P43i_is_dimension_of', _, X1],O1,_,_) \ fact(['a1:E70_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P143i_was_joined_by', _, X1],O1,_,_) \ fact(['a1:E85_Joining', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E85_Joining', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P21_had_general_purpose', Y, X],O1,_,_) \ fact(['a1:P21i_was_purpose_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P21i_was_purpose_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P21i_was_purpose_of', Y, X],O1,_,_) \ fact(['a1:P21_had_general_purpose', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P21_had_general_purpose', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P87i_identifies', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Funeral', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P11i_participated_in', Y, X],O1,_,_) \ fact(['a1:P11_had_participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P11_had_participant', Y, X],O1,_,_) \ fact(['a1:P11i_participated_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P111_added', Y, X],O1,_,_) \ fact(['a1:P111i_was_added_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P111i_was_added_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P111i_was_added_by', Y, X],O1,_,_) \ fact(['a1:P111_added', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P111_added', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E73_Information_Object', X],O1,_,_) \ fact(['a1:P_E73_Information_Object', X, X],add,_,U) <=> member(del,[O1]) | fact(['a1:P_E73_Information_Object', X, X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P113_removed', X, _],O1,_,_) \ fact(['a1:E80_Part_Removal', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E80_Part_Removal', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P142i_was_used_in', X, Y],O1,_,_) \ fact(['a1:P16i_was_used_for', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:page', Y, X],O1,_,_) \ fact(['a3:topic', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:topic', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:topic', Y, X],O1,_,_) \ fact(['a3:page', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', X, Y],O1,_,_) \ fact(['a1:P94i_was_created_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P94i_was_created_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P101_had_as_general_use', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:homepage', X, Y],O1,_,_) \ fact(['a3:isPrimaryTopicOf', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:isPrimaryTopicOf', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P127i_has_narrower_term', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P25i_moved_by', Y, X],O1,_,_) \ fact(['a1:P25_moved', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P25_moved', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P25_moved', Y, X],O1,_,_) \ fact(['a1:P25i_moved_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P25i_moved_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P3_has_note', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P38_deassigned', X, Y],O1,_,_) \ fact(['a1:P141_assigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E42_Identifier', X],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P148_has_component', X, _],O1,_,_) \ fact(['a1:E89_Propositional_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P122_borders_with', Y, X],O1,_,_) \ fact(['a1:P122_borders_with', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P122_borders_with', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P59i_is_located_on_or_within', X, X2],O1,_,_), fact(['a1:P59i_is_located_on_or_within', X, X1],O2,_,_), fact(['a1:E53_Place', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P26i_was_destination_of', _, X1],O1,_,_) \ fact(['a1:E9_Move', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:accountServiceHomepage', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P68_foresees_use_of', Y, X],O1,_,_) \ fact(['a1:P68i_use_foreseen_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P68i_use_foreseen_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P68i_use_foreseen_by', Y, X],O1,_,_) \ fact(['a1:P68_foresees_use_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P68_foresees_use_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:eventInterval', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P128_carries', _, X1],O1,_,_) \ fact(['a1:E73_Information_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E65_Creation', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:mbox_sha1sum', _, X1],O1,_,_) \ fact(['rdfs:Literal', X1],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:interval', X, _],O1,_,_) \ fact(['a2:Relationship', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Relationship', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X, Y],O1,_,_), fact(['a1:P67_refers_to', Y, Z],O2,_,_) \ fact(['a1:P67_refers_to', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P67_refers_to', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E12_Production', X],O1,_,_) \ fact(['a1:E11_Modification', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P12i_was_present_at', X, _],O1,_,_) \ fact(['a1:E77_Persistent_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P48_has_preferred_identifier', X, X2],O1,_,_), fact(['a1:P48_has_preferred_identifier', X, X1],O2,_,_), fact(['a1:E1_CRM_Entity', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P148_has_component', _, X1],O1,_,_) \ fact(['a1:E89_Propositional_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P12_occurred_in_the_presence_of', _, X1],O1,_,_) \ fact(['a1:E77_Persistent_Item', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P31i_was_modified_by', X, _],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P94i_was_created_by', X, _],O1,_,_) \ fact(['a1:E28_Conceptual_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P107_has_current_or_former_member', X, _],O1,_,_) \ fact(['a1:E74_Group', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P103i_was_intention_of', X, _],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P12i_was_present_at', _, X1],O1,_,_) \ fact(['a1:E5_Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P42_assigned', X, Y],O1,_,_) \ fact(['a1:P141_assigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', X, _],O1,_,_) \ fact(['a1:E17_Type_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E17_Type_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P62i_is_depicted_by', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P4i_is_time-span_of', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P106i_forms_part_of', X, _],O1,_,_) \ fact(['a1:E90_Symbolic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E26_Physical_Feature', X],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyPrecedingEvent', X, Y],O1,_,_) \ fact(['a2:precedingEvent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:precedingEvent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Resignation', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:BarMitzvah', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E2_Temporal_Entity', X],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P123i_resulted_from', X, Y],O1,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E54_Dimension', X],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P131i_identifies', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Baptism', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P122_borders_with', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P94_has_created', X, Y],O1,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P115_finishes', X, Y],O1,_,_), fact(['a1:P115_finishes', Y, Z],O2,_,_) \ fact(['a1:P115_finishes', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P115_finishes', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:openid', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P1i_identifies', Y, X],O1,_,_) \ fact(['a1:P1_is_identified_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P1_is_identified_by', Y, X],O1,_,_) \ fact(['a1:P1i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P52_has_current_owner', X, Y],O1,_,_) \ fact(['a1:P51_has_former_or_current_owner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P102i_is_title_of', Y, X],O1,_,_) \ fact(['a1:P102_has_title', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P102_has_title', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P102_has_title', Y, X],O1,_,_) \ fact(['a1:P102i_is_title_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P102i_is_title_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P59_has_section', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P79_beginning_is_qualified_by', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:jabberID', Y1, X],O1,_,_), fact(['a3:jabberID', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P140_assigned_attribute_to', Y, X],O1,_,_) \ fact(['a1:P140i_was_attributed_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P140i_was_attributed_by', Y, X],O1,_,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98_brought_into_life', _, X1],O1,_,_) \ fact(['a1:E21_Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P8_took_place_on_or_within', X, _],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P8_took_place_on_or_within', _, X1],O1,_,_) \ fact(['a1:E19_Physical_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E22_Man-Made_Object', X],O1,_,_) \ fact(['a1:E19_Physical_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P114_is_equal_in_time_to', X, Y],O1,_,_), fact(['a1:P114_is_equal_in_time_to', Y, Z],O2,_,_) \ fact(['a1:P114_is_equal_in_time_to', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P114_is_equal_in_time_to', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E73_Information_Object', X0, X1],O1,_,_), fact(['a1:referredBySame', X1, X2],O2,_,_), fact(['a1:P_E73_Information_Object', X2, X3],O3,_,_) \ fact(['a1:relatedInformationObjects', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedInformationObjects', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Burial', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P140i_was_attributed_by', _, X1],O1,_,_) \ fact(['a1:E13_Attribute_Assignment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E53_Place', X],O1,_,_) \ fact(['a1:P_E53_Place', X, X],add,_,U) <=> member(del,[O1]) | fact(['a1:P_E53_Place', X, X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P23_transferred_title_from', Y, X],O1,_,_) \ fact(['a1:P23i_surrendered_title_through', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P23i_surrendered_title_through', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P23i_surrendered_title_through', Y, X],O1,_,_) \ fact(['a1:P23_transferred_title_from', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P23_transferred_title_from', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', X, Y],O1,_,_), fact(['a1:P27i_was_origin_of', Y, Z],O2,_,_) \ fact(['a1:P27i_was_origin_of', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P27i_was_origin_of', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P33i_was_used_by', X, _],O1,_,_) \ fact(['a1:E29_Design_or_Procedure', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P74i_is_current_or_former_residence_of', Y, X],O1,_,_) \ fact(['a1:P74_has_current_or_former_residence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P74_has_current_or_former_residence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P74_has_current_or_former_residence', Y, X],O1,_,_) \ fact(['a1:P74i_is_current_or_former_residence_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P74i_is_current_or_former_residence_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E90_Symbolic_Object', X],O1,_,_) \ fact(['a1:E28_Conceptual_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P107_has_current_or_former_member', Y, X],O1,_,_) \ fact(['a1:P107i_is_current_or_former_member_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P107i_is_current_or_former_member_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P107i_is_current_or_former_member_of', Y, X],O1,_,_) \ fact(['a1:P107_has_current_or_former_member', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P107_has_current_or_former_member', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P131i_identifies', X, Y],O1,_,_) \ fact(['a1:P1i_identifies', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:keywords', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P87_is_identified_by', _, X1],O1,_,_) \ fact(['a1:E44_Place_Appellation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P15i_influenced', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P109_has_current_or_former_curator', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P141i_was_assigned_by', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E16_Measurement', X],O1,_,_) \ fact(['a1:E13_Attribute_Assignment', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P124_transformed', _, X1],O1,_,_) \ fact(['a1:E77_Persistent_Item', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P120i_occurs_after', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E53_Place', X0, X1],O1,_,_), fact(['a1:P67_refers_to', X1, X2],O2,_,_), fact(['a1:P_E53_Place', X2, X3],O3,_,_) \ fact(['a1:relatedPlaces', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedPlaces', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:Agent', X],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Agent', X],O1,_,_) \ fact(['a5:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a5:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P62_depicts', X, _],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P65_shows_visual_item', _, X1],O1,_,_) \ fact(['a1:E36_Visual_Item', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:initiatingEvent', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P11i_participated_in', _, X1],O1,_,_) \ fact(['a1:E5_Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', X, Y],O1,_,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P136i_supported_type_creation', _, X1],O1,_,_) \ fact(['a1:E83_Type_Creation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E83_Type_Creation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E55_Type', X],O1,_,_) \ fact(['a1:E28_Conceptual_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:officiator', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:relatedPlaces', Y, X],O1,_,_) \ fact(['a1:relatedPlaces', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:relatedPlaces', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P147_curated', Y, X],O1,_,_) \ fact(['a1:P147i_was_curated_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P147i_was_curated_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P147i_was_curated_by', Y, X],O1,_,_) \ fact(['a1:P147_curated', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P147_curated', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P53_has_former_or_current_location', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Birth', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:keywords', X, Y],O1,_,_) \ fact(['a12:subject', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a12:subject', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P5_consists_of', X, _],O1,_,_) \ fact(['a1:E3_Condition_State', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:icqChatID', X, Y],O1,_,_) \ fact(['a3:nick', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P118i_is_overlapped_in_time_by', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P48_has_preferred_identifier', _, X1],O1,_,_) \ fact(['a1:E42_Identifier', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P44i_is_condition_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P69_is_associated_with', X, _],O1,_,_) \ fact(['a1:E29_Design_or_Procedure', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E11_Modification', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P93i_was_taken_out_of_existence_by', Y, X],O1,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P93_took_out_of_existence', Y, X],O1,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P109i_is_current_or_former_curator_of', _, X1],O1,_,_) \ fact(['a1:E78_Collection', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E78_Collection', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P76i_provides_access_to', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P94i_was_created_by', X, Y],O1,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E86_Leaving', X],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Document', X],O1,_,_), fact(['a3:Project', X],O2,_,_) \ fact(['owl:Nothing', X],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P20i_was_purpose_of', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Event', X],O1,_,_) \ fact(['a13:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a13:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:birthday', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P143_joined', X, _],O1,_,_) \ fact(['a1:E85_Joining', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E85_Joining', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P115_finishes', Y, X],O1,_,_) \ fact(['a1:P115i_is_finished_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P115i_is_finished_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P115i_is_finished_by', Y, X],O1,_,_) \ fact(['a1:P115_finishes', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P115_finishes', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P25i_moved_by', X, _],O1,_,_) \ fact(['a1:E19_Physical_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:witness', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E38_Image', X],O1,_,_) \ fact(['a1:E36_Visual_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P73_has_translation', X, _],O1,_,_) \ fact(['a1:E33_Linguistic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P26i_was_destination_of', X, Y],O1,_,_) \ fact(['a1:P7i_witnessed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P7i_witnessed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:weblog', Y1, X],O1,_,_), fact(['a3:weblog', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P17i_motivated', X, Y],O1,_,_) \ fact(['a1:P15i_influenced', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P142_used_constituent', _, X1],O1,_,_) \ fact(['a1:E41_Appellation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P125i_was_type_of_object_used_in', Y, X],O1,_,_) \ fact(['a1:P125_used_object_of_type', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P125_used_object_of_type', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P125_used_object_of_type', Y, X],O1,_,_) \ fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:workplaceHomepage', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P134i_was_continued_by', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E89_Propositional_Object', X],O1,_,_) \ fact(['a1:E28_Conceptual_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:skypeID', _, X1],O1,_,_) \ fact(['rdfs:Literal', X1],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:isPrimaryTopicOf', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P88_consists_of', Y, X],O1,_,_) \ fact(['a1:P88i_forms_part_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P88i_forms_part_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P88i_forms_part_of', Y, X],O1,_,_) \ fact(['a1:P88_consists_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P88_consists_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:relationship', Y, X],O1,_,_) \ fact(['a2:participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:participant', Y, X],O1,_,_) \ fact(['a2:relationship', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:relationship', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P21i_was_purpose_of', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P17_was_motivated_by', _, X1],O1,_,_) \ fact(['a1:E1_CRM_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P34_concerned', X, Y],O1,_,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P25_moved', X, _],O1,_,_) \ fact(['a1:E9_Move', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Accession', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:interest', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E58_Measurement_Unit', X],O1,_,_) \ fact(['a1:E55_Type', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P105i_has_right_on', Y, X],O1,_,_) \ fact(['a1:P105_right_held_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P105_right_held_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P105_right_held_by', Y, X],O1,_,_) \ fact(['a1:P105i_has_right_on', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P105i_has_right_on', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Assassination', X],O1,_,_) \ fact(['a2:Murder', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Murder', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', X, _],O1,_,_) \ fact(['a1:E12_Production', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E12_Production', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E35_Title', X],O1,_,_) \ fact(['a1:E33_Linguistic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:witness', X, Y],O1,_,_) \ fact(['a2:spectator', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:spectator', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E83_Type_Creation', X],O1,_,_) \ fact(['a1:E65_Creation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E65_Creation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, Y1],O1,_,_), fact(['a2:mother', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P32i_was_technique_of', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P65_shows_visual_item', X, Y],O1,_,_) \ fact(['a1:P128_carries', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P128_carries', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P69_is_associated_with', _, X1],O1,_,_) \ fact(['a1:E29_Design_or_Procedure', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P135_created_type', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P22_transferred_title_to', X, Y],O1,_,_) \ fact(['a1:P14_carried_out_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P49_has_former_or_current_keeper', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P104i_applies_to', X, _],O1,_,_) \ fact(['a1:E30_Right', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E30_Right', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P86i_contains', Y, X],O1,_,_) \ fact(['a1:P86_falls_within', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P86_falls_within', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P86_falls_within', Y, X],O1,_,_) \ fact(['a1:P86i_contains', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P86i_contains', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P11_had_participant', X, _],O1,_,_) \ fact(['a1:E5_Event', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P2i_is_type_of', Y, X],O1,_,_) \ fact(['a1:P2_has_type', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P2_has_type', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P2_has_type', Y, X],O1,_,_) \ fact(['a1:P2i_is_type_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P2i_is_type_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:workplaceHomepage', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E52_Time-Span', X],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', _, X1],O1,_,_) \ fact(['a1:E6_Destruction', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E6_Destruction', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P129_is_about', X, _],O1,_,_) \ fact(['a1:E89_Propositional_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P103i_was_intention_of', Y, X],O1,_,_) \ fact(['a1:P103_was_intended_for', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P103_was_intended_for', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P103_was_intended_for', Y, X],O1,_,_) \ fact(['a1:P103i_was_intention_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P103i_was_intention_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:birthday', X, Y1],O1,_,_), fact(['a3:birthday', X, Y2],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E34_Inscription', X],O1,_,_) \ fact(['a1:E33_Linguistic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P21_had_general_purpose', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E69_Death', X],O1,_,_) \ fact(['a1:E64_End_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E18_Physical_Thing', X],O1,_,_) \ fact(['a1:E72_Legal_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P_E53_Place', X0, X1],O1,_,_), fact(['a1:referToSame', X1, X2],O2,_,_), fact(['a1:P_E53_Place', X2, X3],O3,_,_) \ fact(['a1:relatedPlaces', X0, X3],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedPlaces', X0, X3],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P143_joined', X, Y],O1,_,_) \ fact(['a1:P11_had_participant', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P35_has_identified', X, Y],O1,_,_) \ fact(['a1:P141_assigned', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:employer', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P145_separated', X, _],O1,_,_) \ fact(['a1:E86_Leaving', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E86_Leaving', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', X, X2],O1,_,_), fact(['a1:P98i_was_born', X, X1],O2,_,_), fact(['a1:E21_Person', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P114_is_equal_in_time_to', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P20i_was_purpose_of', X, _],O1,_,_) \ fact(['a1:E5_Event', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P38i_was_deassigned_by', _, X1],O1,_,_) \ fact(['a1:E15_Identifier_Assignment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P83_had_at_least_duration', _, X1],O1,_,_) \ fact(['a1:E54_Dimension', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:page', _, X1],O1,_,_) \ fact(['a3:Document', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:precedingEvent', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P134i_was_continued_by', X, Y],O1,_,_) \ fact(['a1:P15i_influenced', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E67_Birth', X],O1,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P133_is_separated_from', _, X1],O1,_,_) \ fact(['a1:E4_Period', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:pastProject', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:concludingEvent', X, Y],O1,_,_) \ fact(['owl:differentFrom', X, Y],add,_,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P19_was_intended_use_of', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E35_Title', X],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98_brought_into_life', X, _],O1,_,_) \ fact(['a1:E67_Birth', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P68_foresees_use_of', _, X1],O1,_,_) \ fact(['a1:E57_Material', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P33_used_specific_technique', X, Y],O1,_,_) \ fact(['a1:P16_used_specific_object', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:precedingEvent', _, X1],O1,_,_) \ fact(['a2:Event', X1],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P17i_motivated', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E68_Dissolution', X],O1,_,_) \ fact(['a1:E64_End_of_Existence', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],O1,_,_) \ fact(['a1:P12i_was_present_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P52i_is_current_owner_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P120_occurs_before', X, Y],O1,_,_), fact(['a1:P120_occurs_before', Y, Z],O2,_,_) \ fact(['a1:P120_occurs_before', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P120_occurs_before', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P89i_contains', Y, X],O1,_,_) \ fact(['a1:P89_falls_within', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P89_falls_within', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P89_falls_within', Y, X],O1,_,_) \ fact(['a1:P89i_contains', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P89i_contains', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P121_overlaps_with', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P88_consists_of', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P129_is_about', Y, X],O1,_,_) \ fact(['a1:P129i_is_subject_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P129i_is_subject_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P129i_is_subject_of', Y, X],O1,_,_) \ fact(['a1:P129_is_about', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P129_is_about', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:state', X, Y],O1,_,_) \ fact(['a2:agent', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P50i_is_current_keeper_of', X, Y],O1,_,_) \ fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:precedingEvent', X, Y],O1,_,_), fact(['a2:precedingEvent', Y, Z],O2,_,_) \ fact(['a2:precedingEvent', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a2:precedingEvent', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:member', X, _],O1,_,_) \ fact(['a3:Group', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Group', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['rdfs:Class', X],O1,_,_) \ fact(['rdfs:Resource', X],add,_,U) <=> member(del,[O1]) | fact(['rdfs:Resource', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P4i_is_time-span_of', Y, X],O1,_,_) \ fact(['a1:P4_has_time-span', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P4_has_time-span', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P4_has_time-span', Y, X],O1,_,_) \ fact(['a1:P4i_is_time-span_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P4i_is_time-span_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P105_right_held_by', X, _],O1,_,_) \ fact(['a1:E72_Legal_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:aimChatID', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P122_borders_with', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:OnlineGamingAccount', X],O1,_,_) \ fact(['a3:OnlineAccount', X],add,_,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P26_moved_to', X, Y],O1,_,_) \ fact(['a1:P7_took_place_at', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P7_took_place_at', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P31_has_modified', _, X1],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P83_had_at_least_duration', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:GroupEvent', X],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P86_falls_within', _, X1],O1,_,_) \ fact(['a1:E52_Time-Span', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:yahooChatID', Y1, X],O1,_,_), fact(['a3:yahooChatID', Y2, X],O2,_,_) \ fact(['owl:sameAs', Y1, Y2],add,_,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P106i_forms_part_of', Y, X],O1,_,_) \ fact(['a1:P106_is_composed_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P106_is_composed_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P106_is_composed_of', Y, X],O1,_,_) \ fact(['a1:P106i_forms_part_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P106i_forms_part_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P40i_was_observed_in', X, Y],O1,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P133_is_separated_from', Y, X],O1,_,_) \ fact(['a1:P133_is_separated_from', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P133_is_separated_from', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P130_shows_features_of', X, _],O1,_,_) \ fact(['a1:E70_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Interval', X],O1,_,_) \ fact(['a14:ProperInterval', X],add,_,U) <=> member(del,[O1]) | fact(['a14:ProperInterval', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P52i_is_current_owner_of', Y, X],O1,_,_) \ fact(['a1:P52_has_current_owner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P52_has_current_owner', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P52_has_current_owner', Y, X],O1,_,_) \ fact(['a1:P52i_is_current_owner_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P52i_is_current_owner_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P100i_died_in', _, X1],O1,_,_) \ fact(['a1:E69_Death', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E69_Death', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:maker', Y, X],O1,_,_) \ fact(['a3:made', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:made', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:made', Y, X],O1,_,_) \ fact(['a3:maker', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a3:maker', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P124_transformed', X, _],O1,_,_) \ fact(['a1:E81_Transformation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E81_Transformation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E82_Actor_Appellation', X],O1,_,_) \ fact(['a1:E41_Appellation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P32_used_general_technique', _, X1],O1,_,_) \ fact(['a1:E55_Type', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P123i_resulted_from', Y, X],O1,_,_) \ fact(['a1:P123_resulted_in', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P123_resulted_in', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P123_resulted_in', Y, X],O1,_,_) \ fact(['a1:P123i_resulted_from', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P123i_resulted_from', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P10i_contains', X, Y],O1,_,_), fact(['a1:P10i_contains', Y, Z],O2,_,_) \ fact(['a1:P10i_contains', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P10i_contains', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P51i_is_former_or_current_owner_of', Y, X],O1,_,_) \ fact(['a1:P51_has_former_or_current_owner', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P51_has_former_or_current_owner', Y, X],O1,_,_) \ fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P142i_was_used_in', _, X1],O1,_,_) \ fact(['a1:E15_Identifier_Assignment', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Death', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P98_brought_into_life', X, Y],O1,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P93i_was_taken_out_of_existence_by', X, _],O1,_,_) \ fact(['a1:E77_Persistent_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', Y, X],O1,_,_) \ fact(['a1:P39i_was_measured_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P39i_was_measured_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P39i_was_measured_by', Y, X],O1,_,_) \ fact(['a1:P39_measured', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P39_measured', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P116i_is_started_by', _, X1],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E41_Appellation', X],O1,_,_) \ fact(['a1:E90_Symbolic_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P106i_forms_part_of', X, Y],O1,_,_), fact(['a1:P106i_forms_part_of', Y, Z],O2,_,_) \ fact(['a1:P106i_forms_part_of', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P106i_forms_part_of', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P50_has_current_keeper', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P9_consists_of', X, _],O1,_,_) \ fact(['a1:E4_Period', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P144_joined_with', _, X1],O1,_,_) \ fact(['a1:E74_Group', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:publications', X, _],O1,_,_) \ fact(['a3:Person', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P46_is_composed_of', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P59_has_section', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E36_Visual_Item', X],O1,_,_) \ fact(['a1:E73_Information_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P112i_was_diminished_by', _, X1],O1,_,_) \ fact(['a1:E80_Part_Removal', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E80_Part_Removal', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P11i_participated_in', X, _],O1,_,_) \ fact(['a1:E39_Actor', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P78_is_identified_by', X, _],O1,_,_) \ fact(['a1:E52_Time-Span', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P34_concerned', _, X1],O1,_,_) \ fact(['a1:E18_Physical_Thing', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P112i_was_diminished_by', X, _],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P136i_supported_type_creation', X, _],O1,_,_) \ fact(['a1:E1_CRM_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P144i_gained_member_by', Y, X],O1,_,_) \ fact(['a1:P144_joined_with', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P144_joined_with', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P144_joined_with', Y, X],O1,_,_) \ fact(['a1:P144i_gained_member_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P144i_gained_member_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Cremation', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P119_meets_in_time_with', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Marriage', X],O1,_,_) \ fact(['a7:WeddingEvent_Generic', X],add,_,U) <=> member(del,[O1]) | fact(['a7:WeddingEvent_Generic', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a7:WeddingEvent_Generic', X],O1,_,_) \ fact(['a2:Marriage', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Marriage', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', _, X1],O1,_,_) \ fact(['a1:E7_Activity', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:Image', X],O1,_,_) \ fact(['a3:Document', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Document', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P143_joined', Y, X],O1,_,_) \ fact(['a1:P143i_was_joined_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P143i_was_joined_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P143i_was_joined_by', Y, X],O1,_,_) \ fact(['a1:P143_joined', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P143_joined', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P24i_changed_ownership_through', _, X1],O1,_,_) \ fact(['a1:E8_Acquisition', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P115i_is_finished_by', X, _],O1,_,_) \ fact(['a1:E2_Temporal_Entity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P103_was_intended_for', X, _],O1,_,_) \ fact(['a1:E71_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P53i_is_former_or_current_location_of', X, _],O1,_,_) \ fact(['a1:E53_Place', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P128_carries', X, _],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a5:LicenseDocument', X],O1,_,_) \ fact(['a5:RightsStatement', X],add,_,U) <=> member(del,[O1]) | fact(['a5:RightsStatement', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P68_foresees_use_of', X, _],O1,_,_) \ fact(['a1:E29_Design_or_Procedure', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P89i_contains', _, X1],O1,_,_) \ fact(['a1:E53_Place', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P20_had_specific_purpose', X, _],O1,_,_) \ fact(['a1:E7_Activity', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P46_is_composed_of', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P7i_witnessed', _, X1],O1,_,_) \ fact(['a1:E4_Period', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Naturalization', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P23i_surrendered_title_through', X, Y],O1,_,_) \ fact(['a1:P14i_performed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E30_Right', X],O1,_,_) \ fact(['a1:E89_Propositional_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P9_consists_of', _, X1],O1,_,_) \ fact(['a1:E4_Period', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P106_is_composed_of', _, X1],O1,_,_) \ fact(['a1:E90_Symbolic_Object', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:tipjar', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:account', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E70_Thing', X],O1,_,_) \ fact(['a1:E77_Persistent_Item', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P22i_acquired_title_through', X, Y],O1,_,_) \ fact(['a1:P14i_performed', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', X, _],O1,_,_) \ fact(['a1:E9_Move', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P105_right_held_by', _, X1],O1,_,_) \ fact(['a1:E39_Actor', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a3:icqChatID', X, _],O1,_,_) \ fact(['a3:Agent', X],add,_,U) <=> member(del,[O1]) | fact(['a3:Agent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E78_Collection', X],O1,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', X, X2],O1,_,_), fact(['a1:P13i_was_destroyed_by', X, X1],O2,_,_), fact(['a1:E18_Physical_Thing', X],O3,_,_) \ fact(['owl:sameAs', X1, X2],add,_,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P136_was_based_on', X, Y],O1,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', Y, X],O1,_,_) \ fact(['a1:P16_used_specific_object', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', Y, X],O1,_,_) \ fact(['a1:P16i_was_used_for', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P88_consists_of', X, Y],O1,_,_), fact(['a1:P88_consists_of', Y, Z],O2,_,_) \ fact(['a1:P88_consists_of', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P88_consists_of', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a15:Performance', X],O1,_,_) \ fact(['a2:Performance', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Performance', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Performance', X],O1,_,_) \ fact(['a15:Performance', X],add,_,U) <=> member(del,[O1]) | fact(['a15:Performance', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P54_has_current_permanent_location', X, _],O1,_,_) \ fact(['a1:E19_Physical_Object', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P88i_forms_part_of', X, Y],O1,_,_), fact(['a1:P88i_forms_part_of', Y, Z],O2,_,_) \ fact(['a1:P88i_forms_part_of', X, Z],add,_,U) <=> member(del,[O1,O2]) | fact(['a1:P88i_forms_part_of', X, Z],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:E25_Man-Made_Feature', X],O1,_,_) \ fact(['a1:E26_Physical_Feature', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E26_Physical_Feature', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P94_has_created', X, _],O1,_,_) \ fact(['a1:E65_Creation', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E65_Creation', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P128_carries', Y, X],O1,_,_) \ fact(['a1:P128i_is_carried_by', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P128i_is_carried_by', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P128i_is_carried_by', Y, X],O1,_,_) \ fact(['a1:P128_carries', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P128_carries', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:Emigration', X],O1,_,_) \ fact(['a2:IndividualEvent', X],add,_,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P112_diminished', X, Y],O1,_,_) \ fact(['a1:P31_has_modified', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P33i_was_used_by', X, Y],O1,_,_) \ fact(['a1:P16i_was_used_for', X, Y],add,_,U) <=> member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Y],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P83i_was_minimum_duration_of', _, X1],O1,_,_) \ fact(['a1:E52_Time-Span', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:organization', X, _],O1,_,_) \ fact(['a2:Event', X],add,_,U) <=> member(del,[O1]) | fact(['a2:Event', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P113i_was_removed_by', X, _],O1,_,_) \ fact(['a1:E18_Physical_Thing', X],add,_,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk,_,U), applied_rules(1,del).
phase(1), fact(['a2:child', _, X1],O1,_,_) \ fact(['a3:Person', X1],add,_,U) <=> member(del,[O1]) | fact(['a3:Person', X1],chk,_,U), applied_rules(1,del).
phase(1), fact(['a1:P78_is_identified_by', _, X1],O1,_,_) \ fact(['a1:E49_Time_Appellation', X1],add,_,U) <=> member(del,[O1]) | fact(['a1:E49_Time_Appellation', X1],chk,_,U), applied_rules(1,del).

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
fact(['a1:P22i_acquired_title_through', _, X1],prv,_,_) \ fact(['a1:E8_Acquisition', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E8_Acquisition', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P24_transferred_title_of', X, _],prv,_,_) \ fact(['a1:E8_Acquisition', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E8_Acquisition', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P110i_was_augmented_by', _, X1],prv,_,_) \ fact(['a1:E79_Part_Addition', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E79_Part_Addition', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P41_classified', X, X2],prv,_,_), fact(['a1:P41_classified', X, X1],prv,_,_), fact(['a1:E17_Type_Assignment', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P33_used_specific_technique', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P116_starts', X, Y],prv,_,_), fact(['a1:P116_starts', Y, Z],prv,_,_) \ fact(['a1:P116_starts', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P116_starts', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P124i_was_transformed_by', _, X1],prv,_,_) \ fact(['a1:E81_Transformation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E81_Transformation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P104_is_subject_to', X, _],prv,_,_) \ fact(['a1:E72_Legal_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E72_Legal_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P114_is_equal_in_time_to', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P127_has_broader_term', Y, X],prv,_,_) \ fact(['a1:P127i_has_narrower_term', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P127i_has_narrower_term', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P127i_has_narrower_term', Y, X],prv,_,_) \ fact(['a1:P127_has_broader_term', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P127_has_broader_term', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:followingEvent', X, Y],prv,_,_), fact(['a2:followingEvent', Y, Z],prv,_,_) \ fact(['a2:followingEvent', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:followingEvent', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:E34_Inscription', X],prv,M1,_) \ fact(['a1:E37_Mark', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E37_Mark', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P94i_was_created_by', _, X1],prv,_,_) \ fact(['a1:E65_Creation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E65_Creation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:aimChatID', _, X1],prv,M1,_) \ fact(['rdfs:Literal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Literal', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E7_Activity', X],prv,_,_) \ fact(['a1:E5_Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:depiction', _, X1],prv,_,_) \ fact(['a3:Image', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Image', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P23_transferred_title_from', X, _],prv,_,_) \ fact(['a1:E8_Acquisition', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E8_Acquisition', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Murder', X],prv,_,_) \ fact(['a2:Death', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Death', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E14_Condition_Assessment', X],prv,_,_) \ fact(['a1:E13_Attribute_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E13_Attribute_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P108_has_produced', X, Y],prv,_,_) \ fact(['a1:P31_has_modified', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P31_has_modified', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P16i_was_used_for', X, Y],prv,_,_) \ fact(['a1:P15i_influenced', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15i_influenced', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P123i_resulted_from', _, X1],prv,_,_) \ fact(['a1:E81_Transformation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E81_Transformation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:homepage', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P96_by_mother', Y, X],prv,_,_) \ fact(['a1:P96i_gave_birth', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P96i_gave_birth', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P96i_gave_birth', Y, X],prv,_,_) \ fact(['a1:P96_by_mother', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P96_by_mother', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P100_was_death_of', X, _],prv,_,_) \ fact(['a1:E69_Death', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E69_Death', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P41i_was_classified_by', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P71i_is_listed_in', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P41i_was_classified_by', Y, X],prv,_,_) \ fact(['a1:P41_classified', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P41_classified', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P41_classified', Y, X],prv,_,_) \ fact(['a1:P41i_was_classified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P41i_was_classified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P14_carried_out_by', X, Y],prv,_,_) \ fact(['a1:P11_had_participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11_had_participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P93_took_out_of_existence', X, Y],prv,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P54_has_current_permanent_location', X, X2],prv,_,_), fact(['a1:P54_has_current_permanent_location', X, X1],prv,_,_), fact(['a1:E19_Physical_Object', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P146_separated_from', X, Y],prv,_,_) \ fact(['a1:P11_had_participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11_had_participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P17_was_motivated_by', Y, X],prv,_,_) \ fact(['a1:P17i_motivated', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P17i_motivated', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P17i_motivated', Y, X],prv,_,_) \ fact(['a1:P17_was_motivated_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P17_was_motivated_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P39i_was_measured_by', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P113_removed', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P73_has_translation', Y, X],prv,_,_) \ fact(['a1:P73i_is_translation_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P73i_is_translation_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P73i_is_translation_of', Y, X],prv,_,_) \ fact(['a1:P73_has_translation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P73_has_translation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P2i_is_type_of', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P141i_was_assigned_by', _, X1],prv,_,_) \ fact(['a1:E13_Attribute_Assignment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E13_Attribute_Assignment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P102_has_title', X, Y],prv,_,_) \ fact(['a1:P1_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P38_deassigned', _, X1],prv,_,_) \ fact(['a1:E42_Identifier', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E42_Identifier', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P54_has_current_permanent_location', Y, X],prv,_,_) \ fact(['a1:P54i_is_current_permanent_location_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P54i_is_current_permanent_location_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P54i_is_current_permanent_location_of', Y, X],prv,_,_) \ fact(['a1:P54_has_current_permanent_location', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P54_has_current_permanent_location', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E21_Person', X],prv,_,_) \ fact(['a1:E20_Biological_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E20_Biological_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['rdfs:Container', X],prv,M1,_) \ fact(['rdfs:Resource', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Resource', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:publications', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:relatedInformationObjects', Y, X],prv,_,_) \ fact(['a1:relatedInformationObjects', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedInformationObjects', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P126_employed', X, _],prv,_,_) \ fact(['a1:E11_Modification', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E11_Modification', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:death', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a2:Divorce', X],prv,M1,_) \ fact(['a2:GroupEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:GroupEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P108i_was_produced_by', X, _],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P136_was_based_on', X, _],prv,_,_) \ fact(['a1:E83_Type_Creation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E83_Type_Creation', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Graduation', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P29i_received_custody_through', Y, X],prv,_,_) \ fact(['a1:P29_custody_received_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P29_custody_received_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P29_custody_received_by', Y, X],prv,_,_) \ fact(['a1:P29i_received_custody_through', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P29i_received_custody_through', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P10_falls_within', Y, X],prv,_,_) \ fact(['a1:P10i_contains', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P10i_contains', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P10i_contains', Y, X],prv,_,_) \ fact(['a1:P10_falls_within', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P10_falls_within', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P55_has_current_location', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P142_used_constituent', X, Y],prv,_,_) \ fact(['a1:P16_used_specific_object', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P16_used_specific_object', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P147i_was_curated_by', X, _],prv,_,_) \ fact(['a1:E78_Collection', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E78_Collection', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E53_Place', X],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P72i_is_language_of', _, X1],prv,_,_) \ fact(['a1:E33_Linguistic_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E33_Linguistic_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P70_documents', X, Y],prv,_,_) \ fact(['a1:P67_refers_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67_refers_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P124_transformed', X, Y],prv,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93_took_out_of_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:Person', X],prv,_,_) \ fact(['a4:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a4:Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,_) \ fact(['a1:E71_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E71_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P148i_is_component_of', Y, X],prv,_,_) \ fact(['a1:P148_has_component', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P148_has_component', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P148_has_component', Y, X],prv,_,_) \ fact(['a1:P148i_is_component_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P148i_is_component_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P15_was_influenced_by', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P107_has_current_or_former_member', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:made', X, _],prv,_,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P30_transferred_custody_of', Y, X],prv,_,_) \ fact(['a1:P30i_custody_transferred_through', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P30i_custody_transferred_through', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P30i_custody_transferred_through', Y, X],prv,_,_) \ fact(['a1:P30_transferred_custody_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P30_transferred_custody_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P125_used_object_of_type', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:birth', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E65_Creation', X],prv,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E63_Beginning_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E81_Transformation', X],prv,_,_) \ fact(['a1:E64_End_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E64_End_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P24i_changed_ownership_through', Y, X],prv,_,_) \ fact(['a1:P24_transferred_title_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P24_transferred_title_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P24_transferred_title_of', Y, X],prv,_,_) \ fact(['a1:P24i_changed_ownership_through', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P24i_changed_ownership_through', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:Annulment', X],prv,M1,_) \ fact(['a2:GroupEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:GroupEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:Promotion', X],prv,M1,_) \ fact(['a2:PositionChange', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:PositionChange', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P31_has_modified', X, Y],prv,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:Ordination', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P130_shows_features_of', _, X1],prv,_,_) \ fact(['a1:E70_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P118_overlaps_in_time_with', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P144i_gained_member_by', _, X1],prv,_,_) \ fact(['a1:E85_Joining', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E85_Joining', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P124i_was_transformed_by', X, Y],prv,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P15_was_influenced_by', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E79_Part_Addition', X],prv,_,_), fact(['a1:E80_Part_Removal', X],prv,_,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:Nothing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P135_created_type', X, Y],prv,_,_) \ fact(['a1:P94_has_created', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P94_has_created', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P7_took_place_at', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a5:Jurisdiction', X],prv,M1,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:LocationPeriodOrJurisdiction', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P56i_is_found_on', X, _],prv,_,_) \ fact(['a1:E26_Physical_Feature', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E26_Physical_Feature', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P1_is_identified_by', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P126i_was_employed_in', Y, X],prv,_,_) \ fact(['a1:P126_employed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P126_employed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P126_employed', Y, X],prv,_,_) \ fact(['a1:P126i_was_employed_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P126i_was_employed_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:principal', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:myersBriggs', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:Demotion', X],prv,M1,_) \ fact(['a2:PositionChange', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:PositionChange', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:relationship', X, _],prv,_,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P112_diminished', Y, X],prv,_,_) \ fact(['a1:P112i_was_diminished_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P112i_was_diminished_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P112i_was_diminished_by', Y, X],prv,_,_) \ fact(['a1:P112_diminished', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P112_diminished', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:openid', X, Y],prv,M1,_) \ fact(['a3:isPrimaryTopicOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:isPrimaryTopicOf', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P141_assigned', Y, X],prv,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141i_was_assigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P141i_was_assigned_by', Y, X],prv,_,_) \ fact(['a1:P141_assigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141_assigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P44_has_condition', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P45_consists_of', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P50i_is_current_keeper_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P26_moved_to', Y, X],prv,_,_) \ fact(['a1:P26i_was_destination_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P26i_was_destination_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P26i_was_destination_of', Y, X],prv,_,_) \ fact(['a1:P26_moved_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P26_moved_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:img', X, Y],prv,M1,_) \ fact(['a3:depiction', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:depiction', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P24_transferred_title_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P133_is_separated_from', X, _],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P94_has_created', Y, X],prv,_,_) \ fact(['a1:P94i_was_created_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P94i_was_created_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P94i_was_created_by', Y, X],prv,_,_) \ fact(['a1:P94_has_created', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P94_has_created', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P67i_is_referred_to_by', _, X1],prv,_,_) \ fact(['a1:E89_Propositional_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P9_consists_of', Y, X],prv,_,_) \ fact(['a1:P9i_forms_part_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P9i_forms_part_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P9i_forms_part_of', Y, X],prv,_,_) \ fact(['a1:P9_consists_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P9_consists_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P51_has_former_or_current_owner', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P68i_use_foreseen_by', X, _],prv,_,_) \ fact(['a1:E57_Material', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E57_Material', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:IndividualEvent', X],prv,_,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P138i_has_representation', Y, X],prv,_,_) \ fact(['a1:P138_represents', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P138_represents', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P138_represents', Y, X],prv,_,_) \ fact(['a1:P138i_has_representation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P138i_has_representation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P51_has_former_or_current_owner', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:Organization', X],prv,M1,_), fact(['a3:Person', X],prv,M2,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:Organization',M1),('a3:Person',M2)],M), fact(['owl:Nothing', X],prv,M,U), applied_rules(1,fwd).
fact(['a2:state', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:father', X, Y],prv,M1,_) \ fact(['a6:childOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a6:childOf', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P55i_currently_holds', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P19_was_intended_use_of', _, X1],prv,_,_) \ fact(['a1:E71_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E71_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E47_Spatial_Coordinates', X],prv,M1,_) \ fact(['a1:E44_Place_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E44_Place_Appellation', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:workInfoHomepage', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a3:depicts', Y, X],prv,_,_) \ fact(['a3:depiction', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:depiction', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:depiction', Y, X],prv,_,_) \ fact(['a3:depicts', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:depicts', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['rdfs:Literal', X],prv,_,_) \ fact(['rdfs:Resource', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Resource', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P52_has_current_owner', X, Y],prv,_,_) \ fact(['a1:P105_right_held_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P105_right_held_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:concurrentEvent', _, X1],prv,_,_) \ fact(['a2:Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P58_has_section_definition', _, X1],prv,_,_) \ fact(['a1:E46_Section_Definition', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E46_Section_Definition', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P98i_was_born', X, _],prv,_,_) \ fact(['a1:E21_Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E21_Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:surname', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P56i_is_found_on', _, X1],prv,_,_) \ fact(['a1:E19_Physical_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P144_joined_with', X, _],prv,_,_) \ fact(['a1:E85_Joining', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E85_Joining', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P130i_features_are_also_found_on', X, _],prv,_,_) \ fact(['a1:E70_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:event', X, _],prv,_,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P43_has_dimension', X, _],prv,_,_) \ fact(['a1:E70_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P56_bears_feature', Y, X],prv,_,_) \ fact(['a1:P56i_is_found_on', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P56i_is_found_on', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P56i_is_found_on', Y, X],prv,_,_) \ fact(['a1:P56_bears_feature', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P56_bears_feature', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P83_had_at_least_duration', X, X2],prv,_,_), fact(['a1:P83_had_at_least_duration', X, X1],prv,_,_), fact(['a1:E52_Time-Span', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a2:participant', X, _],prv,_,_) \ fact(['a2:Relationship', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Relationship', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P140_assigned_attribute_to', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P4_has_time-span', _, X1],prv,_,_) \ fact(['a1:E52_Time-Span', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13_destroyed', Y, X],prv,_,_) \ fact(['a1:P13i_was_destroyed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P13i_was_destroyed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13i_was_destroyed_by', Y, X],prv,_,_) \ fact(['a1:P13_destroyed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P13_destroyed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P107i_is_current_or_former_member_of', _, X1],prv,_,_) \ fact(['a1:E74_Group', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E12_Production', X],prv,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E63_Beginning_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:employer', X, Y],prv,M1,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E15_Identifier_Assignment', X],prv,_,_) \ fact(['a1:E13_Attribute_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E13_Attribute_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P117_occurs_during', X, Y],prv,_,_), fact(['a1:P117_occurs_during', Y, Z],prv,_,_) \ fact(['a1:P117_occurs_during', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P117_occurs_during', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:E63_Beginning_of_Existence', X],prv,_,_) \ fact(['a1:E5_Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P117i_includes', Y, X],prv,_,_) \ fact(['a1:P117_occurs_during', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P117_occurs_during', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P117_occurs_during', Y, X],prv,_,_) \ fact(['a1:P117i_includes', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P117i_includes', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P10i_contains', X, _],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P120i_occurs_after', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P28_custody_surrendered_by', X, Y],prv,_,_) \ fact(['a1:P14_carried_out_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14_carried_out_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P84i_was_maximum_duration_of', _, X1],prv,_,_) \ fact(['a1:E52_Time-Span', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P37i_was_assigned_by', _, X1],prv,_,_) \ fact(['a1:E15_Identifier_Assignment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E15_Identifier_Assignment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P39_measured', X, X2],prv,_,_), fact(['a1:P39_measured', X, X1],prv,_,_), fact(['a1:E16_Measurement', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P147_curated', _, X1],prv,_,_) \ fact(['a1:E78_Collection', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E78_Collection', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99i_was_dissolved_by', _, X1],prv,_,_) \ fact(['a1:E68_Dissolution', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E68_Dissolution', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P65i_is_shown_by', Y, X],prv,_,_) \ fact(['a1:P65_shows_visual_item', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P65_shows_visual_item', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P65_shows_visual_item', Y, X],prv,_,_) \ fact(['a1:P65i_is_shown_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P65i_is_shown_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P56_bears_feature', X, _],prv,_,_) \ fact(['a1:E19_Physical_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E90_Symbolic_Object', X],prv,_,_) \ fact(['a1:E72_Legal_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E72_Legal_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P120_occurs_before', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E85_Joining', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P58_has_section_definition', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P146i_lost_member_by', _, X1],prv,_,_) \ fact(['a1:E86_Leaving', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E86_Leaving', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P8i_witnessed', _, X1],prv,_,_) \ fact(['a1:E4_Period', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P37_assigned', X, _],prv,_,_) \ fact(['a1:E15_Identifier_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E15_Identifier_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P118_overlaps_in_time_with', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E4_Period', X],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Event', X],prv,_,_) \ fact(['a7:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a7:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:officiator', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P62i_is_depicted_by', _, X1],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P72_has_language', _, X1],prv,_,_) \ fact(['a1:E56_Language', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E56_Language', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P138_represents', X, Y],prv,_,_) \ fact(['a1:P67_refers_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67_refers_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P70i_is_documented_in', _, X1],prv,_,_) \ fact(['a1:E31_Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E31_Document', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P32_used_general_technique', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:aimChatID', X, Y],prv,M1,_) \ fact(['a3:nick', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:nick', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P105i_has_right_on', _, X1],prv,_,_) \ fact(['a1:E72_Legal_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E72_Legal_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:age', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P100_was_death_of', Y, X],prv,_,_) \ fact(['a1:P100i_died_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P100i_died_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P100i_died_in', Y, X],prv,_,_) \ fact(['a1:P100_was_death_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P100_was_death_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:skypeID', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:participant', X, Y],prv,_,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P11_had_participant', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:father', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P82_at_some_time_within', X, _],prv,M1,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P31i_was_modified_by', _, X1],prv,_,_) \ fact(['a1:E11_Modification', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E11_Modification', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:gender', X, Y1],prv,M1,_), fact(['a3:gender', X, Y2],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:gender',M1),('a3:gender',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:relatedPlaces', X, Y],prv,_,_), fact(['a1:relatedPlaces', Y, Z],prv,_,_) \ fact(['a1:relatedPlaces', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedPlaces', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P141_assigned', X, _],prv,_,_) \ fact(['a1:E13_Attribute_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E13_Attribute_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:Document', X],prv,M1,_), fact(['a3:Organization', X],prv,M2,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:Document',M1),('a3:Organization',M2)],M), fact(['owl:Nothing', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:P72_has_language', X, _],prv,_,_) \ fact(['a1:E33_Linguistic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E33_Linguistic_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P105i_has_right_on', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P97_from_father', X, _],prv,_,_) \ fact(['a1:E67_Birth', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E67_Birth', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P110i_was_augmented_by', X, _],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P136_was_based_on', Y, X],prv,_,_) \ fact(['a1:P136i_supported_type_creation', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P136i_supported_type_creation', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P136i_supported_type_creation', Y, X],prv,_,_) \ fact(['a1:P136_was_based_on', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P136_was_based_on', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P22i_acquired_title_through', Y1, X],prv,_,_), fact(['a1:P22i_acquired_title_through', Y2, X],prv,_,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', Y1, Y2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P100_was_death_of', X, Y],prv,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93_took_out_of_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P45_consists_of', Y, X],prv,_,_) \ fact(['a1:P45i_is_incorporated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P45i_is_incorporated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P45i_is_incorporated_in', Y, X],prv,_,_) \ fact(['a1:P45_consists_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P45_consists_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:jabberID', _, X1],prv,M1,_) \ fact(['rdfs:Literal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Literal', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P78i_identifies', _, X1],prv,_,_) \ fact(['a1:E52_Time-Span', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:primaryTopic', X, _],prv,_,_) \ fact(['a3:Document', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P53_has_former_or_current_location', Y, X],prv,_,_) \ fact(['a1:P53i_is_former_or_current_location_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P53i_is_former_or_current_location_of', Y, X],prv,_,_) \ fact(['a1:P53_has_former_or_current_location', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P53_has_former_or_current_location', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P37_assigned', Y, X],prv,_,_) \ fact(['a1:P37i_was_assigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P37i_was_assigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P37i_was_assigned_by', Y, X],prv,_,_) \ fact(['a1:P37_assigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P37_assigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:lastName', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P84i_was_maximum_duration_of', X, _],prv,_,_) \ fact(['a1:E54_Dimension', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P32_used_general_technique', X, Y],prv,_,_) \ fact(['a1:P125_used_object_of_type', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P125_used_object_of_type', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P32_used_general_technique', Y, X],prv,_,_) \ fact(['a1:P32i_was_technique_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P32i_was_technique_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P32i_was_technique_of', Y, X],prv,_,_) \ fact(['a1:P32_used_general_technique', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P32_used_general_technique', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P59i_is_located_on_or_within', Y, X],prv,_,_) \ fact(['a1:P59_has_section', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P59_has_section', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P59_has_section', Y, X],prv,_,_) \ fact(['a1:P59i_is_located_on_or_within', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P59i_is_located_on_or_within', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:mbox', Y1, X],prv,M1,_), fact(['a3:mbox', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:mbox',M1),('a3:mbox',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a2:Marriage', X],prv,_,_) \ fact(['a2:GroupEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:GroupEvent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E79_Part_Addition', X],prv,_,_) \ fact(['a1:E11_Modification', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E11_Modification', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P35_has_identified', Y, X],prv,_,_) \ fact(['a1:P35i_was_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P35i_was_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P35i_was_identified_by', Y, X],prv,_,_) \ fact(['a1:P35_has_identified', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P35_has_identified', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:focus', X, _],prv,M1,_) \ fact(['a8:Concept', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a8:Concept', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:img', _, X1],prv,M1,_) \ fact(['a3:Image', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Image', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a3:Organization', X],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:topic_interest', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:eventInterval', _, X1],prv,M1,_) \ fact(['a2:Interval', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Interval', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P116i_is_started_by', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P108i_was_produced_by', X, Y],prv,_,_) \ fact(['a1:P31i_was_modified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P31i_was_modified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:birth', _, X1],prv,M1,_) \ fact(['a2:Birth', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Birth', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P132_overlaps_with', Y, X],prv,_,_) \ fact(['a1:P132_overlaps_with', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P132_overlaps_with', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E71_Man-Made_Thing', X],prv,_,_) \ fact(['a1:P_E71_Man-Made_Thing', X, X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P_E71_Man-Made_Thing', X, X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E66_Formation', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P40_observed_dimension', X, _],prv,_,_) \ fact(['a1:E16_Measurement', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E16_Measurement', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:immediatelyPrecedingEvent', _, X1],prv,M1,_) \ fact(['a2:Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P70_documents', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P131_is_identified_by', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P102i_is_title_of', _, X1],prv,_,_) \ fact(['a1:E71_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E71_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P11i_participated_in', X, Y],prv,_,_) \ fact(['a1:P12i_was_present_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12i_was_present_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P29_custody_received_by', X, _],prv,_,_) \ fact(['a1:E10_Transfer_of_Custody', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E10_Transfer_of_Custody', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:event', Y, X],prv,_,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:agent', Y, X],prv,_,_) \ fact(['a2:event', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:event', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P109_has_current_or_former_curator', X, _],prv,_,_) \ fact(['a1:E78_Collection', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E78_Collection', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P136_was_based_on', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P30_transferred_custody_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:immediatelyFollowingEvent', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P124i_was_transformed_by', X, _],prv,_,_) \ fact(['a1:E77_Persistent_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P132_overlaps_with', X, _],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P110_augmented', Y, X],prv,_,_) \ fact(['a1:P110i_was_augmented_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P110i_was_augmented_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P110i_was_augmented_by', Y, X],prv,_,_) \ fact(['a1:P110_augmented', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P110_augmented', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P142i_was_used_in', X, _],prv,_,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E21_Person', X],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P44_has_condition', _, X1],prv,_,_) \ fact(['a1:E3_Condition_State', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E3_Condition_State', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P78_is_identified_by', Y, X],prv,_,_) \ fact(['a1:P78i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P78i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P78i_identifies', Y, X],prv,_,_) \ fact(['a1:P78_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P78_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P112_diminished', _, X1],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P8i_witnessed', X, _],prv,_,_) \ fact(['a1:E19_Physical_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P5i_forms_part_of', Y, X],prv,_,_) \ fact(['a1:P5_consists_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P5_consists_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P5_consists_of', Y, X],prv,_,_) \ fact(['a1:P5i_forms_part_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P5i_forms_part_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P116_starts', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P39i_was_measured_by', _, X1],prv,_,_) \ fact(['a1:E16_Measurement', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E16_Measurement', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:precedingEvent', X, _],prv,_,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E71_Man-Made_Thing', X0, X1],prv,_,_), fact(['a1:referToSame', X1, X2],prv,_,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],prv,_,_) \ fact(['a1:relatedManMadeThings', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedManMadeThings', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a1:P5i_forms_part_of', X, X2],prv,_,_), fact(['a1:P5i_forms_part_of', X, X1],prv,_,_), fact(['a1:E3_Condition_State', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P10i_contains', _, X1],prv,_,_) \ fact(['a1:E4_Period', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P125i_was_type_of_object_used_in', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P138_represents', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P10_falls_within', X, _],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P56_bears_feature', _, X1],prv,_,_) \ fact(['a1:E26_Physical_Feature', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E26_Physical_Feature', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99i_was_dissolved_by', X, Y],prv,_,_) \ fact(['a1:P11i_participated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11i_participated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E44_Place_Appellation', X],prv,_,_), fact(['a1:E49_Time_Appellation', X],prv,_,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:Nothing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P71_lists', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:immediatelyPrecedingEvent', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:child', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:Event', X],prv,_,_) \ fact(['a9:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a9:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P91i_is_unit_of', X, _],prv,_,_) \ fact(['a1:E58_Measurement_Unit', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E58_Measurement_Unit', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E50_Date', X],prv,M1,_) \ fact(['a1:E49_Time_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E49_Time_Appellation', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P23_transferred_title_from', X, Y],prv,_,_) \ fact(['a1:P14_carried_out_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14_carried_out_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P110_augmented', _, X1],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P55_has_current_location', Y, X],prv,_,_) \ fact(['a1:P55i_currently_holds', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P55i_currently_holds', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P55i_currently_holds', Y, X],prv,_,_) \ fact(['a1:P55_has_current_location', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P55_has_current_location', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E31_Document', X0, X1],prv,_,_), fact(['a1:referredBySame', X1, X2],prv,_,_), fact(['a1:P_E31_Document', X2, X3],prv,_,_) \ fact(['a1:relatedDocuments', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedDocuments', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a1:relatedManMadeThings', Y, X],prv,_,_) \ fact(['a1:relatedManMadeThings', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedManMadeThings', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P74i_is_current_or_former_residence_of', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P103i_was_intention_of', _, X1],prv,_,_) \ fact(['a1:E71_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E71_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P84_had_at_most_duration', X, X2],prv,_,_), fact(['a1:P84_had_at_most_duration', X, X1],prv,_,_), fact(['a1:E52_Time-Span', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P88_consists_of', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P135i_was_created_by', _, X1],prv,_,_) \ fact(['a1:E83_Type_Creation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E83_Type_Creation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P119i_is_met_in_time_by', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P39_measured', X, _],prv,_,_) \ fact(['a1:E16_Measurement', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E16_Measurement', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P97i_was_father_for', X, _],prv,_,_) \ fact(['a1:E21_Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E21_Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P42i_was_assigned_by', _, X1],prv,_,_) \ fact(['a1:E17_Type_Assignment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E17_Type_Assignment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P16i_was_used_for', X, Y],prv,_,_) \ fact(['a1:P12i_was_present_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12i_was_present_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P106_is_composed_of', X, _],prv,_,_) \ fact(['a1:E90_Symbolic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E90_Symbolic_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P43_has_dimension', _, X1],prv,_,_) \ fact(['a1:E54_Dimension', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P81_ongoing_throughout', X, _],prv,M1,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:family_name', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P140_assigned_attribute_to', X, _],prv,_,_) \ fact(['a1:E13_Attribute_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E13_Attribute_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P70i_is_documented_in', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P7_took_place_at', X, _],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P45i_is_incorporated_in', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E10_Transfer_of_Custody', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P73_has_translation', _, X1],prv,_,_) \ fact(['a1:E33_Linguistic_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E33_Linguistic_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95i_was_formed_by', X, X2],prv,_,_), fact(['a1:P95i_was_formed_by', X, X1],prv,_,_), fact(['a1:E74_Group', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P134_continued', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P138i_has_representation', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P109_has_current_or_former_curator', Y, X],prv,_,_) \ fact(['a1:P109i_is_current_or_former_curator_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P109i_is_current_or_former_curator_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P109i_is_current_or_former_curator_of', Y, X],prv,_,_) \ fact(['a1:P109_has_current_or_former_curator', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P109_has_current_or_former_curator', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P11_had_participant', X, Y],prv,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P71_lists', X, Y],prv,_,_) \ fact(['a1:P67_refers_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67_refers_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P44_has_condition', Y, X],prv,_,_) \ fact(['a1:P44i_is_condition_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P44i_is_condition_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P44i_is_condition_of', Y, X],prv,_,_) \ fact(['a1:P44_has_condition', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P44_has_condition', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:openid', Y1, X],prv,M1,_), fact(['a3:openid', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:openid',M1),('a3:openid',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P132_overlaps_with', _, X1],prv,_,_) \ fact(['a1:E4_Period', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P111i_was_added_by', _, X1],prv,_,_) \ fact(['a1:E79_Part_Addition', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E79_Part_Addition', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P40i_was_observed_in', _, X1],prv,_,_) \ fact(['a1:E16_Measurement', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E16_Measurement', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P102_has_title', _, X1],prv,_,_) \ fact(['a1:E35_Title', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E35_Title', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99i_was_dissolved_by', Y, X],prv,_,_) \ fact(['a1:P99_dissolved', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P99_dissolved', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99_dissolved', Y, X],prv,_,_) \ fact(['a1:P99i_was_dissolved_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P99i_was_dissolved_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P119_meets_in_time_with', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P144_joined_with', X, Y],prv,_,_) \ fact(['a1:P11_had_participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11_had_participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:parent', X, Y],prv,M1,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P41_classified', X, Y],prv,_,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P140_assigned_attribute_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:initiatingEvent', _, X1],prv,M1,_) \ fact(['a2:Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P104i_applies_to', _, X1],prv,_,_) \ fact(['a1:E72_Legal_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E72_Legal_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P71i_is_listed_in', _, X1],prv,_,_) \ fact(['a1:E32_Authority_Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E32_Authority_Document', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P35i_was_identified_by', X, _],prv,_,_) \ fact(['a1:E3_Condition_State', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E3_Condition_State', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E57_Material', X],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E53_Place', X0, X1],prv,_,_), fact(['a1:referredBySame', X1, X2],prv,_,_), fact(['a1:P_E53_Place', X2, X3],prv,_,_) \ fact(['a1:relatedPlaces', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedPlaces', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a1:P34i_was_assessed_by', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P121_overlaps_with', Y, X],prv,_,_) \ fact(['a1:P121_overlaps_with', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P121_overlaps_with', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13_destroyed', X, _],prv,_,_) \ fact(['a1:E6_Destruction', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E6_Destruction', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P84_had_at_most_duration', _, X1],prv,_,_) \ fact(['a1:E54_Dimension', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P45_consists_of', _, X1],prv,_,_) \ fact(['a1:E57_Material', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E57_Material', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P100i_died_in', X, Y],prv,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P123_resulted_in', _, X1],prv,_,_) \ fact(['a1:E77_Persistent_Item', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E51_Contact_Point', X],prv,_,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:father', X, X2],prv,M1,_), fact(['a2:father', X, X1],prv,M2,_), fact(['a3:Person', X],prv,M3,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a2:father',M1),('a2:father',M2),('a3:Person',M3)],M), fact(['owl:sameAs', X1, X2],prv,M,U), applied_rules(1,fwd).
fact(['a2:mother', X, X4],prv,M1,_), fact(['a2:mother', X, X3],prv,M2,_), fact(['a3:Person', X],prv,M3,_) \ fact(['owl:sameAs', X3, X4],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a2:mother',M1),('a2:mother',M2),('a3:Person',M3)],M), fact(['owl:sameAs', X3, X4],prv,M,U), applied_rules(1,fwd).
fact(['a1:P9i_forms_part_of', X, X2],prv,_,_), fact(['a1:P9i_forms_part_of', X, X1],prv,_,_), fact(['a1:E4_Period', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99_dissolved', X, Y],prv,_,_) \ fact(['a1:P11_had_participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11_had_participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P15i_influenced', Y, X],prv,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15_was_influenced_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P15_was_influenced_by', Y, X],prv,_,_) \ fact(['a1:P15i_influenced', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15i_influenced', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P67_refers_to', X, _],prv,_,_) \ fact(['a1:E89_Propositional_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:parent', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P14i_performed', Y, X],prv,_,_) \ fact(['a1:P14_carried_out_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14_carried_out_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P14_carried_out_by', Y, X],prv,_,_) \ fact(['a1:P14i_performed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14i_performed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P55_has_current_location', X, _],prv,_,_) \ fact(['a1:E19_Physical_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95_has_formed', Y, X],prv,_,_) \ fact(['a1:P95i_was_formed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P95i_was_formed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95i_was_formed_by', Y, X],prv,_,_) \ fact(['a1:P95_has_formed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P95_has_formed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95i_was_formed_by', X, _],prv,_,_) \ fact(['a1:E74_Group', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P42i_was_assigned_by', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P94_has_created', _, X1],prv,_,_) \ fact(['a1:E28_Conceptual_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E28_Conceptual_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P131_is_identified_by', _, X1],prv,_,_) \ fact(['a1:E82_Actor_Appellation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E82_Actor_Appellation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:based_near', _, X1],prv,M1,_) \ fact(['a10:SpatialThing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a10:SpatialThing', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P108_has_produced', Y, X],prv,_,_) \ fact(['a1:P108i_was_produced_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P108i_was_produced_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P108i_was_produced_by', Y, X],prv,_,_) \ fact(['a1:P108_has_produced', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P108_has_produced', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P112i_was_diminished_by', X, Y],prv,_,_) \ fact(['a1:P31i_was_modified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P31i_was_modified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E46_Section_Definition', X],prv,_,_) \ fact(['a1:E44_Place_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E44_Place_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P58i_defines_section', Y, X],prv,_,_) \ fact(['a1:P58_has_section_definition', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P58_has_section_definition', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P58_has_section_definition', Y, X],prv,_,_) \ fact(['a1:P58i_defines_section', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P58i_defines_section', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:age', X, Y1],prv,M1,_), fact(['a3:age', X, Y2],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:age',M1),('a3:age',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P23i_surrendered_title_through', _, X1],prv,_,_) \ fact(['a1:E8_Acquisition', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E8_Acquisition', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P78_is_identified_by', X, Y],prv,_,_) \ fact(['a1:P1_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P27i_was_origin_of', X, Y],prv,_,_) \ fact(['a1:P7i_witnessed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P7i_witnessed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:currentProject', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P119i_is_met_in_time_by', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:aimChatID', Y1, X],prv,M1,_), fact(['a3:aimChatID', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:aimChatID',M1),('a3:aimChatID',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P27i_was_origin_of', Y, X],prv,_,_) \ fact(['a1:P27_moved_from', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P27_moved_from', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P27_moved_from', Y, X],prv,_,_) \ fact(['a1:P27i_was_origin_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P27i_was_origin_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P37_assigned', _, X1],prv,_,_) \ fact(['a1:E42_Identifier', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E42_Identifier', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P116i_is_started_by', Y, X],prv,_,_) \ fact(['a1:P116_starts', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P116_starts', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P116_starts', Y, X],prv,_,_) \ fact(['a1:P116i_is_started_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P116i_is_started_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:sha1', X, _],prv,M1,_) \ fact(['a3:Document', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:agent', _, X1],prv,_,_) \ fact(['a3:Agent', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P12_occurred_in_the_presence_of', X, _],prv,_,_) \ fact(['a1:E5_Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P117i_includes', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P29i_received_custody_through', X, Y],prv,_,_) \ fact(['a1:P14i_performed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14i_performed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P102_has_title', X, _],prv,_,_) \ fact(['a1:E71_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E71_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P118i_is_overlapped_in_time_by', Y, X],prv,_,_) \ fact(['a1:P118_overlaps_in_time_with', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P118_overlaps_in_time_with', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P118_overlaps_in_time_with', Y, X],prv,_,_) \ fact(['a1:P118i_is_overlapped_in_time_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P118i_is_overlapped_in_time_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P89_falls_within', X, Y],prv,_,_), fact(['a1:P89_falls_within', Y, Z],prv,_,_) \ fact(['a1:P89_falls_within', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P89_falls_within', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P138i_has_representation', X, Y],prv,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67i_is_referred_to_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:father', X, Y1],prv,M1,_), fact(['a2:father', X, Y2],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a2:father',M1),('a2:father',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a3:status', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P137_exemplifies', X, Y],prv,_,_) \ fact(['a1:P2_has_type', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P2_has_type', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:event', X, Y],prv,_,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:followingEvent', X, _],prv,_,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E49_Time_Appellation', X],prv,_,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:witness', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P48i_is_preferred_identifier_of', X, Y],prv,_,_) \ fact(['a1:P1i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P26i_was_destination_of', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:openid', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:organization', X, Y],prv,M1,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P14i_performed', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P48i_is_preferred_identifier_of', X, _],prv,_,_) \ fact(['a1:E42_Identifier', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E42_Identifier', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:plan', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P34i_was_assessed_by', X, Y],prv,_,_) \ fact(['a1:P140i_was_attributed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P140i_was_attributed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P131_is_identified_by', Y, X],prv,_,_) \ fact(['a1:P131i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P131i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P131i_identifies', Y, X],prv,_,_) \ fact(['a1:P131_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P131_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P148i_is_component_of', _, X1],prv,_,_) \ fact(['a1:E89_Propositional_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P1_is_identified_by', _, X1],prv,_,_) \ fact(['a1:E41_Appellation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P129_is_about', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P115i_is_finished_by', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P42_assigned', Y, X],prv,_,_) \ fact(['a1:P42i_was_assigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P42i_was_assigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P42i_was_assigned_by', Y, X],prv,_,_) \ fact(['a1:P42_assigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P42_assigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:employer', _, X1],prv,M1,_) \ fact(['a3:Agent', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P31_has_modified', X, _],prv,_,_) \ fact(['a1:E11_Modification', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E11_Modification', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P87_is_identified_by', Y, X],prv,_,_) \ fact(['a1:P87i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P87i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P87i_identifies', Y, X],prv,_,_) \ fact(['a1:P87_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P87_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:spectator', X, _],prv,_,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E28_Conceptual_Object', X],prv,_,_) \ fact(['a1:E71_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E71_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99_dissolved', X, _],prv,_,_) \ fact(['a1:E68_Dissolution', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E68_Dissolution', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:birth', X, Y],prv,M1,_) \ fact(['a2:event', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:event', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P135i_was_created_by', X, X2],prv,_,_), fact(['a1:P135i_was_created_by', X, X1],prv,_,_), fact(['a1:E55_Type', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:E9_Move', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P128i_is_carried_by', _, X1],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P71i_is_listed_in', X, Y],prv,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67i_is_referred_to_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P5_consists_of', _, X1],prv,_,_) \ fact(['a1:E3_Condition_State', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E3_Condition_State', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P78i_identifies', X, _],prv,_,_) \ fact(['a1:E49_Time_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E49_Time_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P65i_is_shown_by', X, Y],prv,_,_) \ fact(['a1:P128i_is_carried_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P128i_is_carried_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E8_Acquisition', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:followingEvent', _, X1],prv,_,_) \ fact(['a2:Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:icqChatID', _, X1],prv,M1,_) \ fact(['rdfs:Literal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Literal', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a5:PhysicalMedium', X],prv,M1,_) \ fact(['a5:MediaType', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:MediaType', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P70i_is_documented_in', Y, X],prv,_,_) \ fact(['a1:P70_documents', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P70_documents', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P70_documents', Y, X],prv,_,_) \ fact(['a1:P70i_is_documented_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P70i_is_documented_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E75_Conceptual_Object_Appellation', X],prv,M1,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P83i_was_minimum_duration_of', X, _],prv,_,_) \ fact(['a1:E54_Dimension', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:Group', X],prv,_,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P126_employed', _, X1],prv,_,_) \ fact(['a1:E57_Material', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E57_Material', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P40i_was_observed_in', X, _],prv,_,_) \ fact(['a1:E54_Dimension', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:agent', X, Y],prv,_,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P71_lists', X, _],prv,_,_) \ fact(['a1:E32_Authority_Document', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E32_Authority_Document', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P32i_was_technique_of', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E20_Biological_Object', X],prv,_,_) \ fact(['a1:E19_Physical_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P87i_identifies', X, _],prv,_,_) \ fact(['a1:E44_Place_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E44_Place_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P130i_features_are_also_found_on', _, X1],prv,_,_) \ fact(['a1:E70_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P119i_is_met_in_time_by', Y, X],prv,_,_) \ fact(['a1:P119_meets_in_time_with', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P119_meets_in_time_with', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P119_meets_in_time_with', Y, X],prv,_,_) \ fact(['a1:P119i_is_met_in_time_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P119i_is_met_in_time_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:interest', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P146i_lost_member_by', X, Y],prv,_,_) \ fact(['a1:P11i_participated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11i_participated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P30i_custody_transferred_through', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P104_is_subject_to', _, X1],prv,_,_) \ fact(['a1:E30_Right', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E30_Right', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P110_augmented', X, _],prv,_,_) \ fact(['a1:E79_Part_Addition', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E79_Part_Addition', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:based_near', X, _],prv,M1,_) \ fact(['a10:SpatialThing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a10:SpatialThing', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P16_used_specific_object', _, X1],prv,_,_) \ fact(['a1:E70_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E72_Legal_Object', X],prv,_,_) \ fact(['a1:E70_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P67i_is_referred_to_by', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P112_diminished', X, _],prv,_,_) \ fact(['a1:E80_Part_Removal', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E80_Part_Removal', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:NameChange', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E37_Mark', X],prv,_,_) \ fact(['a1:E36_Visual_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E36_Visual_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E73_Information_Object', X0, X1],prv,_,_), fact(['a1:P67_refers_to', X1, X2],prv,_,_), fact(['a1:P_E73_Information_Object', X2, X3],prv,_,_) \ fact(['a1:relatedInformationObjects', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedInformationObjects', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a3:depicts', X, _],prv,_,_) \ fact(['a3:Image', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Image', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:isPrimaryTopicOf', X, Y],prv,_,_) \ fact(['a3:page', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:page', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P146i_lost_member_by', X, _],prv,_,_) \ fact(['a1:E74_Group', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P59i_is_located_on_or_within', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P67_refers_to', X1, X0],prv,_,_), fact(['a1:P67_refers_to', X1, X2],prv,_,_) \ fact(['a1:referredBySame', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:referredBySame', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P28i_surrendered_custody_through', _, X1],prv,_,_) \ fact(['a1:E10_Transfer_of_Custody', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E10_Transfer_of_Custody', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P87i_identifies', X, Y],prv,_,_) \ fact(['a1:P1i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P68i_use_foreseen_by', _, X1],prv,_,_) \ fact(['a1:E29_Design_or_Procedure', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E29_Design_or_Procedure', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P17i_motivated', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P22_transferred_title_to', X, Y1],prv,_,_), fact(['a1:P22_transferred_title_to', X, Y2],prv,_,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', Y1, Y2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P86i_contains', X, _],prv,_,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P25i_moved_by', X, Y],prv,_,_) \ fact(['a1:P12i_was_present_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12i_was_present_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P40_observed_dimension', X, Y],prv,_,_) \ fact(['a1:P141_assigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141_assigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P46_is_composed_of', Y, X],prv,_,_) \ fact(['a1:P46i_forms_part_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P46i_forms_part_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P46i_forms_part_of', Y, X],prv,_,_) \ fact(['a1:P46_is_composed_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P46_is_composed_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P48_has_preferred_identifier', X, Y],prv,_,_) \ fact(['a1:P1_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P91_has_unit', _, X1],prv,_,_) \ fact(['a1:E58_Measurement_Unit', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E58_Measurement_Unit', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P127_has_broader_term', X, Y],prv,_,_), fact(['a1:P127_has_broader_term', Y, Z],prv,_,_) \ fact(['a1:P127_has_broader_term', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P127_has_broader_term', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a2:event', _, X1],prv,_,_) \ fact(['a2:Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E3_Condition_State', X],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:accountServiceHomepage', X, _],prv,M1,_) \ fact(['a3:OnlineAccount', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:OnlineAccount', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P70i_is_documented_in', X, Y],prv,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67i_is_referred_to_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:holdsAccount', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P67_refers_to', X0, X1],prv,_,_), fact(['a1:P_E31_Document', X1, X2],prv,_,_) \ fact(['a1:refersToDocument', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:refersToDocument', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P146_separated_from', _, X1],prv,_,_) \ fact(['a1:E74_Group', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P45i_is_incorporated_in', X, _],prv,_,_) \ fact(['a1:E57_Material', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E57_Material', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P88i_forms_part_of', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P24i_changed_ownership_through', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:jabberID', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:participant', _, X1],prv,_,_) \ fact(['a3:Agent', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P4_has_time-span', X, X2],prv,_,_), fact(['a1:P4_has_time-span', X, X1],prv,_,_), fact(['a1:E2_Temporal_Entity', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P55_has_current_location', X, X2],prv,_,_), fact(['a1:P55_has_current_location', X, X1],prv,_,_), fact(['a1:E19_Physical_Object', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P120i_occurs_after', X, Y],prv,_,_), fact(['a1:P120i_occurs_after', Y, Z],prv,_,_) \ fact(['a1:P120i_occurs_after', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P120i_occurs_after', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:E13_Attribute_Assignment', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:knows', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a3:weblog', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a2:PositionChange', X],prv,_,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P134_continued', Y, X],prv,_,_) \ fact(['a1:P134i_was_continued_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P134i_was_continued_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P134i_was_continued_by', Y, X],prv,_,_) \ fact(['a1:P134_continued', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P134_continued', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P29_custody_received_by', X, Y],prv,_,_) \ fact(['a1:P14_carried_out_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14_carried_out_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P43i_is_dimension_of', X, _],prv,_,_) \ fact(['a1:E54_Dimension', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P137_exemplifies', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P65i_is_shown_by', X, _],prv,_,_) \ fact(['a1:E36_Visual_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E36_Visual_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P91i_is_unit_of', Y, X],prv,_,_) \ fact(['a1:P91_has_unit', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P91_has_unit', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P91_has_unit', Y, X],prv,_,_) \ fact(['a1:P91i_is_unit_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P91i_is_unit_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P55_has_current_location', X, Y],prv,_,_) \ fact(['a1:P53_has_former_or_current_location', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P53_has_former_or_current_location', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13i_was_destroyed_by', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P145i_left_by', Y, X],prv,_,_) \ fact(['a1:P145_separated', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P145_separated', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P145_separated', Y, X],prv,_,_) \ fact(['a1:P145i_left_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P145i_left_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95_has_formed', X, _],prv,_,_) \ fact(['a1:E66_Formation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E66_Formation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P38i_was_deassigned_by', X, _],prv,_,_) \ fact(['a1:E42_Identifier', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E42_Identifier', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:immediatelyPrecedingEvent', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a3:isPrimaryTopicOf', Y, X],prv,_,_) \ fact(['a3:primaryTopic', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:primaryTopic', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:primaryTopic', Y, X],prv,_,_) \ fact(['a3:isPrimaryTopicOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:isPrimaryTopicOf', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P38_deassigned', X, _],prv,_,_) \ fact(['a1:E15_Identifier_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E15_Identifier_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P17_was_motivated_by', X, Y],prv,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15_was_influenced_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P4i_is_time-span_of', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E31_Document', X0, X1],prv,_,_), fact(['a1:referToSame', X1, X2],prv,_,_), fact(['a1:P_E31_Document', X2, X3],prv,_,_) \ fact(['a1:relatedDocuments', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedDocuments', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a2:Performance', X],prv,_,_) \ fact(['a2:GroupEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:GroupEvent', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:PersonalProfileDocument', X],prv,M1,_) \ fact(['a3:Document', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P17_was_motivated_by', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P19_was_intended_use_of', Y, X],prv,_,_) \ fact(['a1:P19i_was_made_for', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P19i_was_made_for', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P19i_was_made_for', Y, X],prv,_,_) \ fact(['a1:P19_was_intended_use_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P19_was_intended_use_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P29i_received_custody_through', _, X1],prv,_,_) \ fact(['a1:E10_Transfer_of_Custody', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E10_Transfer_of_Custody', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P30_transferred_custody_of', X, _],prv,_,_) \ fact(['a1:E10_Transfer_of_Custody', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E10_Transfer_of_Custody', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:skypeID', X, Y],prv,M1,_) \ fact(['a3:nick', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:nick', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P101_had_as_general_use', Y, X],prv,_,_) \ fact(['a1:P101i_was_use_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P101i_was_use_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P101i_was_use_of', Y, X],prv,_,_) \ fact(['a1:P101_had_as_general_use', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P101_had_as_general_use', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P131_is_identified_by', X, Y],prv,_,_) \ fact(['a1:P1_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P46i_forms_part_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P76_has_contact_point', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:death', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:followingEvent', X, Y],prv,_,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P58i_defines_section', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P16i_was_used_for', X, _],prv,_,_) \ fact(['a1:E70_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95i_was_formed_by', X, Y],prv,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:relatedDocuments', Y, X],prv,_,_) \ fact(['a1:relatedDocuments', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedDocuments', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P75_possesses', _, X1],prv,_,_) \ fact(['a1:E30_Right', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E30_Right', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E5_Event', X],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P131i_identifies', X, _],prv,_,_) \ fact(['a1:E82_Actor_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E82_Actor_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P35_has_identified', X, _],prv,_,_) \ fact(['a1:E14_Condition_Assessment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E14_Condition_Assessment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P143_joined', X, X2],prv,_,_), fact(['a1:P143_joined', X, X1],prv,_,_), fact(['a1:E85_Joining', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P135i_was_created_by', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P83_had_at_least_duration', Y, X],prv,_,_) \ fact(['a1:P83i_was_minimum_duration_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P83i_was_minimum_duration_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P83i_was_minimum_duration_of', Y, X],prv,_,_) \ fact(['a1:P83_had_at_least_duration', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P83_had_at_least_duration', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P113i_was_removed_by', Y, X],prv,_,_) \ fact(['a1:P113_removed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P113_removed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P113_removed', Y, X],prv,_,_) \ fact(['a1:P113i_was_removed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P113i_was_removed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P27_moved_from', X, Y],prv,_,_) \ fact(['a1:P7_took_place_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P7_took_place_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E73_Information_Object', X0, X1],prv,_,_), fact(['a1:referToSame', X1, X2],prv,_,_), fact(['a1:P_E73_Information_Object', X2, X3],prv,_,_) \ fact(['a1:relatedInformationObjects', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedInformationObjects', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a1:P108_has_produced', X, Y],prv,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92_brought_into_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E31_Document', X],prv,_,_) \ fact(['a1:E73_Information_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E73_Information_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E40_Legal_Body', X],prv,M1,_) \ fact(['a1:E74_Group', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P106_is_composed_of', X, Y],prv,_,_), fact(['a1:P106_is_composed_of', Y, Z],prv,_,_) \ fact(['a1:P106_is_composed_of', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P106_is_composed_of', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P62i_is_depicted_by', Y, X],prv,_,_) \ fact(['a1:P62_depicts', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P62_depicts', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P62_depicts', Y, X],prv,_,_) \ fact(['a1:P62i_is_depicted_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P62i_is_depicted_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:birth', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E39_Actor', X],prv,_,_) \ fact(['a1:E77_Persistent_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E64_End_of_Existence', X],prv,_,_) \ fact(['a1:E5_Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P74_has_current_or_former_residence', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P110i_was_augmented_by', X, Y],prv,_,_) \ fact(['a1:P31i_was_modified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P31i_was_modified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P52i_is_current_owner_of', X, Y],prv,_,_) \ fact(['a1:P105i_has_right_on', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P105i_has_right_on', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P101_had_as_general_use', X, _],prv,_,_) \ fact(['a1:E70_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13_destroyed', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P142_used_constituent', X, _],prv,_,_) \ fact(['a1:E15_Identifier_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E15_Identifier_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E45_Address', X],prv,M1,_) \ fact(['a1:E51_Contact_Point', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E51_Contact_Point', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P43i_is_dimension_of', Y, X],prv,_,_) \ fact(['a1:P43_has_dimension', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P43_has_dimension', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P43_has_dimension', Y, X],prv,_,_) \ fact(['a1:P43i_is_dimension_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P43i_is_dimension_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P21_had_general_purpose', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:relationship', X, Y],prv,_,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a5:AgentClass', X],prv,M1,_) \ fact(['rdfs:Class', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Class', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P31i_was_modified_by', Y, X],prv,_,_) \ fact(['a1:P31_has_modified', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P31_has_modified', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P31_has_modified', Y, X],prv,_,_) \ fact(['a1:P31i_was_modified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P31i_was_modified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:partner', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P98i_was_born', Y, X],prv,_,_) \ fact(['a1:P98_brought_into_life', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P98_brought_into_life', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P98_brought_into_life', Y, X],prv,_,_) \ fact(['a1:P98i_was_born', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P98i_was_born', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:immediatelyFollowingEvent', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P134_continued', X, Y],prv,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15_was_influenced_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P35_has_identified', _, X1],prv,_,_) \ fact(['a1:E3_Condition_State', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E3_Condition_State', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P51i_is_former_or_current_owner_of', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:mother', X, Y],prv,M1,_) \ fact(['a6:childOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a6:childOf', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P115_finishes', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:thumbnail', _, X1],prv,M1,_) \ fact(['a3:Image', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Image', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P2_has_type', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P5i_forms_part_of', _, X1],prv,_,_) \ fact(['a1:E3_Condition_State', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E3_Condition_State', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P22i_acquired_title_through', Y, X],prv,_,_) \ fact(['a1:P22_transferred_title_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P22_transferred_title_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P22_transferred_title_to', Y, X],prv,_,_) \ fact(['a1:P22i_acquired_title_through', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P22i_acquired_title_through', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P25_moved', _, X1],prv,_,_) \ fact(['a1:E19_Physical_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P127_has_broader_term', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P69_is_associated_with', Y, X],prv,_,_) \ fact(['a1:P69_is_associated_with', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P69_is_associated_with', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:father', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P139_has_alternative_form', _, X1],prv,M1,_) \ fact(['a1:E41_Appellation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P26_moved_to', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P123_resulted_in', X, _],prv,_,_) \ fact(['a1:E81_Transformation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E81_Transformation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P92_brought_into_existence', _, X1],prv,_,_) \ fact(['a1:E77_Persistent_Item', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X1],prv,_,U), applied_rules(1,fwd).
fact(['a5:FileFormat', X],prv,M1,_) \ fact(['a5:MediaType', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:MediaType', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P50_has_current_keeper', X, Y],prv,_,_) \ fact(['a1:P49_has_former_or_current_keeper', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:firstName', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P2_has_type', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E25_Man-Made_Feature', X],prv,M1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E73_Information_Object', X],prv,_,_) \ fact(['a1:E89_Propositional_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P96i_gave_birth', X, Y],prv,_,_) \ fact(['a1:P11i_participated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11i_participated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P28_custody_surrendered_by', X, _],prv,_,_) \ fact(['a1:E10_Transfer_of_Custody', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E10_Transfer_of_Custody', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P55i_currently_holds', X, Y],prv,_,_) \ fact(['a1:P53i_is_former_or_current_location_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P87_is_identified_by', X, Y],prv,_,_) \ fact(['a1:P1_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P37_assigned', X, Y],prv,_,_) \ fact(['a1:P141_assigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141_assigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:workInfoHomepage', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E22_Man-Made_Object', X],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P109i_is_current_or_former_curator_of', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P15i_influenced', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P73i_is_translation_of', X, X2],prv,_,_), fact(['a1:P73i_is_translation_of', X, X1],prv,_,_), fact(['a1:E33_Linguistic_Object', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95i_was_formed_by', _, X1],prv,_,_) \ fact(['a1:E66_Formation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E66_Formation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P129_is_about', X, Y],prv,_,_) \ fact(['a1:P67_refers_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67_refers_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E81_Transformation', X],prv,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E63_Beginning_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E31_Document', X0, X1],prv,_,_), fact(['a1:refersToDocument', X1, X2],prv,_,_), fact(['a1:refersToDocument', X2, X3],prv,_,_) \ fact(['a1:relatedDocuments', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedDocuments', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a1:P33i_was_used_by', Y, X],prv,_,_) \ fact(['a1:P33_used_specific_technique', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P33_used_specific_technique', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P33_used_specific_technique', Y, X],prv,_,_) \ fact(['a1:P33i_was_used_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P33i_was_used_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P111_added', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P129i_is_subject_of', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P9i_forms_part_of', X, _],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P14_carried_out_by', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P126i_was_employed_in', _, X1],prv,_,_) \ fact(['a1:E11_Modification', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E11_Modification', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E71_Man-Made_Thing', X0, X1],prv,_,_), fact(['a1:referredBySame', X1, X2],prv,_,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],prv,_,_) \ fact(['a1:relatedManMadeThings', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedManMadeThings', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a1:P58i_defines_section', X, _],prv,_,_) \ fact(['a1:E46_Section_Definition', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E46_Section_Definition', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P14i_performed', X, Y],prv,_,_) \ fact(['a1:P11i_participated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11i_participated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P139_has_alternative_form', X, _],prv,M1,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P75_possesses', Y, X],prv,_,_) \ fact(['a1:P75i_is_possessed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P75i_is_possessed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P75i_is_possessed_by', Y, X],prv,_,_) \ fact(['a1:P75_possesses', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P75_possesses', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:position', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P145i_left_by', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P10_falls_within', _, X1],prv,_,_) \ fact(['a1:E4_Period', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E45_Address', X],prv,M1,_) \ fact(['a1:E44_Place_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E44_Place_Appellation', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:immediatelyFollowingEvent', X, Y],prv,M1,_) \ fact(['a2:followingEvent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:followingEvent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P73i_is_translation_of', _, X1],prv,_,_) \ fact(['a1:E33_Linguistic_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E33_Linguistic_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Employment', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a5:Location', X],prv,M1,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:LocationPeriodOrJurisdiction', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P33i_was_used_by', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:topic', X, _],prv,_,_) \ fact(['a3:Document', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P12_occurred_in_the_presence_of', Y, X],prv,_,_) \ fact(['a1:P12i_was_present_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12i_was_present_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P12i_was_present_at', Y, X],prv,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P117_occurs_during', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P76i_provides_access_to', X, _],prv,_,_) \ fact(['a1:E51_Contact_Point', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E51_Contact_Point', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P70_documents', X, _],prv,_,_) \ fact(['a1:E31_Document', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E31_Document', X],prv,_,U), applied_rules(1,fwd).
fact(['a5:MediaType', X],prv,_,_) \ fact(['a5:MediaTypeOrExtent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:MediaTypeOrExtent', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:maker', _, X1],prv,_,_) \ fact(['a3:Agent', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:primaryTopic', X, Y1],prv,_,_), fact(['a3:primaryTopic', X, Y2],prv,_,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', Y1, Y2],prv,_,U), applied_rules(1,fwd).
fact(['a3:mbox_sha1sum', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P108_has_produced', _, X1],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P35i_was_identified_by', _, X1],prv,_,_) \ fact(['a1:E14_Condition_Assessment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E14_Condition_Assessment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P76_has_contact_point', _, X1],prv,_,_) \ fact(['a1:E51_Contact_Point', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E51_Contact_Point', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E84_Information_Carrier', X],prv,M1,_) \ fact(['a1:E22_Man-Made_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E22_Man-Made_Object', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P48_has_preferred_identifier', Y, X],prv,_,_) \ fact(['a1:P48i_is_preferred_identifier_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P48i_is_preferred_identifier_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P48i_is_preferred_identifier_of', Y, X],prv,_,_) \ fact(['a1:P48_has_preferred_identifier', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P48_has_preferred_identifier', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:BasMitzvah', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P124i_was_transformed_by', Y, X],prv,_,_) \ fact(['a1:P124_transformed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P124_transformed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P124_transformed', Y, X],prv,_,_) \ fact(['a1:P124i_was_transformed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P124i_was_transformed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P92_brought_into_existence', X, Y],prv,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13_destroyed', X, Y],prv,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93_took_out_of_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P8_took_place_on_or_within', Y, X],prv,_,_) \ fact(['a1:P8i_witnessed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P8i_witnessed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P8i_witnessed', Y, X],prv,_,_) \ fact(['a1:P8_took_place_on_or_within', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P8_took_place_on_or_within', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P76i_provides_access_to', Y, X],prv,_,_) \ fact(['a1:P76_has_contact_point', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P76_has_contact_point', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P76_has_contact_point', Y, X],prv,_,_) \ fact(['a1:P76i_provides_access_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P76i_provides_access_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P106i_forms_part_of', _, X1],prv,_,_) \ fact(['a1:E90_Symbolic_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E90_Symbolic_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P56_bears_feature', X, Y],prv,_,_) \ fact(['a1:P46_is_composed_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P46_is_composed_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P145i_left_by', X, Y],prv,_,_) \ fact(['a1:P11i_participated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11i_participated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:mbox', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P53_has_former_or_current_location', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99i_was_dissolved_by', X, _],prv,_,_) \ fact(['a1:E74_Group', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P25_moved', X, Y],prv,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:immediatelyFollowingEvent', _, X1],prv,M1,_) \ fact(['a2:Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P96_by_mother', _, X1],prv,_,_) \ fact(['a1:E21_Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E21_Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:msnChatID', X, Y],prv,M1,_) \ fact(['a3:nick', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:nick', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P146i_lost_member_by', Y, X],prv,_,_) \ fact(['a1:P146_separated_from', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P146_separated_from', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P146_separated_from', Y, X],prv,_,_) \ fact(['a1:P146i_lost_member_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P146i_lost_member_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P40_observed_dimension', _, X1],prv,_,_) \ fact(['a1:E54_Dimension', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:mother', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P33_used_specific_technique', _, X1],prv,_,_) \ fact(['a1:E29_Design_or_Procedure', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E29_Design_or_Procedure', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P41i_was_classified_by', X, Y],prv,_,_) \ fact(['a1:P140i_was_attributed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P140i_was_attributed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:schoolHomepage', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P52_has_current_owner', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P7_took_place_at', Y, X],prv,_,_) \ fact(['a1:P7i_witnessed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P7i_witnessed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P7i_witnessed', Y, X],prv,_,_) \ fact(['a1:P7_took_place_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P7_took_place_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95_has_formed', _, X1],prv,_,_) \ fact(['a1:E74_Group', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:Person', X],prv,_,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P127i_has_narrower_term', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E6_Destruction', X],prv,_,_) \ fact(['a1:E64_End_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E64_End_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P53i_is_former_or_current_location_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P134_continued', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:account', _, X1],prv,M1,_) \ fact(['a3:OnlineAccount', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:OnlineAccount', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P127_has_broader_term', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P93_took_out_of_existence', _, X1],prv,_,_) \ fact(['a1:E77_Persistent_Item', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P137_exemplifies', Y, X],prv,_,_) \ fact(['a1:P137i_is_exemplified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P137i_is_exemplified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P137i_is_exemplified_by', Y, X],prv,_,_) \ fact(['a1:P137_exemplifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P137_exemplifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P22_transferred_title_to', X, _],prv,_,_) \ fact(['a1:E8_Acquisition', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E8_Acquisition', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:accountName', X, _],prv,M1,_) \ fact(['a3:OnlineAccount', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:OnlineAccount', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:mother', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P30i_custody_transferred_through', _, X1],prv,_,_) \ fact(['a1:E10_Transfer_of_Custody', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E10_Transfer_of_Custody', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P86_falls_within', X, _],prv,_,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13i_was_destroyed_by', X, Y],prv,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P20_had_specific_purpose', Y, X],prv,_,_) \ fact(['a1:P20i_was_purpose_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P20i_was_purpose_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P20i_was_purpose_of', Y, X],prv,_,_) \ fact(['a1:P20_had_specific_purpose', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P20_had_specific_purpose', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P89i_contains', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P5i_forms_part_of', X, _],prv,_,_) \ fact(['a1:E3_Condition_State', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E3_Condition_State', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P49i_is_former_or_current_keeper_of', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P128i_is_carried_by', X, _],prv,_,_) \ fact(['a1:E73_Information_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E73_Information_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Imprisonment', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:tipjar', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P92i_was_brought_into_existence_by', X, Y],prv,_,_) \ fact(['a1:P12i_was_present_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12i_was_present_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P98i_was_born', X, Y],prv,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:organization', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a2:concurrentEvent', Y, X],prv,_,_) \ fact(['a2:concurrentEvent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:concurrentEvent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:yahooChatID', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P42_assigned', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P91_has_unit', X, _],prv,_,_) \ fact(['a1:E54_Dimension', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Retirement', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:tipjar', X, Y],prv,M1,_) \ fact(['a3:page', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:page', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P62_depicts', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:interval', _, X1],prv,M1,_) \ fact(['a2:Interval', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Interval', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a2:olb', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P117i_includes', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P88i_forms_part_of', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:mother', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P73i_is_translation_of', X, Y],prv,_,_) \ fact(['a1:P130i_features_are_also_found_on', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:father', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P135_created_type', X, _],prv,_,_) \ fact(['a1:E83_Type_Creation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E83_Type_Creation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P59i_is_located_on_or_within', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Dismissal', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P96i_gave_birth', _, X1],prv,_,_) \ fact(['a1:E67_Birth', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E67_Birth', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E27_Site', X],prv,M1,_) \ fact(['a1:E26_Physical_Feature', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E26_Physical_Feature', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:principal', X, X2],prv,M1,_), fact(['a2:principal', X, X1],prv,M2,_), fact(['a2:IndividualEvent', X],prv,M3,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a2:principal',M1),('a2:principal',M2),('a2:IndividualEvent',M3)],M), fact(['owl:sameAs', X1, X2],prv,M,U), applied_rules(1,fwd).
fact(['a3:msnChatID', _, X1],prv,M1,_) \ fact(['rdfs:Literal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Literal', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a3:homepage', Y1, X],prv,M1,_), fact(['a3:homepage', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:homepage',M1),('a3:homepage',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P1i_identifies', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P10_falls_within', X, Y],prv,_,_), fact(['a1:P10_falls_within', Y, Z],prv,_,_) \ fact(['a1:P10_falls_within', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P10_falls_within', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P96_by_mother', X, _],prv,_,_) \ fact(['a1:E67_Birth', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E67_Birth', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Enrolment', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P75_possesses', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P93i_was_taken_out_of_existence_by', _, X1],prv,_,_) \ fact(['a1:E64_End_of_Existence', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E64_End_of_Existence', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P100_was_death_of', _, X1],prv,_,_) \ fact(['a1:E21_Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E21_Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P126i_was_employed_in', X, _],prv,_,_) \ fact(['a1:E57_Material', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E57_Material', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P9i_forms_part_of', _, X1],prv,_,_) \ fact(['a1:E4_Period', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:Person', X],prv,_,_) \ fact(['a10:SpatialThing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a10:SpatialThing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P16_used_specific_object', X, Y],prv,_,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P92i_was_brought_into_existence_by', X, _],prv,_,_) \ fact(['a1:E77_Persistent_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P54i_is_current_permanent_location_of', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P51i_is_former_or_current_owner_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P115i_is_finished_by', X, Y],prv,_,_), fact(['a1:P115i_is_finished_by', Y, Z],prv,_,_) \ fact(['a1:P115i_is_finished_by', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P115i_is_finished_by', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P137i_is_exemplified_by', X, Y],prv,_,_) \ fact(['a1:P2i_is_type_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P2i_is_type_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:concludingEvent', _, X1],prv,M1,_) \ fact(['a2:Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a3:thumbnail', X, _],prv,M1,_) \ fact(['a3:Image', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Image', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P27i_was_origin_of', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:parent', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P44i_is_condition_of', X, _],prv,_,_) \ fact(['a1:E3_Condition_State', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E3_Condition_State', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P144i_gained_member_by', X, Y],prv,_,_) \ fact(['a1:P11i_participated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11i_participated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P118i_is_overlapped_in_time_by', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P129i_is_subject_of', _, X1],prv,_,_) \ fact(['a1:E89_Propositional_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99_dissolved', _, X1],prv,_,_) \ fact(['a1:E74_Group', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P20_had_specific_purpose', _, X1],prv,_,_) \ fact(['a1:E5_Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P98i_was_born', _, X1],prv,_,_) \ fact(['a1:E67_Birth', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E67_Birth', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P32i_was_technique_of', X, Y],prv,_,_) \ fact(['a1:P125i_was_type_of_object_used_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P16_used_specific_object', X, Y],prv,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15_was_influenced_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P65_shows_visual_item', X, _],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P129i_is_subject_of', X, Y],prv,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67i_is_referred_to_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P134i_was_continued_by', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:msnChatID', Y1, X],prv,M1,_), fact(['a3:msnChatID', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:msnChatID',M1),('a3:msnChatID',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P87_is_identified_by', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:Person', X],prv,M1,_), fact(['a3:Project', X],prv,M2,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:Person',M1),('a3:Project',M2)],M), fact(['owl:Nothing', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:E33_Linguistic_Object', X],prv,_,_) \ fact(['a1:E73_Information_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E73_Information_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:geekcode', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:officiator', X, Y],prv,M1,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P114_is_equal_in_time_to', Y, X],prv,_,_) \ fact(['a1:P114_is_equal_in_time_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P114_is_equal_in_time_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:partner', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a2:spectator', X, Y],prv,_,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P28i_surrendered_custody_through', X, Y],prv,_,_) \ fact(['a1:P14i_performed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14i_performed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P136i_supported_type_creation', X, Y],prv,_,_) \ fact(['a1:P15i_influenced', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15i_influenced', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P72i_is_language_of', X, _],prv,_,_) \ fact(['a1:E56_Language', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E56_Language', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P96_by_mother', X, Y],prv,_,_) \ fact(['a1:P11_had_participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11_had_participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P116_starts', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:img', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P100i_died_in', X, _],prv,_,_) \ fact(['a1:E21_Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E21_Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P96i_gave_birth', X, _],prv,_,_) \ fact(['a1:E21_Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E21_Person', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P108i_was_produced_by', X, Y],prv,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:familyName', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P148_has_component', X, Y],prv,_,_), fact(['a1:P148_has_component', Y, Z],prv,_,_) \ fact(['a1:P148_has_component', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P148_has_component', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P55i_currently_holds', _, X1],prv,_,_) \ fact(['a1:E19_Physical_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Event', X],prv,_,_) \ fact(['a11:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a11:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P97i_was_father_for', Y, X],prv,_,_) \ fact(['a1:P97_from_father', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P97_from_father', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P97_from_father', Y, X],prv,_,_) \ fact(['a1:P97i_was_father_for', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P97i_was_father_for', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P26_moved_to', X, _],prv,_,_) \ fact(['a1:E9_Move', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E9_Move', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E52_Time-Span', X],prv,_,_), fact(['a1:E53_Place', X],prv,_,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:Nothing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P89_falls_within', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E56_Language', X],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:spectator', _, X1],prv,_,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P40i_was_observed_in', Y, X],prv,_,_) \ fact(['a1:P40_observed_dimension', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P40_observed_dimension', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P40_observed_dimension', Y, X],prv,_,_) \ fact(['a1:P40i_was_observed_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P40i_was_observed_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E71_Man-Made_Thing', X0, X1],prv,_,_), fact(['a1:P67_refers_to', X1, X2],prv,_,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],prv,_,_) \ fact(['a1:relatedManMadeThings', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedManMadeThings', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a2:Adoption', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P42i_was_assigned_by', X, Y],prv,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141i_was_assigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P95_has_formed', X, Y],prv,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92_brought_into_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P31i_was_modified_by', X, Y],prv,_,_) \ fact(['a1:P12i_was_present_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12i_was_present_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P56i_is_found_on', X, Y],prv,_,_) \ fact(['a1:P46i_forms_part_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P46i_forms_part_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P117_occurs_during', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99_dissolved', X, Y],prv,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93_took_out_of_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P41_classified', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:msnChatID', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P89i_contains', X, Y],prv,_,_), fact(['a1:P89i_contains', Y, Z],prv,_,_) \ fact(['a1:P89i_contains', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P89i_contains', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E31_Document', X0, X1],prv,_,_), fact(['a1:P67_refers_to', X1, X2],prv,_,_), fact(['a1:P_E31_Document', X2, X3],prv,_,_) \ fact(['a1:relatedDocuments', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedDocuments', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a1:P137i_is_exemplified_by', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P130_shows_features_of', Y, X],prv,_,_) \ fact(['a1:P130i_features_are_also_found_on', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P130i_features_are_also_found_on', Y, X],prv,_,_) \ fact(['a1:P130_shows_features_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P130_shows_features_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P52i_is_current_owner_of', X, Y],prv,_,_) \ fact(['a1:P51i_is_former_or_current_owner_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P46i_forms_part_of', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P19i_was_made_for', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E17_Type_Assignment', X],prv,_,_) \ fact(['a1:E13_Attribute_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E13_Attribute_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E32_Authority_Document', X],prv,_,_) \ fact(['a1:E31_Document', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E31_Document', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P135i_was_created_by', Y, X],prv,_,_) \ fact(['a1:P135_created_type', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P135_created_type', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P135_created_type', Y, X],prv,_,_) \ fact(['a1:P135i_was_created_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P135i_was_created_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P120_occurs_before', Y, X],prv,_,_) \ fact(['a1:P120i_occurs_after', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P120i_occurs_after', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P120i_occurs_after', Y, X],prv,_,_) \ fact(['a1:P120_occurs_before', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P120_occurs_before', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P107i_is_current_or_former_member_of', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:gender', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P19i_was_made_for', X, _],prv,_,_) \ fact(['a1:E71_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E71_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P86_falls_within', X, Y],prv,_,_), fact(['a1:P86_falls_within', Y, Z],prv,_,_) \ fact(['a1:P86_falls_within', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P86_falls_within', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P120_occurs_before', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E19_Physical_Object', X],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P7i_witnessed', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P75i_is_possessed_by', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['rdfs:ContainerMembershipProperty', X],prv,M1,_) \ fact(['rdf:Property', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdf:Property', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P16_used_specific_object', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P27i_was_origin_of', _, X1],prv,_,_) \ fact(['a1:E9_Move', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E9_Move', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P92i_was_brought_into_existence_by', _, X1],prv,_,_) \ fact(['a1:E63_Beginning_of_Existence', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E63_Beginning_of_Existence', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P113i_was_removed_by', _, X1],prv,_,_) \ fact(['a1:E80_Part_Removal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E80_Part_Removal', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P103_was_intended_for', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:child', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a3:homepage', X, Y],prv,M1,_) \ fact(['a3:page', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:page', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a2:partner', X, Y],prv,M1,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P39i_was_measured_by', X, Y],prv,_,_) \ fact(['a1:P140i_was_attributed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P140i_was_attributed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E48_Place_Name', X],prv,M1,_) \ fact(['a1:P_E53_Place', X, X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P_E53_Place', X, X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:schoolHomepage', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P34_concerned', X, _],prv,_,_) \ fact(['a1:E14_Condition_Assessment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E14_Condition_Assessment', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Redundancy', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P28_custody_surrendered_by', Y, X],prv,_,_) \ fact(['a1:P28i_surrendered_custody_through', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P28i_surrendered_custody_through', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P28i_surrendered_custody_through', Y, X],prv,_,_) \ fact(['a1:P28_custody_surrendered_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P28_custody_surrendered_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P27_moved_from', X, Y],prv,_,_), fact(['a1:P27_moved_from', Y, Z],prv,_,_) \ fact(['a1:P27_moved_from', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P27_moved_from', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:E80_Part_Removal', X],prv,_,_) \ fact(['a1:E11_Modification', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E11_Modification', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P102i_is_title_of', X, _],prv,_,_) \ fact(['a1:E35_Title', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E35_Title', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P116i_is_started_by', X, Y],prv,_,_), fact(['a1:P116i_is_started_by', Y, Z],prv,_,_) \ fact(['a1:P116i_is_started_by', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P116i_is_started_by', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:E44_Place_Appellation', X],prv,_,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P54_has_current_permanent_location', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P38i_was_deassigned_by', Y, X],prv,_,_) \ fact(['a1:P38_deassigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P38_deassigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P38_deassigned', Y, X],prv,_,_) \ fact(['a1:P38i_was_deassigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P38i_was_deassigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P97i_was_father_for', _, X1],prv,_,_) \ fact(['a1:E67_Birth', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E67_Birth', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P4_has_time-span', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Formation', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:agent', X, _],prv,_,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P137_exemplifies', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P137i_is_exemplified_by', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P80_end_is_qualified_by', X, _],prv,M1,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:knows', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:Disbanding', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P148i_is_component_of', X, Y],prv,_,_), fact(['a1:P148i_is_component_of', Y, Z],prv,_,_) \ fact(['a1:P148i_is_component_of', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P148i_is_component_of', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a3:yahooChatID', X, Y],prv,M1,_) \ fact(['a3:nick', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:nick', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a2:death', X, Y],prv,M1,_) \ fact(['a2:event', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:event', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P89_falls_within', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P115_finishes', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:death', _, X1],prv,M1,_) \ fact(['a2:Death', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Death', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P35i_was_identified_by', X, Y],prv,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141i_was_assigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P111_added', X, _],prv,_,_) \ fact(['a1:E79_Part_Addition', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E79_Part_Addition', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P37i_was_assigned_by', X, _],prv,_,_) \ fact(['a1:E42_Identifier', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E42_Identifier', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P42_assigned', X, _],prv,_,_) \ fact(['a1:E17_Type_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E17_Type_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E73_Information_Object', X],prv,_,_) \ fact(['a1:E90_Symbolic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E90_Symbolic_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P110_augmented', X, Y],prv,_,_) \ fact(['a1:P31_has_modified', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P31_has_modified', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P78i_identifies', X, Y],prv,_,_) \ fact(['a1:P1i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P91i_is_unit_of', _, X1],prv,_,_) \ fact(['a1:E54_Dimension', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P146_separated_from', X, _],prv,_,_) \ fact(['a1:E86_Leaving', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E86_Leaving', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:position', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P86i_contains', _, X1],prv,_,_) \ fact(['a1:E52_Time-Span', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:mbox_sha1sum', Y1, X],prv,M1,_), fact(['a3:mbox_sha1sum', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:mbox_sha1sum',M1),('a3:mbox_sha1sum',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:E74_Group', X],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P37i_was_assigned_by', X, Y],prv,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141i_was_assigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:yahooChatID', _, X1],prv,M1,_) \ fact(['rdfs:Literal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Literal', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P127i_has_narrower_term', X, Y],prv,_,_), fact(['a1:P127i_has_narrower_term', Y, Z],prv,_,_) \ fact(['a1:P127i_has_narrower_term', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P127i_has_narrower_term', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a3:member', _, X1],prv,M1,_) \ fact(['a3:Agent', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P21i_was_purpose_of', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E29_Design_or_Procedure', X],prv,_,_) \ fact(['a1:E73_Information_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E73_Information_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Execution', X],prv,M1,_) \ fact(['a2:Death', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Death', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P71_lists', Y, X],prv,_,_) \ fact(['a1:P71i_is_listed_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P71i_is_listed_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P71i_is_listed_in', Y, X],prv,_,_) \ fact(['a1:P71_lists', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P71_lists', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P84_had_at_most_duration', X, _],prv,_,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P101i_was_use_of', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P142_used_constituent', Y, X],prv,_,_) \ fact(['a1:P142i_was_used_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P142i_was_used_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P142i_was_used_in', Y, X],prv,_,_) \ fact(['a1:P142_used_constituent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P142_used_constituent', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:position', X, Y],prv,M1,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P147i_was_curated_by', _, X1],prv,_,_) \ fact(['a1:E87_Curation_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E87_Curation_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P49_has_former_or_current_keeper', Y, X],prv,_,_) \ fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P49i_is_former_or_current_keeper_of', Y, X],prv,_,_) \ fact(['a1:P49_has_former_or_current_keeper', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P38i_was_deassigned_by', X, Y],prv,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141i_was_assigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P145i_left_by', _, X1],prv,_,_) \ fact(['a1:E86_Leaving', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E86_Leaving', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P91_has_unit', X, X2],prv,_,_), fact(['a1:P91_has_unit', X, X1],prv,_,_), fact(['a1:E54_Dimension', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a2:relationship', _, X1],prv,_,_) \ fact(['a2:Relationship', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Relationship', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P73i_is_translation_of', X, _],prv,_,_) \ fact(['a1:E33_Linguistic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E33_Linguistic_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P75i_is_possessed_by', X, _],prv,_,_) \ fact(['a1:E30_Right', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E30_Right', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:principal', X, Y],prv,M1,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a3:OnlineEcommerceAccount', X],prv,M1,_) \ fact(['a3:OnlineAccount', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:OnlineAccount', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P2i_is_type_of', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E31_Document', X],prv,_,_) \ fact(['a1:P_E31_Document', X, X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P_E31_Document', X, X],prv,_,U), applied_rules(1,fwd).
fact(['a2:principal', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P144i_gained_member_by', X, _],prv,_,_) \ fact(['a1:E74_Group', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P74i_is_current_or_former_residence_of', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:holdsAccount', _, X1],prv,M1,_) \ fact(['a3:OnlineAccount', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:OnlineAccount', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P90_has_value', X, _],prv,M1,_) \ fact(['a1:E54_Dimension', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:weblog', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P41i_was_classified_by', _, X1],prv,_,_) \ fact(['a1:E17_Type_Assignment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E17_Type_Assignment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P123_resulted_in', X, Y],prv,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92_brought_into_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P93_took_out_of_existence', X, _],prv,_,_) \ fact(['a1:E64_End_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E64_End_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:concurrentEvent', X, Y],prv,_,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P49i_is_former_or_current_keeper_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['rdfs:Datatype', X],prv,M1,_) \ fact(['rdfs:Class', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Class', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P111i_was_added_by', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:father', X, _],prv,M1,_), fact(['a2:mother', X, _],prv,M2,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a2:father',M1),('a2:mother',M2)],M), fact(['a3:Person', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:P125i_was_type_of_object_used_in', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P145_separated', X, Y],prv,_,_) \ fact(['a1:P11_had_participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11_had_participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P57_has_number_of_parts', X, _],prv,M1,_) \ fact(['a1:E19_Physical_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P39_measured', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Investiture', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P147_curated', X, _],prv,_,_) \ fact(['a1:E87_Curation_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E87_Curation_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P138i_has_representation', _, X1],prv,_,_) \ fact(['a1:E36_Visual_Item', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E36_Visual_Item', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P67i_is_referred_to_by', Y, X],prv,_,_) \ fact(['a1:P67_refers_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67_refers_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P67_refers_to', Y, X],prv,_,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67i_is_referred_to_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P50_has_current_keeper', Y, X],prv,_,_) \ fact(['a1:P50i_is_current_keeper_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P50i_is_current_keeper_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P50i_is_current_keeper_of', Y, X],prv,_,_) \ fact(['a1:P50_has_current_keeper', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P50_has_current_keeper', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P138_represents', X, _],prv,_,_) \ fact(['a1:E36_Visual_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E36_Visual_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P73_has_translation', X, Y],prv,_,_) \ fact(['a1:P130_shows_features_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P130_shows_features_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:concurrentEvent', X, _],prv,_,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a5:PeriodOfTime', X],prv,M1,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:LocationPeriodOrJurisdiction', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P143i_was_joined_by', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P121_overlaps_with', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P34i_was_assessed_by', Y, X],prv,_,_) \ fact(['a1:P34_concerned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P34_concerned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P34_concerned', Y, X],prv,_,_) \ fact(['a1:P34i_was_assessed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P34i_was_assessed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P108i_was_produced_by', _, X1],prv,_,_) \ fact(['a1:E12_Production', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E12_Production', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P140i_was_attributed_by', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P117i_includes', X, Y],prv,_,_), fact(['a1:P117i_includes', Y, Z],prv,_,_) \ fact(['a1:P117i_includes', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P117i_includes', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P102i_is_title_of', X, Y],prv,_,_) \ fact(['a1:P1i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P67_refers_to', X0, X1],prv,_,_), fact(['a1:P67_refers_to', X2, X1],prv,_,_) \ fact(['a1:referToSame', X0, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:referToSame', X0, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:E71_Man-Made_Thing', X],prv,_,_) \ fact(['a1:E70_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P141_assigned', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P74_has_current_or_former_residence', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P84i_was_maximum_duration_of', Y, X],prv,_,_) \ fact(['a1:P84_had_at_most_duration', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P84_had_at_most_duration', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P84_had_at_most_duration', Y, X],prv,_,_) \ fact(['a1:P84i_was_maximum_duration_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P84i_was_maximum_duration_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:weblog', X, Y],prv,M1,_) \ fact(['a3:page', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:page', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E77_Persistent_Item', X],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P104i_applies_to', Y, X],prv,_,_) \ fact(['a1:P104_is_subject_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P104_is_subject_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P104_is_subject_to', Y, X],prv,_,_) \ fact(['a1:P104i_applies_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P104i_applies_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E87_Curation_Activity', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:isPrimaryTopicOf', Y1, X],prv,_,_), fact(['a3:isPrimaryTopicOf', Y2, X],prv,_,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', Y1, Y2],prv,_,U), applied_rules(1,fwd).
fact(['a2:Relationship', X],prv,_,_) \ fact(['a6:Relationship', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a6:Relationship', X],prv,_,U), applied_rules(1,fwd).
fact(['a6:Relationship', X],prv,_,_) \ fact(['a2:Relationship', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Relationship', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:logo', Y1, X],prv,M1,_), fact(['a3:logo', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:logo',M1),('a3:logo',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P92_brought_into_existence', X, _],prv,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E63_Beginning_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E48_Place_Name', X],prv,M1,_) \ fact(['a1:E44_Place_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E44_Place_Appellation', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P143i_was_joined_by', X, Y],prv,_,_) \ fact(['a1:P11i_participated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11i_participated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E2_Temporal_Entity', X],prv,_,_), fact(['a1:E77_Persistent_Item', X],prv,_,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:Nothing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P54i_is_current_permanent_location_of', _, X1],prv,_,_) \ fact(['a1:E19_Physical_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P145_separated', X, X2],prv,_,_), fact(['a1:P145_separated', X, X1],prv,_,_), fact(['a1:E86_Leaving', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P99i_was_dissolved_by', X, Y],prv,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:Inauguration', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P125_used_object_of_type', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P25i_moved_by', _, X1],prv,_,_) \ fact(['a1:E9_Move', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E9_Move', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P72i_is_language_of', Y, X],prv,_,_) \ fact(['a1:P72_has_language', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P72_has_language', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P72_has_language', Y, X],prv,_,_) \ fact(['a1:P72i_is_language_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P72i_is_language_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P101i_was_use_of', _, X1],prv,_,_) \ fact(['a1:E70_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P123i_resulted_from', X, _],prv,_,_) \ fact(['a1:E77_Persistent_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E66_Formation', X],prv,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E63_Beginning_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P1i_identifies', X, _],prv,_,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a5:SizeOrDuration', X],prv,M1,_) \ fact(['a5:MediaTypeOrExtent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:MediaTypeOrExtent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P92_brought_into_existence', Y, X],prv,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P92i_was_brought_into_existence_by', Y, X],prv,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92_brought_into_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:icqChatID', Y1, X],prv,M1,_), fact(['a3:icqChatID', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:icqChatID',M1),('a3:icqChatID',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a3:OnlineChatAccount', X],prv,M1,_) \ fact(['a3:OnlineAccount', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:OnlineAccount', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P97_from_father', _, X1],prv,_,_) \ fact(['a1:E21_Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E21_Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P65i_is_shown_by', _, X1],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P86i_contains', X, Y],prv,_,_), fact(['a1:P86i_contains', Y, Z],prv,_,_) \ fact(['a1:P86i_contains', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P86i_contains', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a2:Coronation', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P148i_is_component_of', X, _],prv,_,_) \ fact(['a1:E89_Propositional_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P34i_was_assessed_by', _, X1],prv,_,_) \ fact(['a1:E14_Condition_Assessment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E14_Condition_Assessment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P49_has_former_or_current_keeper', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P43i_is_dimension_of', _, X1],prv,_,_) \ fact(['a1:E70_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P143i_was_joined_by', _, X1],prv,_,_) \ fact(['a1:E85_Joining', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E85_Joining', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P21_had_general_purpose', Y, X],prv,_,_) \ fact(['a1:P21i_was_purpose_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P21i_was_purpose_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P21i_was_purpose_of', Y, X],prv,_,_) \ fact(['a1:P21_had_general_purpose', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P21_had_general_purpose', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P87i_identifies', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Funeral', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P11i_participated_in', Y, X],prv,_,_) \ fact(['a1:P11_had_participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11_had_participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P11_had_participant', Y, X],prv,_,_) \ fact(['a1:P11i_participated_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11i_participated_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P111_added', Y, X],prv,_,_) \ fact(['a1:P111i_was_added_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P111i_was_added_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P111i_was_added_by', Y, X],prv,_,_) \ fact(['a1:P111_added', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P111_added', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P67_refers_to', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E73_Information_Object', X],prv,_,_) \ fact(['a1:P_E73_Information_Object', X, X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P_E73_Information_Object', X, X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P113_removed', X, _],prv,_,_) \ fact(['a1:E80_Part_Removal', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E80_Part_Removal', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P142i_was_used_in', X, Y],prv,_,_) \ fact(['a1:P16i_was_used_for', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P16i_was_used_for', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:page', Y, X],prv,_,_) \ fact(['a3:topic', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:topic', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:topic', Y, X],prv,_,_) \ fact(['a3:page', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:page', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P135i_was_created_by', X, Y],prv,_,_) \ fact(['a1:P94i_was_created_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P94i_was_created_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P101_had_as_general_use', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:homepage', X, Y],prv,M1,_) \ fact(['a3:isPrimaryTopicOf', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:isPrimaryTopicOf', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P127i_has_narrower_term', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P25i_moved_by', Y, X],prv,_,_) \ fact(['a1:P25_moved', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P25_moved', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P25_moved', Y, X],prv,_,_) \ fact(['a1:P25i_moved_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P25i_moved_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P3_has_note', X, _],prv,M1,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P38_deassigned', X, Y],prv,_,_) \ fact(['a1:P141_assigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141_assigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E42_Identifier', X],prv,_,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P148_has_component', X, _],prv,_,_) \ fact(['a1:E89_Propositional_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P122_borders_with', Y, X],prv,_,_) \ fact(['a1:P122_borders_with', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P122_borders_with', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P59i_is_located_on_or_within', X, X2],prv,_,_), fact(['a1:P59i_is_located_on_or_within', X, X1],prv,_,_), fact(['a1:E53_Place', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P26i_was_destination_of', _, X1],prv,_,_) \ fact(['a1:E9_Move', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E9_Move', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:accountServiceHomepage', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P68_foresees_use_of', Y, X],prv,_,_) \ fact(['a1:P68i_use_foreseen_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P68i_use_foreseen_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P68i_use_foreseen_by', Y, X],prv,_,_) \ fact(['a1:P68_foresees_use_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P68_foresees_use_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:eventInterval', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P128_carries', _, X1],prv,_,_) \ fact(['a1:E73_Information_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E73_Information_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E65_Creation', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:mbox_sha1sum', _, X1],prv,M1,_) \ fact(['rdfs:Literal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Literal', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a2:interval', X, _],prv,M1,_) \ fact(['a2:Relationship', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Relationship', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P67_refers_to', X, Y],prv,_,_), fact(['a1:P67_refers_to', Y, Z],prv,_,_) \ fact(['a1:P67_refers_to', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P67_refers_to', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:E12_Production', X],prv,_,_) \ fact(['a1:E11_Modification', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E11_Modification', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P12i_was_present_at', X, _],prv,_,_) \ fact(['a1:E77_Persistent_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P48_has_preferred_identifier', X, X2],prv,_,_), fact(['a1:P48_has_preferred_identifier', X, X1],prv,_,_), fact(['a1:E1_CRM_Entity', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P148_has_component', _, X1],prv,_,_) \ fact(['a1:E89_Propositional_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P12_occurred_in_the_presence_of', _, X1],prv,_,_) \ fact(['a1:E77_Persistent_Item', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P31i_was_modified_by', X, _],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P94i_was_created_by', X, _],prv,_,_) \ fact(['a1:E28_Conceptual_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E28_Conceptual_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P107_has_current_or_former_member', X, _],prv,_,_) \ fact(['a1:E74_Group', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P103i_was_intention_of', X, _],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P12i_was_present_at', _, X1],prv,_,_) \ fact(['a1:E5_Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P42_assigned', X, Y],prv,_,_) \ fact(['a1:P141_assigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141_assigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P41_classified', X, _],prv,_,_) \ fact(['a1:E17_Type_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E17_Type_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P62i_is_depicted_by', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P4i_is_time-span_of', X, _],prv,_,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P106i_forms_part_of', X, _],prv,_,_) \ fact(['a1:E90_Symbolic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E90_Symbolic_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E26_Physical_Feature', X],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:immediatelyPrecedingEvent', X, Y],prv,M1,_) \ fact(['a2:precedingEvent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:precedingEvent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a2:Resignation', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:BarMitzvah', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E2_Temporal_Entity', X],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P123i_resulted_from', X, Y],prv,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E54_Dimension', X],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P131i_identifies', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Baptism', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P122_borders_with', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P94_has_created', X, Y],prv,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92_brought_into_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P115_finishes', X, Y],prv,_,_), fact(['a1:P115_finishes', Y, Z],prv,_,_) \ fact(['a1:P115_finishes', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P115_finishes', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a3:openid', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P1i_identifies', Y, X],prv,_,_) \ fact(['a1:P1_is_identified_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1_is_identified_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P1_is_identified_by', Y, X],prv,_,_) \ fact(['a1:P1i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P52_has_current_owner', X, Y],prv,_,_) \ fact(['a1:P51_has_former_or_current_owner', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P102i_is_title_of', Y, X],prv,_,_) \ fact(['a1:P102_has_title', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P102_has_title', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P102_has_title', Y, X],prv,_,_) \ fact(['a1:P102i_is_title_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P102i_is_title_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P59_has_section', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P79_beginning_is_qualified_by', X, _],prv,M1,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:jabberID', Y1, X],prv,M1,_), fact(['a3:jabberID', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:jabberID',M1),('a3:jabberID',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P140_assigned_attribute_to', Y, X],prv,_,_) \ fact(['a1:P140i_was_attributed_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P140i_was_attributed_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P140i_was_attributed_by', Y, X],prv,_,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P140_assigned_attribute_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P98_brought_into_life', _, X1],prv,_,_) \ fact(['a1:E21_Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E21_Person', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P8_took_place_on_or_within', X, _],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P8_took_place_on_or_within', _, X1],prv,_,_) \ fact(['a1:E19_Physical_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E22_Man-Made_Object', X],prv,_,_) \ fact(['a1:E19_Physical_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P114_is_equal_in_time_to', X, Y],prv,_,_), fact(['a1:P114_is_equal_in_time_to', Y, Z],prv,_,_) \ fact(['a1:P114_is_equal_in_time_to', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P114_is_equal_in_time_to', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E73_Information_Object', X0, X1],prv,_,_), fact(['a1:referredBySame', X1, X2],prv,_,_), fact(['a1:P_E73_Information_Object', X2, X3],prv,_,_) \ fact(['a1:relatedInformationObjects', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedInformationObjects', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a2:Burial', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P140i_was_attributed_by', _, X1],prv,_,_) \ fact(['a1:E13_Attribute_Assignment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E13_Attribute_Assignment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E53_Place', X],prv,_,_) \ fact(['a1:P_E53_Place', X, X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P_E53_Place', X, X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P23_transferred_title_from', Y, X],prv,_,_) \ fact(['a1:P23i_surrendered_title_through', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P23i_surrendered_title_through', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P23i_surrendered_title_through', Y, X],prv,_,_) \ fact(['a1:P23_transferred_title_from', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P23_transferred_title_from', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P27i_was_origin_of', X, Y],prv,_,_), fact(['a1:P27i_was_origin_of', Y, Z],prv,_,_) \ fact(['a1:P27i_was_origin_of', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P27i_was_origin_of', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P33i_was_used_by', X, _],prv,_,_) \ fact(['a1:E29_Design_or_Procedure', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E29_Design_or_Procedure', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P74i_is_current_or_former_residence_of', Y, X],prv,_,_) \ fact(['a1:P74_has_current_or_former_residence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P74_has_current_or_former_residence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P74_has_current_or_former_residence', Y, X],prv,_,_) \ fact(['a1:P74i_is_current_or_former_residence_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P74i_is_current_or_former_residence_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E90_Symbolic_Object', X],prv,_,_) \ fact(['a1:E28_Conceptual_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E28_Conceptual_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P107_has_current_or_former_member', Y, X],prv,_,_) \ fact(['a1:P107i_is_current_or_former_member_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P107i_is_current_or_former_member_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P107i_is_current_or_former_member_of', Y, X],prv,_,_) \ fact(['a1:P107_has_current_or_former_member', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P107_has_current_or_former_member', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P131i_identifies', X, Y],prv,_,_) \ fact(['a1:P1i_identifies', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P1i_identifies', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:keywords', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P87_is_identified_by', _, X1],prv,_,_) \ fact(['a1:E44_Place_Appellation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E44_Place_Appellation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P15i_influenced', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P109_has_current_or_former_curator', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P141i_was_assigned_by', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E16_Measurement', X],prv,_,_) \ fact(['a1:E13_Attribute_Assignment', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E13_Attribute_Assignment', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P124_transformed', _, X1],prv,_,_) \ fact(['a1:E77_Persistent_Item', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P120i_occurs_after', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E53_Place', X0, X1],prv,_,_), fact(['a1:P67_refers_to', X1, X2],prv,_,_), fact(['a1:P_E53_Place', X2, X3],prv,_,_) \ fact(['a1:relatedPlaces', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedPlaces', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a5:Agent', X],prv,_,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:Agent', X],prv,_,_) \ fact(['a5:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:Agent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P62_depicts', X, _],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P65_shows_visual_item', _, X1],prv,_,_) \ fact(['a1:E36_Visual_Item', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E36_Visual_Item', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:initiatingEvent', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P11i_participated_in', _, X1],prv,_,_) \ fact(['a1:E5_Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P39_measured', X, Y],prv,_,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P140_assigned_attribute_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P136i_supported_type_creation', _, X1],prv,_,_) \ fact(['a1:E83_Type_Creation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E83_Type_Creation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E55_Type', X],prv,_,_) \ fact(['a1:E28_Conceptual_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E28_Conceptual_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:officiator', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:relatedPlaces', Y, X],prv,_,_) \ fact(['a1:relatedPlaces', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedPlaces', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P147_curated', Y, X],prv,_,_) \ fact(['a1:P147i_was_curated_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P147i_was_curated_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P147i_was_curated_by', Y, X],prv,_,_) \ fact(['a1:P147_curated', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P147_curated', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P53_has_former_or_current_location', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Birth', X],prv,_,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:keywords', X, Y],prv,M1,_) \ fact(['a12:subject', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a12:subject', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P5_consists_of', X, _],prv,_,_) \ fact(['a1:E3_Condition_State', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E3_Condition_State', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:icqChatID', X, Y],prv,M1,_) \ fact(['a3:nick', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:nick', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P118i_is_overlapped_in_time_by', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P48_has_preferred_identifier', _, X1],prv,_,_) \ fact(['a1:E42_Identifier', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E42_Identifier', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P44i_is_condition_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P69_is_associated_with', X, _],prv,_,_) \ fact(['a1:E29_Design_or_Procedure', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E29_Design_or_Procedure', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E11_Modification', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P93i_was_taken_out_of_existence_by', Y, X],prv,_,_) \ fact(['a1:P93_took_out_of_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93_took_out_of_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P93_took_out_of_existence', Y, X],prv,_,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P109i_is_current_or_former_curator_of', _, X1],prv,_,_) \ fact(['a1:E78_Collection', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E78_Collection', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P76i_provides_access_to', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P94i_was_created_by', X, Y],prv,_,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E86_Leaving', X],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:Document', X],prv,M1,_), fact(['a3:Project', X],prv,M2,_) \ fact(['owl:Nothing', X],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:Document',M1),('a3:Project',M2)],M), fact(['owl:Nothing', X],prv,M,U), applied_rules(1,fwd).
fact(['a1:P20i_was_purpose_of', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Event', X],prv,_,_) \ fact(['a13:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a13:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P27_moved_from', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:birthday', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P143_joined', X, _],prv,_,_) \ fact(['a1:E85_Joining', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E85_Joining', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P115_finishes', Y, X],prv,_,_) \ fact(['a1:P115i_is_finished_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P115i_is_finished_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P115i_is_finished_by', Y, X],prv,_,_) \ fact(['a1:P115_finishes', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P115_finishes', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P25i_moved_by', X, _],prv,_,_) \ fact(['a1:E19_Physical_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:witness', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E38_Image', X],prv,M1,_) \ fact(['a1:E36_Visual_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E36_Visual_Item', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P73_has_translation', X, _],prv,_,_) \ fact(['a1:E33_Linguistic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E33_Linguistic_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P26i_was_destination_of', X, Y],prv,_,_) \ fact(['a1:P7i_witnessed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P7i_witnessed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:weblog', Y1, X],prv,M1,_), fact(['a3:weblog', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:weblog',M1),('a3:weblog',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P17i_motivated', X, Y],prv,_,_) \ fact(['a1:P15i_influenced', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15i_influenced', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P142_used_constituent', _, X1],prv,_,_) \ fact(['a1:E41_Appellation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P125i_was_type_of_object_used_in', Y, X],prv,_,_) \ fact(['a1:P125_used_object_of_type', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P125_used_object_of_type', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P125_used_object_of_type', Y, X],prv,_,_) \ fact(['a1:P125i_was_type_of_object_used_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:workplaceHomepage', _, X1],prv,M1,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P134i_was_continued_by', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E89_Propositional_Object', X],prv,_,_) \ fact(['a1:E28_Conceptual_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E28_Conceptual_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:skypeID', _, X1],prv,M1,_) \ fact(['rdfs:Literal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Literal', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a3:isPrimaryTopicOf', _, X1],prv,_,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P88_consists_of', Y, X],prv,_,_) \ fact(['a1:P88i_forms_part_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P88i_forms_part_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P88i_forms_part_of', Y, X],prv,_,_) \ fact(['a1:P88_consists_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P88_consists_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:relationship', Y, X],prv,_,_) \ fact(['a2:participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:participant', Y, X],prv,_,_) \ fact(['a2:relationship', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:relationship', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P21i_was_purpose_of', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P17_was_motivated_by', _, X1],prv,_,_) \ fact(['a1:E1_CRM_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P34_concerned', X, Y],prv,_,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P140_assigned_attribute_to', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P25_moved', X, _],prv,_,_) \ fact(['a1:E9_Move', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E9_Move', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Accession', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:interest', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E58_Measurement_Unit', X],prv,_,_) \ fact(['a1:E55_Type', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P105i_has_right_on', Y, X],prv,_,_) \ fact(['a1:P105_right_held_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P105_right_held_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P105_right_held_by', Y, X],prv,_,_) \ fact(['a1:P105i_has_right_on', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P105i_has_right_on', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:Assassination', X],prv,M1,_) \ fact(['a2:Murder', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Murder', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P108_has_produced', X, _],prv,_,_) \ fact(['a1:E12_Production', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E12_Production', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E35_Title', X],prv,_,_) \ fact(['a1:E33_Linguistic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E33_Linguistic_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:witness', X, Y],prv,M1,_) \ fact(['a2:spectator', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:spectator', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E83_Type_Creation', X],prv,_,_) \ fact(['a1:E65_Creation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E65_Creation', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:mother', X, Y1],prv,M1,_), fact(['a2:mother', X, Y2],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a2:mother',M1),('a2:mother',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P32i_was_technique_of', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P65_shows_visual_item', X, Y],prv,_,_) \ fact(['a1:P128_carries', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P128_carries', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P69_is_associated_with', _, X1],prv,_,_) \ fact(['a1:E29_Design_or_Procedure', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E29_Design_or_Procedure', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P135_created_type', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P22_transferred_title_to', X, Y],prv,_,_) \ fact(['a1:P14_carried_out_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14_carried_out_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P49_has_former_or_current_keeper', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P104i_applies_to', X, _],prv,_,_) \ fact(['a1:E30_Right', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E30_Right', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P86i_contains', Y, X],prv,_,_) \ fact(['a1:P86_falls_within', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P86_falls_within', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P86_falls_within', Y, X],prv,_,_) \ fact(['a1:P86i_contains', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P86i_contains', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P11_had_participant', X, _],prv,_,_) \ fact(['a1:E5_Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P2i_is_type_of', Y, X],prv,_,_) \ fact(['a1:P2_has_type', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P2_has_type', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P2_has_type', Y, X],prv,_,_) \ fact(['a1:P2i_is_type_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P2i_is_type_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:workplaceHomepage', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E52_Time-Span', X],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13i_was_destroyed_by', _, X1],prv,_,_) \ fact(['a1:E6_Destruction', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E6_Destruction', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P129_is_about', X, _],prv,_,_) \ fact(['a1:E89_Propositional_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P103i_was_intention_of', Y, X],prv,_,_) \ fact(['a1:P103_was_intended_for', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P103_was_intended_for', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P103_was_intended_for', Y, X],prv,_,_) \ fact(['a1:P103i_was_intention_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P103i_was_intention_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:birthday', X, Y1],prv,M1,_), fact(['a3:birthday', X, Y2],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:birthday',M1),('a3:birthday',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:E34_Inscription', X],prv,M1,_) \ fact(['a1:E33_Linguistic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E33_Linguistic_Object', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P21_had_general_purpose', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E69_Death', X],prv,_,_) \ fact(['a1:E64_End_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E64_End_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E18_Physical_Thing', X],prv,_,_) \ fact(['a1:E72_Legal_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E72_Legal_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P_E53_Place', X0, X1],prv,_,_), fact(['a1:referToSame', X1, X2],prv,_,_), fact(['a1:P_E53_Place', X2, X3],prv,_,_) \ fact(['a1:relatedPlaces', X0, X3],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:relatedPlaces', X0, X3],prv,_,U), applied_rules(1,fwd).
fact(['a1:P143_joined', X, Y],prv,_,_) \ fact(['a1:P11_had_participant', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P11_had_participant', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P35_has_identified', X, Y],prv,_,_) \ fact(['a1:P141_assigned', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141_assigned', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:employer', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P145_separated', X, _],prv,_,_) \ fact(['a1:E86_Leaving', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E86_Leaving', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P98i_was_born', X, X2],prv,_,_), fact(['a1:P98i_was_born', X, X1],prv,_,_), fact(['a1:E21_Person', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P114_is_equal_in_time_to', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P20i_was_purpose_of', X, _],prv,_,_) \ fact(['a1:E5_Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E5_Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P38i_was_deassigned_by', _, X1],prv,_,_) \ fact(['a1:E15_Identifier_Assignment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E15_Identifier_Assignment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P83_had_at_least_duration', _, X1],prv,_,_) \ fact(['a1:E54_Dimension', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E54_Dimension', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:page', _, X1],prv,_,_) \ fact(['a3:Document', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:precedingEvent', X, Y],prv,_,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P134i_was_continued_by', X, Y],prv,_,_) \ fact(['a1:P15i_influenced', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15i_influenced', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E67_Birth', X],prv,_,_) \ fact(['a1:E63_Beginning_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E63_Beginning_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P133_is_separated_from', _, X1],prv,_,_) \ fact(['a1:E4_Period', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:pastProject', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a2:concludingEvent', X, Y],prv,M1,_) \ fact(['owl:differentFrom', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:differentFrom', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P19_was_intended_use_of', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E35_Title', X],prv,_,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P98_brought_into_life', X, _],prv,_,_) \ fact(['a1:E67_Birth', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E67_Birth', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P68_foresees_use_of', _, X1],prv,_,_) \ fact(['a1:E57_Material', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E57_Material', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P33_used_specific_technique', X, Y],prv,_,_) \ fact(['a1:P16_used_specific_object', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P16_used_specific_object', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:precedingEvent', _, X1],prv,_,_) \ fact(['a2:Event', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P17i_motivated', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E68_Dissolution', X],prv,_,_) \ fact(['a1:E64_End_of_Existence', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E64_End_of_Existence', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],prv,_,_) \ fact(['a1:P12i_was_present_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P12i_was_present_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P52i_is_current_owner_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P120_occurs_before', X, Y],prv,_,_), fact(['a1:P120_occurs_before', Y, Z],prv,_,_) \ fact(['a1:P120_occurs_before', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P120_occurs_before', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P89i_contains', Y, X],prv,_,_) \ fact(['a1:P89_falls_within', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P89_falls_within', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P89_falls_within', Y, X],prv,_,_) \ fact(['a1:P89i_contains', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P89i_contains', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P121_overlaps_with', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P88_consists_of', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P129_is_about', Y, X],prv,_,_) \ fact(['a1:P129i_is_subject_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P129i_is_subject_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P129i_is_subject_of', Y, X],prv,_,_) \ fact(['a1:P129_is_about', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P129_is_about', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:state', X, Y],prv,M1,_) \ fact(['a2:agent', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:agent', X, Y],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P50i_is_current_keeper_of', X, Y],prv,_,_) \ fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:precedingEvent', X, Y],prv,_,_), fact(['a2:precedingEvent', Y, Z],prv,_,_) \ fact(['a2:precedingEvent', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:precedingEvent', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a3:member', X, _],prv,M1,_) \ fact(['a3:Group', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Group', X],prv,M1,U), applied_rules(1,fwd).
fact(['rdfs:Class', X],prv,_,_) \ fact(['rdfs:Resource', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['rdfs:Resource', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P4i_is_time-span_of', Y, X],prv,_,_) \ fact(['a1:P4_has_time-span', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P4_has_time-span', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P4_has_time-span', Y, X],prv,_,_) \ fact(['a1:P4i_is_time-span_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P4i_is_time-span_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P105_right_held_by', X, _],prv,_,_) \ fact(['a1:E72_Legal_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E72_Legal_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:aimChatID', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P122_borders_with', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a3:OnlineGamingAccount', X],prv,M1,_) \ fact(['a3:OnlineAccount', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:OnlineAccount', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P26_moved_to', X, Y],prv,_,_) \ fact(['a1:P7_took_place_at', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P7_took_place_at', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P31_has_modified', _, X1],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P83_had_at_least_duration', X, _],prv,_,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:GroupEvent', X],prv,_,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P86_falls_within', _, X1],prv,_,_) \ fact(['a1:E52_Time-Span', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:yahooChatID', Y1, X],prv,M1,_), fact(['a3:yahooChatID', Y2, X],prv,M2,_) \ fact(['owl:sameAs', Y1, Y2],O,_,U) <=> member(O,[chk,chk1]) | check_neg_mark([('a3:yahooChatID',M1),('a3:yahooChatID',M2)],M), fact(['owl:sameAs', Y1, Y2],prv,M,U), applied_rules(1,fwd).
fact(['a1:P106i_forms_part_of', Y, X],prv,_,_) \ fact(['a1:P106_is_composed_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P106_is_composed_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P106_is_composed_of', Y, X],prv,_,_) \ fact(['a1:P106i_forms_part_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P106i_forms_part_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P40i_was_observed_in', X, Y],prv,_,_) \ fact(['a1:P141i_was_assigned_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P141i_was_assigned_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P133_is_separated_from', Y, X],prv,_,_) \ fact(['a1:P133_is_separated_from', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P133_is_separated_from', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P130_shows_features_of', X, _],prv,_,_) \ fact(['a1:E70_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E70_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Interval', X],prv,_,_) \ fact(['a14:ProperInterval', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a14:ProperInterval', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P52i_is_current_owner_of', Y, X],prv,_,_) \ fact(['a1:P52_has_current_owner', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P52_has_current_owner', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P52_has_current_owner', Y, X],prv,_,_) \ fact(['a1:P52i_is_current_owner_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P52i_is_current_owner_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P100i_died_in', _, X1],prv,_,_) \ fact(['a1:E69_Death', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E69_Death', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:maker', Y, X],prv,_,_) \ fact(['a3:made', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:made', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a3:made', Y, X],prv,_,_) \ fact(['a3:maker', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:maker', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P124_transformed', X, _],prv,_,_) \ fact(['a1:E81_Transformation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E81_Transformation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:E82_Actor_Appellation', X],prv,_,_) \ fact(['a1:E41_Appellation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E41_Appellation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P32_used_general_technique', _, X1],prv,_,_) \ fact(['a1:E55_Type', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E55_Type', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P123i_resulted_from', Y, X],prv,_,_) \ fact(['a1:P123_resulted_in', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P123_resulted_in', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P123_resulted_in', Y, X],prv,_,_) \ fact(['a1:P123i_resulted_from', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P123i_resulted_from', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P10i_contains', X, Y],prv,_,_), fact(['a1:P10i_contains', Y, Z],prv,_,_) \ fact(['a1:P10i_contains', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P10i_contains', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P51i_is_former_or_current_owner_of', Y, X],prv,_,_) \ fact(['a1:P51_has_former_or_current_owner', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P51_has_former_or_current_owner', Y, X],prv,_,_) \ fact(['a1:P51i_is_former_or_current_owner_of', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P142i_was_used_in', _, X1],prv,_,_) \ fact(['a1:E15_Identifier_Assignment', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E15_Identifier_Assignment', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Death', X],prv,_,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P98_brought_into_life', X, Y],prv,_,_) \ fact(['a1:P92_brought_into_existence', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P92_brought_into_existence', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P93i_was_taken_out_of_existence_by', X, _],prv,_,_) \ fact(['a1:E77_Persistent_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P39_measured', Y, X],prv,_,_) \ fact(['a1:P39i_was_measured_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P39i_was_measured_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P39i_was_measured_by', Y, X],prv,_,_) \ fact(['a1:P39_measured', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P39_measured', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P116i_is_started_by', _, X1],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E41_Appellation', X],prv,_,_) \ fact(['a1:E90_Symbolic_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E90_Symbolic_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P106i_forms_part_of', X, Y],prv,_,_), fact(['a1:P106i_forms_part_of', Y, Z],prv,_,_) \ fact(['a1:P106i_forms_part_of', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P106i_forms_part_of', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:P50_has_current_keeper', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P9_consists_of', X, _],prv,_,_) \ fact(['a1:E4_Period', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P144_joined_with', _, X1],prv,_,_) \ fact(['a1:E74_Group', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E74_Group', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:publications', X, _],prv,M1,_) \ fact(['a3:Person', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P46_is_composed_of', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P59_has_section', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:E36_Visual_Item', X],prv,_,_) \ fact(['a1:E73_Information_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E73_Information_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P112i_was_diminished_by', _, X1],prv,_,_) \ fact(['a1:E80_Part_Removal', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E80_Part_Removal', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P11i_participated_in', X, _],prv,_,_) \ fact(['a1:E39_Actor', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P78_is_identified_by', X, _],prv,_,_) \ fact(['a1:E52_Time-Span', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P34_concerned', _, X1],prv,_,_) \ fact(['a1:E18_Physical_Thing', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P112i_was_diminished_by', X, _],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P136i_supported_type_creation', X, _],prv,_,_) \ fact(['a1:E1_CRM_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E1_CRM_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P144i_gained_member_by', Y, X],prv,_,_) \ fact(['a1:P144_joined_with', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P144_joined_with', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P144_joined_with', Y, X],prv,_,_) \ fact(['a1:P144i_gained_member_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P144i_gained_member_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:Cremation', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P119_meets_in_time_with', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Marriage', X],prv,_,_) \ fact(['a7:WeddingEvent_Generic', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a7:WeddingEvent_Generic', X],prv,_,U), applied_rules(1,fwd).
fact(['a7:WeddingEvent_Generic', X],prv,_,_) \ fact(['a2:Marriage', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Marriage', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P16i_was_used_for', _, X1],prv,_,_) \ fact(['a1:E7_Activity', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:Image', X],prv,_,_) \ fact(['a3:Document', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Document', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P143_joined', Y, X],prv,_,_) \ fact(['a1:P143i_was_joined_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P143i_was_joined_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P143i_was_joined_by', Y, X],prv,_,_) \ fact(['a1:P143_joined', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P143_joined', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P24i_changed_ownership_through', _, X1],prv,_,_) \ fact(['a1:E8_Acquisition', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E8_Acquisition', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P115i_is_finished_by', X, _],prv,_,_) \ fact(['a1:E2_Temporal_Entity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E2_Temporal_Entity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P103_was_intended_for', X, _],prv,_,_) \ fact(['a1:E71_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E71_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P53i_is_former_or_current_location_of', X, _],prv,_,_) \ fact(['a1:E53_Place', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P128_carries', X, _],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a5:LicenseDocument', X],prv,M1,_) \ fact(['a5:RightsStatement', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a5:RightsStatement', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P68_foresees_use_of', X, _],prv,_,_) \ fact(['a1:E29_Design_or_Procedure', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E29_Design_or_Procedure', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P89i_contains', _, X1],prv,_,_) \ fact(['a1:E53_Place', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E53_Place', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P20_had_specific_purpose', X, _],prv,_,_) \ fact(['a1:E7_Activity', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E7_Activity', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P46_is_composed_of', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P7i_witnessed', _, X1],prv,_,_) \ fact(['a1:E4_Period', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:Naturalization', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P23i_surrendered_title_through', X, Y],prv,_,_) \ fact(['a1:P14i_performed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14i_performed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:E30_Right', X],prv,_,_) \ fact(['a1:E89_Propositional_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E89_Propositional_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P9_consists_of', _, X1],prv,_,_) \ fact(['a1:E4_Period', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E4_Period', X1],prv,_,U), applied_rules(1,fwd).
fact(['a1:P106_is_composed_of', _, X1],prv,_,_) \ fact(['a1:E90_Symbolic_Object', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E90_Symbolic_Object', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:tipjar', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a3:account', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E70_Thing', X],prv,_,_) \ fact(['a1:E77_Persistent_Item', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E77_Persistent_Item', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P22i_acquired_title_through', X, Y],prv,_,_) \ fact(['a1:P14i_performed', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P14i_performed', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P27_moved_from', X, _],prv,_,_) \ fact(['a1:E9_Move', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E9_Move', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P105_right_held_by', _, X1],prv,_,_) \ fact(['a1:E39_Actor', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E39_Actor', X1],prv,_,U), applied_rules(1,fwd).
fact(['a3:icqChatID', X, _],prv,M1,_) \ fact(['a3:Agent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Agent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:E78_Collection', X],prv,_,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P13i_was_destroyed_by', X, X2],prv,_,_), fact(['a1:P13i_was_destroyed_by', X, X1],prv,_,_), fact(['a1:E18_Physical_Thing', X],prv,_,_) \ fact(['owl:sameAs', X1, X2],O,_,U) <=> member(O,[chk,chk1]) | fact(['owl:sameAs', X1, X2],prv,_,U), applied_rules(1,fwd).
fact(['a1:P136_was_based_on', X, Y],prv,_,_) \ fact(['a1:P15_was_influenced_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P15_was_influenced_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P16i_was_used_for', Y, X],prv,_,_) \ fact(['a1:P16_used_specific_object', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P16_used_specific_object', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P16_used_specific_object', Y, X],prv,_,_) \ fact(['a1:P16i_was_used_for', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P16i_was_used_for', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P88_consists_of', X, Y],prv,_,_), fact(['a1:P88_consists_of', Y, Z],prv,_,_) \ fact(['a1:P88_consists_of', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P88_consists_of', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a15:Performance', X],prv,_,_) \ fact(['a2:Performance', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Performance', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:Performance', X],prv,_,_) \ fact(['a15:Performance', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a15:Performance', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P54_has_current_permanent_location', X, _],prv,_,_) \ fact(['a1:E19_Physical_Object', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E19_Physical_Object', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P88i_forms_part_of', X, Y],prv,_,_), fact(['a1:P88i_forms_part_of', Y, Z],prv,_,_) \ fact(['a1:P88i_forms_part_of', X, Z],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P88i_forms_part_of', X, Z],prv,_,U), applied_rules(1,fwd).
fact(['a1:E25_Man-Made_Feature', X],prv,M1,_) \ fact(['a1:E26_Physical_Feature', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E26_Physical_Feature', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P94_has_created', X, _],prv,_,_) \ fact(['a1:E65_Creation', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E65_Creation', X],prv,_,U), applied_rules(1,fwd).
fact(['a1:P128_carries', Y, X],prv,_,_) \ fact(['a1:P128i_is_carried_by', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P128i_is_carried_by', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P128i_is_carried_by', Y, X],prv,_,_) \ fact(['a1:P128_carries', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P128_carries', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a2:Emigration', X],prv,M1,_) \ fact(['a2:IndividualEvent', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:IndividualEvent', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P112_diminished', X, Y],prv,_,_) \ fact(['a1:P31_has_modified', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P31_has_modified', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P33i_was_used_by', X, Y],prv,_,_) \ fact(['a1:P16i_was_used_for', X, Y],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:P16i_was_used_for', X, Y],prv,_,U), applied_rules(1,fwd).
fact(['a1:P83i_was_minimum_duration_of', _, X1],prv,_,_) \ fact(['a1:E52_Time-Span', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E52_Time-Span', X1],prv,_,U), applied_rules(1,fwd).
fact(['a2:organization', X, _],prv,M1,_) \ fact(['a2:Event', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a2:Event', X],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P113i_was_removed_by', X, _],prv,_,_) \ fact(['a1:E18_Physical_Thing', X],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E18_Physical_Thing', X],prv,_,U), applied_rules(1,fwd).
fact(['a2:child', _, X1],prv,M1,_) \ fact(['a3:Person', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a3:Person', X1],prv,M1,U), applied_rules(1,fwd).
fact(['a1:P78_is_identified_by', _, X1],prv,_,_) \ fact(['a1:E49_Time_Appellation', X1],O,_,U) <=> member(O,[chk,chk1]) | fact(['a1:E49_Time_Appellation', X1],prv,_,U), applied_rules(1,fwd).


% - backward -
fact(['a1:E8_Acquisition', X1],chk1,_,_), fact(['a1:P22i_acquired_title_through', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P22i_acquired_title_through', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E8_Acquisition', X],chk1,_,_), fact(['a1:P24_transferred_title_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P24_transferred_title_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E79_Part_Addition', X1],chk1,_,_), fact(['a1:P110i_was_augmented_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P110i_was_augmented_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P41_classified', X, X2],O1,M1,U1), fact(['a1:P41_classified', X, X1],O2,M2,U2), fact(['a1:E17_Type_Assignment', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P41_classified', X, X2],chk1,M1,U1), fact(['a1:P41_classified', X, X1],chk1,M2,U2), fact(['a1:E17_Type_Assignment', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P33_used_specific_technique', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P33_used_specific_technique', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P116_starts', X, Z],chk1,_,_), fact(['a1:P116_starts', X, Y],O1,M1,U1), fact(['a1:P116_starts', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P116_starts', X, Y],chk1,M1,U1), fact(['a1:P116_starts', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E81_Transformation', X1],chk1,_,_), fact(['a1:P124i_was_transformed_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P124i_was_transformed_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E72_Legal_Object', X],chk1,_,_), fact(['a1:P104_is_subject_to', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P104_is_subject_to', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P114_is_equal_in_time_to', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P114_is_equal_in_time_to', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P127i_has_narrower_term', X, Y],chk1,_,_), fact(['a1:P127_has_broader_term', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P127_has_broader_term', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P127_has_broader_term', X, Y],chk1,_,_), fact(['a1:P127i_has_narrower_term', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P127i_has_narrower_term', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:followingEvent', X, Z],chk1,_,_), fact(['a2:followingEvent', X, Y],O1,M1,U1), fact(['a2:followingEvent', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a2:followingEvent', X, Y],chk1,M1,U1), fact(['a2:followingEvent', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E37_Mark', X],chk1,_,_), fact(['a1:E34_Inscription', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E34_Inscription', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E65_Creation', X1],chk1,_,_), fact(['a1:P94i_was_created_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P94i_was_created_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Literal', X1],chk1,_,_), fact(['a3:aimChatID', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:aimChatID', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E5_Event', X],chk1,_,_), fact(['a1:E7_Activity', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E7_Activity', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Image', X1],chk1,_,_), fact(['a3:depiction', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:depiction', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E8_Acquisition', X],chk1,_,_), fact(['a1:P23_transferred_title_from', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P23_transferred_title_from', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Death', X],chk1,_,_), fact(['a2:Murder', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Murder', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E13_Attribute_Assignment', X],chk1,_,_), fact(['a1:E14_Condition_Assessment', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P31_has_modified', X, Y],chk1,_,_), fact(['a1:P108_has_produced', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108_has_produced', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P15i_influenced', X, Y],chk1,_,_), fact(['a1:P16i_was_used_for', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E81_Transformation', X1],chk1,_,_), fact(['a1:P123i_resulted_from', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P123i_resulted_from', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:homepage', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:homepage', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P96i_gave_birth', X, Y],chk1,_,_), fact(['a1:P96_by_mother', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P96_by_mother', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P96_by_mother', X, Y],chk1,_,_), fact(['a1:P96i_gave_birth', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P96i_gave_birth', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E69_Death', X],chk1,_,_), fact(['a1:P100_was_death_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P100_was_death_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P41i_was_classified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P41i_was_classified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P71i_is_listed_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P71i_is_listed_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P41_classified', X, Y],chk1,_,_), fact(['a1:P41i_was_classified_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P41i_was_classified_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P41i_was_classified_by', X, Y],chk1,_,_), fact(['a1:P41_classified', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P41_classified', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11_had_participant', X, Y],chk1,_,_), fact(['a1:P14_carried_out_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk1,_,_), fact(['a1:P93_took_out_of_existence', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P54_has_current_permanent_location', X, X2],O1,M1,U1), fact(['a1:P54_has_current_permanent_location', X, X1],O2,M2,U2), fact(['a1:E19_Physical_Object', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P54_has_current_permanent_location', X, X2],chk1,M1,U1), fact(['a1:P54_has_current_permanent_location', X, X1],chk1,M2,U2), fact(['a1:E19_Physical_Object', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:P11_had_participant', X, Y],chk1,_,_), fact(['a1:P146_separated_from', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P146_separated_from', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P17i_motivated', X, Y],chk1,_,_), fact(['a1:P17_was_motivated_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P17_was_motivated_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P17_was_motivated_by', X, Y],chk1,_,_), fact(['a1:P17i_motivated', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P17i_motivated', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P39i_was_measured_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P39i_was_measured_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P113_removed', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P113_removed', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P73i_is_translation_of', X, Y],chk1,_,_), fact(['a1:P73_has_translation', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P73_has_translation', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P73_has_translation', X, Y],chk1,_,_), fact(['a1:P73i_is_translation_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P73i_is_translation_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P2i_is_type_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P2i_is_type_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E13_Attribute_Assignment', X1],chk1,_,_), fact(['a1:P141i_was_assigned_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P141i_was_assigned_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1_is_identified_by', X, Y],chk1,_,_), fact(['a1:P102_has_title', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P102_has_title', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E42_Identifier', X1],chk1,_,_), fact(['a1:P38_deassigned', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P38_deassigned', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P54i_is_current_permanent_location_of', X, Y],chk1,_,_), fact(['a1:P54_has_current_permanent_location', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P54_has_current_permanent_location', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P54_has_current_permanent_location', X, Y],chk1,_,_), fact(['a1:P54i_is_current_permanent_location_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P54i_is_current_permanent_location_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E20_Biological_Object', X],chk1,_,_), fact(['a1:E21_Person', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E21_Person', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Resource', X],chk1,_,_), fact(['rdfs:Container', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['rdfs:Container', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:publications', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:publications', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedInformationObjects', X, Y],chk1,_,_), fact(['a1:relatedInformationObjects', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:relatedInformationObjects', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E11_Modification', X],chk1,_,_), fact(['a1:P126_employed', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P126_employed', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:death', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:death', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:GroupEvent', X],chk1,_,_), fact(['a2:Divorce', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Divorce', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:P108i_was_produced_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108i_was_produced_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E83_Type_Creation', X],chk1,_,_), fact(['a1:P136_was_based_on', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P136_was_based_on', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Graduation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Graduation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P29_custody_received_by', X, Y],chk1,_,_), fact(['a1:P29i_received_custody_through', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P29i_received_custody_through', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P29i_received_custody_through', X, Y],chk1,_,_), fact(['a1:P29_custody_received_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P29_custody_received_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P10i_contains', X, Y],chk1,_,_), fact(['a1:P10_falls_within', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P10_falls_within', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P10_falls_within', X, Y],chk1,_,_), fact(['a1:P10i_contains', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P10i_contains', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P55_has_current_location', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P55_has_current_location', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P16_used_specific_object', X, Y],chk1,_,_), fact(['a1:P142_used_constituent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P142_used_constituent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E78_Collection', X],chk1,_,_), fact(['a1:P147i_was_curated_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P147i_was_curated_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:E53_Place', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E53_Place', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E33_Linguistic_Object', X1],chk1,_,_), fact(['a1:P72i_is_language_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P72i_is_language_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67_refers_to', X, Y],chk1,_,_), fact(['a1:P70_documents', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P70_documents', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P93_took_out_of_existence', X, Y],chk1,_,_), fact(['a1:P124_transformed', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P124_transformed', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a4:Person', X],chk1,_,_), fact(['a3:Person', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:Person', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E71_Man-Made_Thing', X],chk1,_,_), fact(['a1:E24_Physical_Man-Made_Thing', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P148_has_component', X, Y],chk1,_,_), fact(['a1:P148i_is_component_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P148i_is_component_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P148i_is_component_of', X, Y],chk1,_,_), fact(['a1:P148_has_component', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P148_has_component', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P15_was_influenced_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P107_has_current_or_former_member', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P107_has_current_or_former_member', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:made', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:made', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P30i_custody_transferred_through', X, Y],chk1,_,_), fact(['a1:P30_transferred_custody_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P30_transferred_custody_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P30_transferred_custody_of', X, Y],chk1,_,_), fact(['a1:P30i_custody_transferred_through', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P30i_custody_transferred_through', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P125_used_object_of_type', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P125_used_object_of_type', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a2:birth', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:birth', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E63_Beginning_of_Existence', X],chk1,_,_), fact(['a1:E65_Creation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E65_Creation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E64_End_of_Existence', X],chk1,_,_), fact(['a1:E81_Transformation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E81_Transformation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P24_transferred_title_of', X, Y],chk1,_,_), fact(['a1:P24i_changed_ownership_through', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P24i_changed_ownership_through', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P24i_changed_ownership_through', X, Y],chk1,_,_), fact(['a1:P24_transferred_title_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P24_transferred_title_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:GroupEvent', X],chk1,_,_), fact(['a2:Annulment', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Annulment', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:PositionChange', X],chk1,_,_), fact(['a2:Promotion', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Promotion', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk1,_,_), fact(['a1:P31_has_modified', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Ordination', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Ordination', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X1],chk1,_,_), fact(['a1:P130_shows_features_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P130_shows_features_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P118_overlaps_in_time_with', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P118_overlaps_in_time_with', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E85_Joining', X1],chk1,_,_), fact(['a1:P144i_gained_member_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P144i_gained_member_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk1,_,_), fact(['a1:P124i_was_transformed_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P124i_was_transformed_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P15_was_influenced_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P15_was_influenced_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['a1:E79_Part_Addition', X],O1,M1,U1), fact(['a1:E80_Part_Removal', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:E79_Part_Addition', X],chk1,M1,U1), fact(['a1:E80_Part_Removal', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P94_has_created', X, Y],chk1,_,_), fact(['a1:P135_created_type', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P135_created_type', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P7_took_place_at', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P7_took_place_at', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:LocationPeriodOrJurisdiction', X],chk1,_,_), fact(['a5:Jurisdiction', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:Jurisdiction', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E26_Physical_Feature', X],chk1,_,_), fact(['a1:P56i_is_found_on', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P56i_is_found_on', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P1_is_identified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P126_employed', X, Y],chk1,_,_), fact(['a1:P126i_was_employed_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P126i_was_employed_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P126i_was_employed_in', X, Y],chk1,_,_), fact(['a1:P126_employed', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P126_employed', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:principal', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:principal', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:myersBriggs', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:myersBriggs', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:PositionChange', X],chk1,_,_), fact(['a2:Demotion', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Demotion', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a2:relationship', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:relationship', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P112i_was_diminished_by', X, Y],chk1,_,_), fact(['a1:P112_diminished', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P112_diminished', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P112_diminished', X, Y],chk1,_,_), fact(['a1:P112i_was_diminished_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P112i_was_diminished_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:isPrimaryTopicOf', X, Y],chk1,_,_), fact(['a3:openid', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:openid', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141i_was_assigned_by', X, Y],chk1,_,_), fact(['a1:P141_assigned', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P141_assigned', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141_assigned', X, Y],chk1,_,_), fact(['a1:P141i_was_assigned_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P141i_was_assigned_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P44_has_condition', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P44_has_condition', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P45_consists_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P45_consists_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P50i_is_current_keeper_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P50i_is_current_keeper_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P26i_was_destination_of', X, Y],chk1,_,_), fact(['a1:P26_moved_to', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P26_moved_to', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P26_moved_to', X, Y],chk1,_,_), fact(['a1:P26i_was_destination_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P26i_was_destination_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:depiction', X, Y],chk1,_,_), fact(['a3:img', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:img', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P24_transferred_title_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P24_transferred_title_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:P133_is_separated_from', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P133_is_separated_from', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P94i_was_created_by', X, Y],chk1,_,_), fact(['a1:P94_has_created', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P94_has_created', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P94_has_created', X, Y],chk1,_,_), fact(['a1:P94i_was_created_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P94i_was_created_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X1],chk1,_,_), fact(['a1:P67i_is_referred_to_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P9i_forms_part_of', X, Y],chk1,_,_), fact(['a1:P9_consists_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P9_consists_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P9_consists_of', X, Y],chk1,_,_), fact(['a1:P9i_forms_part_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P9i_forms_part_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P51_has_former_or_current_owner', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P51_has_former_or_current_owner', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E57_Material', X],chk1,_,_), fact(['a1:P68i_use_foreseen_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P68i_use_foreseen_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:IndividualEvent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:IndividualEvent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P138_represents', X, Y],chk1,_,_), fact(['a1:P138i_has_representation', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P138i_has_representation', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P138i_has_representation', X, Y],chk1,_,_), fact(['a1:P138_represents', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P138_represents', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P51_has_former_or_current_owner', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P51_has_former_or_current_owner', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['a3:Organization', X],O1,M1,U1), fact(['a3:Person', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:Organization', X],chk1,M1,U1), fact(['a3:Person', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:state', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:state', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a6:childOf', X, Y],chk1,_,_), fact(['a2:father', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:father', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P55i_currently_holds', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P55i_currently_holds', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E71_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P19_was_intended_use_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P19_was_intended_use_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E44_Place_Appellation', X],chk1,_,_), fact(['a1:E47_Spatial_Coordinates', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E47_Spatial_Coordinates', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:workInfoHomepage', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:workInfoHomepage', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:depiction', X, Y],chk1,_,_), fact(['a3:depicts', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:depicts', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:depicts', X, Y],chk1,_,_), fact(['a3:depiction', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:depiction', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Resource', X],chk1,_,_), fact(['rdfs:Literal', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['rdfs:Literal', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P105_right_held_by', X, Y],chk1,_,_), fact(['a1:P52_has_current_owner', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P52_has_current_owner', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X1],chk1,_,_), fact(['a2:concurrentEvent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:concurrentEvent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E46_Section_Definition', X1],chk1,_,_), fact(['a1:P58_has_section_definition', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P58_has_section_definition', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E21_Person', X],chk1,_,_), fact(['a1:P98i_was_born', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P98i_was_born', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:surname', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:surname', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X1],chk1,_,_), fact(['a1:P56i_is_found_on', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P56i_is_found_on', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E85_Joining', X],chk1,_,_), fact(['a1:P144_joined_with', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P144_joined_with', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X],chk1,_,_), fact(['a1:P130i_features_are_also_found_on', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P130i_features_are_also_found_on', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a2:event', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:event', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X],chk1,_,_), fact(['a1:P43_has_dimension', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P43_has_dimension', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P56i_is_found_on', X, Y],chk1,_,_), fact(['a1:P56_bears_feature', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P56_bears_feature', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P56_bears_feature', X, Y],chk1,_,_), fact(['a1:P56i_is_found_on', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P56i_is_found_on', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P83_had_at_least_duration', X, X2],O1,M1,U1), fact(['a1:P83_had_at_least_duration', X, X1],O2,M2,U2), fact(['a1:E52_Time-Span', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P83_had_at_least_duration', X, X2],chk1,M1,U1), fact(['a1:P83_had_at_least_duration', X, X1],chk1,M2,U2), fact(['a1:E52_Time-Span', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a2:Relationship', X],chk1,_,_), fact(['a2:participant', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:participant', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P140_assigned_attribute_to', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X1],chk1,_,_), fact(['a1:P4_has_time-span', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P4_has_time-span', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P13i_was_destroyed_by', X, Y],chk1,_,_), fact(['a1:P13_destroyed', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P13_destroyed', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P13_destroyed', X, Y],chk1,_,_), fact(['a1:P13i_was_destroyed_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P13i_was_destroyed_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X1],chk1,_,_), fact(['a1:P107i_is_current_or_former_member_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P107i_is_current_or_former_member_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E63_Beginning_of_Existence', X],chk1,_,_), fact(['a1:E12_Production', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E12_Production', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:employer', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:employer', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E13_Attribute_Assignment', X],chk1,_,_), fact(['a1:E15_Identifier_Assignment', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P117_occurs_during', X, Z],chk1,_,_), fact(['a1:P117_occurs_during', X, Y],O1,M1,U1), fact(['a1:P117_occurs_during', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P117_occurs_during', X, Y],chk1,M1,U1), fact(['a1:P117_occurs_during', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E5_Event', X],chk1,_,_), fact(['a1:E63_Beginning_of_Existence', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P117_occurs_during', X, Y],chk1,_,_), fact(['a1:P117i_includes', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P117i_includes', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P117i_includes', X, Y],chk1,_,_), fact(['a1:P117_occurs_during', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P117_occurs_during', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:P10i_contains', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P10i_contains', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P120i_occurs_after', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P120i_occurs_after', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14_carried_out_by', X, Y],chk1,_,_), fact(['a1:P28_custody_surrendered_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P28_custody_surrendered_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X1],chk1,_,_), fact(['a1:P84i_was_maximum_duration_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P84i_was_maximum_duration_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E15_Identifier_Assignment', X1],chk1,_,_), fact(['a1:P37i_was_assigned_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P37i_was_assigned_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P39_measured', X, X2],O1,M1,U1), fact(['a1:P39_measured', X, X1],O2,M2,U2), fact(['a1:E16_Measurement', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P39_measured', X, X2],chk1,M1,U1), fact(['a1:P39_measured', X, X1],chk1,M2,U2), fact(['a1:E16_Measurement', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E78_Collection', X1],chk1,_,_), fact(['a1:P147_curated', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P147_curated', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E68_Dissolution', X1],chk1,_,_), fact(['a1:P99i_was_dissolved_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99i_was_dissolved_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P65_shows_visual_item', X, Y],chk1,_,_), fact(['a1:P65i_is_shown_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P65i_is_shown_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P65i_is_shown_by', X, Y],chk1,_,_), fact(['a1:P65_shows_visual_item', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P65_shows_visual_item', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X],chk1,_,_), fact(['a1:P56_bears_feature', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P56_bears_feature', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E72_Legal_Object', X],chk1,_,_), fact(['a1:E90_Symbolic_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P120_occurs_before', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P120_occurs_before', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:E24_Physical_Man-Made_Thing', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E85_Joining', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E85_Joining', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P58_has_section_definition', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P58_has_section_definition', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E86_Leaving', X1],chk1,_,_), fact(['a1:P146i_lost_member_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P146i_lost_member_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X1],chk1,_,_), fact(['a1:P8i_witnessed', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P8i_witnessed', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E15_Identifier_Assignment', X],chk1,_,_), fact(['a1:P37_assigned', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P37_assigned', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P118_overlaps_in_time_with', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P118_overlaps_in_time_with', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:E4_Period', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E4_Period', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a7:Event', X],chk1,_,_), fact(['a2:Event', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Event', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:officiator', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:officiator', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P62i_is_depicted_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P62i_is_depicted_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E56_Language', X1],chk1,_,_), fact(['a1:P72_has_language', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P72_has_language', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67_refers_to', X, Y],chk1,_,_), fact(['a1:P138_represents', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P138_represents', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E31_Document', X1],chk1,_,_), fact(['a1:P70i_is_documented_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P70i_is_documented_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P32_used_general_technique', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P32_used_general_technique', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:nick', X, Y],chk1,_,_), fact(['a3:aimChatID', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:aimChatID', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E72_Legal_Object', X1],chk1,_,_), fact(['a1:P105i_has_right_on', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P105i_has_right_on', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:age', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:age', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P100i_died_in', X, Y],chk1,_,_), fact(['a1:P100_was_death_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P100_was_death_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P100_was_death_of', X, Y],chk1,_,_), fact(['a1:P100i_died_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P100i_died_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:skypeID', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:skypeID', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:participant', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:participant', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P11_had_participant', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P11_had_participant', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:father', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:father', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P82_at_some_time_within', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P82_at_some_time_within', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E11_Modification', X1],chk1,_,_), fact(['a1:P31i_was_modified_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P31i_was_modified_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:gender', X, Y1],O1,M1,U1), fact(['a3:gender', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:gender', X, Y1],chk1,M1,U1), fact(['a3:gender', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:relatedPlaces', X, Z],chk1,_,_), fact(['a1:relatedPlaces', X, Y],O1,M1,U1), fact(['a1:relatedPlaces', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:relatedPlaces', X, Y],chk1,M1,U1), fact(['a1:relatedPlaces', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E13_Attribute_Assignment', X],chk1,_,_), fact(['a1:P141_assigned', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P141_assigned', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['a3:Document', X],O1,M1,U1), fact(['a3:Organization', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:Document', X],chk1,M1,U1), fact(['a3:Organization', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E33_Linguistic_Object', X],chk1,_,_), fact(['a1:P72_has_language', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P72_has_language', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P105i_has_right_on', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P105i_has_right_on', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E67_Birth', X],chk1,_,_), fact(['a1:P97_from_father', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P97_from_father', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:P110i_was_augmented_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P110i_was_augmented_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P136i_supported_type_creation', X, Y],chk1,_,_), fact(['a1:P136_was_based_on', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P136_was_based_on', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P136_was_based_on', X, Y],chk1,_,_), fact(['a1:P136i_supported_type_creation', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P136i_supported_type_creation', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a1:P22i_acquired_title_through', Y1, X],O1,M1,U1), fact(['a1:P22i_acquired_title_through', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P22i_acquired_title_through', Y1, X],chk1,M1,U1), fact(['a1:P22i_acquired_title_through', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P93_took_out_of_existence', X, Y],chk1,_,_), fact(['a1:P100_was_death_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P100_was_death_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P45i_is_incorporated_in', X, Y],chk1,_,_), fact(['a1:P45_consists_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P45_consists_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P45_consists_of', X, Y],chk1,_,_), fact(['a1:P45i_is_incorporated_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P45i_is_incorporated_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Literal', X1],chk1,_,_), fact(['a3:jabberID', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:jabberID', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X1],chk1,_,_), fact(['a1:P78i_identifies', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P78i_identifies', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X],chk1,_,_), fact(['a3:primaryTopic', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:primaryTopic', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P53i_is_former_or_current_location_of', X, Y],chk1,_,_), fact(['a1:P53_has_former_or_current_location', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P53_has_former_or_current_location', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P53_has_former_or_current_location', X, Y],chk1,_,_), fact(['a1:P53i_is_former_or_current_location_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P53i_is_former_or_current_location_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P37i_was_assigned_by', X, Y],chk1,_,_), fact(['a1:P37_assigned', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P37_assigned', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P37_assigned', X, Y],chk1,_,_), fact(['a1:P37i_was_assigned_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P37i_was_assigned_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:lastName', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:lastName', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X],chk1,_,_), fact(['a1:P84i_was_maximum_duration_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P84i_was_maximum_duration_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P125_used_object_of_type', X, Y],chk1,_,_), fact(['a1:P32_used_general_technique', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P32_used_general_technique', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P32i_was_technique_of', X, Y],chk1,_,_), fact(['a1:P32_used_general_technique', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P32_used_general_technique', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P32_used_general_technique', X, Y],chk1,_,_), fact(['a1:P32i_was_technique_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P32i_was_technique_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P59_has_section', X, Y],chk1,_,_), fact(['a1:P59i_is_located_on_or_within', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P59i_is_located_on_or_within', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P59i_is_located_on_or_within', X, Y],chk1,_,_), fact(['a1:P59_has_section', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P59_has_section', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:mbox', Y1, X],O1,M1,U1), fact(['a3:mbox', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:mbox', Y1, X],chk1,M1,U1), fact(['a3:mbox', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a2:GroupEvent', X],chk1,_,_), fact(['a2:Marriage', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Marriage', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E11_Modification', X],chk1,_,_), fact(['a1:E79_Part_Addition', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E79_Part_Addition', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P35i_was_identified_by', X, Y],chk1,_,_), fact(['a1:P35_has_identified', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P35_has_identified', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P35_has_identified', X, Y],chk1,_,_), fact(['a1:P35i_was_identified_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P35i_was_identified_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a8:Concept', X],chk1,_,_), fact(['a3:focus', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:focus', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Image', X1],chk1,_,_), fact(['a3:img', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:img', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:Organization', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:Organization', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:topic_interest', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:topic_interest', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Interval', X1],chk1,_,_), fact(['a2:eventInterval', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:eventInterval', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P116i_is_started_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P116i_is_started_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P31i_was_modified_by', X, Y],chk1,_,_), fact(['a1:P108i_was_produced_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108i_was_produced_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Birth', X1],chk1,_,_), fact(['a2:birth', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:birth', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P132_overlaps_with', X, Y],chk1,_,_), fact(['a1:P132_overlaps_with', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P132_overlaps_with', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P_E71_Man-Made_Thing', X, X],chk1,_,_), fact(['a1:E71_Man-Made_Thing', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E66_Formation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E66_Formation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E16_Measurement', X],chk1,_,_), fact(['a1:P40_observed_dimension', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P40_observed_dimension', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X1],chk1,_,_), fact(['a2:immediatelyPrecedingEvent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:immediatelyPrecedingEvent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P70_documents', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P70_documents', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P131_is_identified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P131_is_identified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E71_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P102i_is_title_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P102i_is_title_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12i_was_present_at', X, Y],chk1,_,_), fact(['a1:P11i_participated_in', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E10_Transfer_of_Custody', X],chk1,_,_), fact(['a1:P29_custody_received_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P29_custody_received_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:event', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:event', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:event', X, Y],chk1,_,_), fact(['a2:agent', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:agent', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E78_Collection', X],chk1,_,_), fact(['a1:P109_has_current_or_former_curator', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P109_has_current_or_former_curator', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P136_was_based_on', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P136_was_based_on', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P30_transferred_custody_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P30_transferred_custody_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:immediatelyFollowingEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:immediatelyFollowingEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X],chk1,_,_), fact(['a1:P124i_was_transformed_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P124i_was_transformed_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:P132_overlaps_with', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P132_overlaps_with', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P110i_was_augmented_by', X, Y],chk1,_,_), fact(['a1:P110_augmented', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P110_augmented', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P110_augmented', X, Y],chk1,_,_), fact(['a1:P110i_was_augmented_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P110i_was_augmented_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:P142i_was_used_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P142i_was_used_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:E21_Person', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E21_Person', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E3_Condition_State', X1],chk1,_,_), fact(['a1:P44_has_condition', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P44_has_condition', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P78i_identifies', X, Y],chk1,_,_), fact(['a1:P78_is_identified_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P78_is_identified_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P78_is_identified_by', X, Y],chk1,_,_), fact(['a1:P78i_identifies', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P78i_identifies', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P112_diminished', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P112_diminished', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X],chk1,_,_), fact(['a1:P8i_witnessed', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P8i_witnessed', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P5_consists_of', X, Y],chk1,_,_), fact(['a1:P5i_forms_part_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P5i_forms_part_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P5i_forms_part_of', X, Y],chk1,_,_), fact(['a1:P5_consists_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P5_consists_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P116_starts', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P116_starts', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E16_Measurement', X1],chk1,_,_), fact(['a1:P39i_was_measured_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P39i_was_measured_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:precedingEvent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:precedingEvent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedManMadeThings', X0, X3],chk1,_,_), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,M1,U1), fact(['a1:referToSame', X1, X2],O2,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E71_Man-Made_Thing', X0, X1],chk1,M1,U1), fact(['a1:referToSame', X1, X2],chk1,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P5i_forms_part_of', X, X2],O1,M1,U1), fact(['a1:P5i_forms_part_of', X, X1],O2,M2,U2), fact(['a1:E3_Condition_State', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P5i_forms_part_of', X, X2],chk1,M1,U1), fact(['a1:P5i_forms_part_of', X, X1],chk1,M2,U2), fact(['a1:E3_Condition_State', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E4_Period', X1],chk1,_,_), fact(['a1:P10i_contains', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P10i_contains', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P125i_was_type_of_object_used_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P138_represents', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P138_represents', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:P10_falls_within', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P10_falls_within', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E26_Physical_Feature', X1],chk1,_,_), fact(['a1:P56_bears_feature', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P56_bears_feature', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11i_participated_in', X, Y],chk1,_,_), fact(['a1:P99i_was_dissolved_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99i_was_dissolved_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['a1:E44_Place_Appellation', X],O1,M1,U1), fact(['a1:E49_Time_Appellation', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:E44_Place_Appellation', X],chk1,M1,U1), fact(['a1:E49_Time_Appellation', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P71_lists', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P71_lists', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:immediatelyPrecedingEvent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:immediatelyPrecedingEvent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a2:child', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:child', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a9:Event', X],chk1,_,_), fact(['a2:Event', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Event', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E58_Measurement_Unit', X],chk1,_,_), fact(['a1:P91i_is_unit_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P91i_is_unit_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E49_Time_Appellation', X],chk1,_,_), fact(['a1:E50_Date', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E50_Date', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14_carried_out_by', X, Y],chk1,_,_), fact(['a1:P23_transferred_title_from', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P23_transferred_title_from', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P110_augmented', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P110_augmented', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P55i_currently_holds', X, Y],chk1,_,_), fact(['a1:P55_has_current_location', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P55_has_current_location', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P55_has_current_location', X, Y],chk1,_,_), fact(['a1:P55i_currently_holds', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P55i_currently_holds', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedDocuments', X0, X3],chk1,_,_), fact(['a1:P_E31_Document', X0, X1],O1,M1,U1), fact(['a1:referredBySame', X1, X2],O2,M2,U2), fact(['a1:P_E31_Document', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E31_Document', X0, X1],chk1,M1,U1), fact(['a1:referredBySame', X1, X2],chk1,M2,U2), fact(['a1:P_E31_Document', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:relatedManMadeThings', X, Y],chk1,_,_), fact(['a1:relatedManMadeThings', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:relatedManMadeThings', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P74i_is_current_or_former_residence_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P74i_is_current_or_former_residence_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E71_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P103i_was_intention_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P103i_was_intention_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P84_had_at_most_duration', X, X2],O1,M1,U1), fact(['a1:P84_had_at_most_duration', X, X1],O2,M2,U2), fact(['a1:E52_Time-Span', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P84_had_at_most_duration', X, X2],chk1,M1,U1), fact(['a1:P84_had_at_most_duration', X, X1],chk1,M2,U2), fact(['a1:E52_Time-Span', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P88_consists_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P88_consists_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E83_Type_Creation', X1],chk1,_,_), fact(['a1:P135i_was_created_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P135i_was_created_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P119i_is_met_in_time_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P119i_is_met_in_time_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E16_Measurement', X],chk1,_,_), fact(['a1:P39_measured', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P39_measured', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E21_Person', X],chk1,_,_), fact(['a1:P97i_was_father_for', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P97i_was_father_for', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E17_Type_Assignment', X1],chk1,_,_), fact(['a1:P42i_was_assigned_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P42i_was_assigned_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12i_was_present_at', X, Y],chk1,_,_), fact(['a1:P16i_was_used_for', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E90_Symbolic_Object', X],chk1,_,_), fact(['a1:P106_is_composed_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P106_is_composed_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X1],chk1,_,_), fact(['a1:P43_has_dimension', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P43_has_dimension', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P81_ongoing_throughout', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P81_ongoing_throughout', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:family_name', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:family_name', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E13_Attribute_Assignment', X],chk1,_,_), fact(['a1:P140_assigned_attribute_to', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P70i_is_documented_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P70i_is_documented_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:P7_took_place_at', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P7_took_place_at', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P45i_is_incorporated_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P45i_is_incorporated_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E10_Transfer_of_Custody', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E33_Linguistic_Object', X1],chk1,_,_), fact(['a1:P73_has_translation', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P73_has_translation', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P95i_was_formed_by', X, X2],O1,M1,U1), fact(['a1:P95i_was_formed_by', X, X1],O2,M2,U2), fact(['a1:E74_Group', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P95i_was_formed_by', X, X2],chk1,M1,U1), fact(['a1:P95i_was_formed_by', X, X1],chk1,M2,U2), fact(['a1:E74_Group', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P134_continued', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P134_continued', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P138i_has_representation', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P138i_has_representation', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P109i_is_current_or_former_curator_of', X, Y],chk1,_,_), fact(['a1:P109_has_current_or_former_curator', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P109_has_current_or_former_curator', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P109_has_current_or_former_curator', X, Y],chk1,_,_), fact(['a1:P109i_is_current_or_former_curator_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P109i_is_current_or_former_curator_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk1,_,_), fact(['a1:P11_had_participant', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67_refers_to', X, Y],chk1,_,_), fact(['a1:P71_lists', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P71_lists', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P44i_is_condition_of', X, Y],chk1,_,_), fact(['a1:P44_has_condition', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P44_has_condition', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P44_has_condition', X, Y],chk1,_,_), fact(['a1:P44i_is_condition_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P44i_is_condition_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:openid', Y1, X],O1,M1,U1), fact(['a3:openid', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:openid', Y1, X],chk1,M1,U1), fact(['a3:openid', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E4_Period', X1],chk1,_,_), fact(['a1:P132_overlaps_with', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P132_overlaps_with', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E79_Part_Addition', X1],chk1,_,_), fact(['a1:P111i_was_added_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P111i_was_added_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E16_Measurement', X1],chk1,_,_), fact(['a1:P40i_was_observed_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P40i_was_observed_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E35_Title', X1],chk1,_,_), fact(['a1:P102_has_title', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P102_has_title', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P99_dissolved', X, Y],chk1,_,_), fact(['a1:P99i_was_dissolved_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99i_was_dissolved_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P99i_was_dissolved_by', X, Y],chk1,_,_), fact(['a1:P99_dissolved', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99_dissolved', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P119_meets_in_time_with', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P119_meets_in_time_with', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11_had_participant', X, Y],chk1,_,_), fact(['a1:P144_joined_with', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P144_joined_with', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:parent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:parent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P140_assigned_attribute_to', X, Y],chk1,_,_), fact(['a1:P41_classified', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P41_classified', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X1],chk1,_,_), fact(['a2:initiatingEvent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:initiatingEvent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E72_Legal_Object', X1],chk1,_,_), fact(['a1:P104i_applies_to', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P104i_applies_to', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E32_Authority_Document', X1],chk1,_,_), fact(['a1:P71i_is_listed_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P71i_is_listed_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E3_Condition_State', X],chk1,_,_), fact(['a1:P35i_was_identified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P35i_was_identified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:E57_Material', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E57_Material', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedPlaces', X0, X3],chk1,_,_), fact(['a1:P_E53_Place', X0, X1],O1,M1,U1), fact(['a1:referredBySame', X1, X2],O2,M2,U2), fact(['a1:P_E53_Place', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E53_Place', X0, X1],chk1,M1,U1), fact(['a1:referredBySame', X1, X2],chk1,M2,U2), fact(['a1:P_E53_Place', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P34i_was_assessed_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P34i_was_assessed_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P121_overlaps_with', X, Y],chk1,_,_), fact(['a1:P121_overlaps_with', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P121_overlaps_with', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E6_Destruction', X],chk1,_,_), fact(['a1:P13_destroyed', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P13_destroyed', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X1],chk1,_,_), fact(['a1:P84_had_at_most_duration', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P84_had_at_most_duration', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E57_Material', X1],chk1,_,_), fact(['a1:P45_consists_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P45_consists_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk1,_,_), fact(['a1:P100i_died_in', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P100i_died_in', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X1],chk1,_,_), fact(['a1:P123_resulted_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P123_resulted_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:E51_Contact_Point', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E51_Contact_Point', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a2:father', X, X2],O1,M1,U1), fact(['a2:father', X, X1],O2,M2,U2), fact(['a3:Person', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a2:father', X, X2],chk1,M1,U1), fact(['a2:father', X, X1],chk1,M2,U2), fact(['a3:Person', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['owl:sameAs', X3, X4],chk1,_,_), fact(['a2:mother', X, X4],O1,M1,U1), fact(['a2:mother', X, X3],O2,M2,U2), fact(['a3:Person', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a2:mother', X, X4],chk1,M1,U1), fact(['a2:mother', X, X3],chk1,M2,U2), fact(['a3:Person', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P9i_forms_part_of', X, X2],O1,M1,U1), fact(['a1:P9i_forms_part_of', X, X1],O2,M2,U2), fact(['a1:E4_Period', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P9i_forms_part_of', X, X2],chk1,M1,U1), fact(['a1:P9i_forms_part_of', X, X1],chk1,M2,U2), fact(['a1:E4_Period', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:P11_had_participant', X, Y],chk1,_,_), fact(['a1:P99_dissolved', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99_dissolved', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P15_was_influenced_by', X, Y],chk1,_,_), fact(['a1:P15i_influenced', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P15i_influenced', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P15i_influenced', X, Y],chk1,_,_), fact(['a1:P15_was_influenced_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P15_was_influenced_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X],chk1,_,_), fact(['a1:P67_refers_to', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P67_refers_to', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:parent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:parent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14_carried_out_by', X, Y],chk1,_,_), fact(['a1:P14i_performed', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P14i_performed', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14i_performed', X, Y],chk1,_,_), fact(['a1:P14_carried_out_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P14_carried_out_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X],chk1,_,_), fact(['a1:P55_has_current_location', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P55_has_current_location', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P95i_was_formed_by', X, Y],chk1,_,_), fact(['a1:P95_has_formed', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P95_has_formed', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P95_has_formed', X, Y],chk1,_,_), fact(['a1:P95i_was_formed_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P95i_was_formed_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X],chk1,_,_), fact(['a1:P95i_was_formed_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P95i_was_formed_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P42i_was_assigned_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P42i_was_assigned_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E28_Conceptual_Object', X1],chk1,_,_), fact(['a1:P94_has_created', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P94_has_created', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E82_Actor_Appellation', X1],chk1,_,_), fact(['a1:P131_is_identified_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P131_is_identified_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a10:SpatialThing', X1],chk1,_,_), fact(['a3:based_near', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:based_near', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P108i_was_produced_by', X, Y],chk1,_,_), fact(['a1:P108_has_produced', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108_has_produced', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P108_has_produced', X, Y],chk1,_,_), fact(['a1:P108i_was_produced_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108i_was_produced_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P31i_was_modified_by', X, Y],chk1,_,_), fact(['a1:P112i_was_diminished_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P112i_was_diminished_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E44_Place_Appellation', X],chk1,_,_), fact(['a1:E46_Section_Definition', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E46_Section_Definition', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P58_has_section_definition', X, Y],chk1,_,_), fact(['a1:P58i_defines_section', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P58i_defines_section', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P58i_defines_section', X, Y],chk1,_,_), fact(['a1:P58_has_section_definition', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P58_has_section_definition', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:age', X, Y1],O1,M1,U1), fact(['a3:age', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:age', X, Y1],chk1,M1,U1), fact(['a3:age', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E8_Acquisition', X1],chk1,_,_), fact(['a1:P23i_surrendered_title_through', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P23i_surrendered_title_through', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1_is_identified_by', X, Y],chk1,_,_), fact(['a1:P78_is_identified_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P78_is_identified_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P7i_witnessed', X, Y],chk1,_,_), fact(['a1:P27i_was_origin_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P27i_was_origin_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:currentProject', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:currentProject', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P119i_is_met_in_time_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P119i_is_met_in_time_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:aimChatID', Y1, X],O1,M1,U1), fact(['a3:aimChatID', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:aimChatID', Y1, X],chk1,M1,U1), fact(['a3:aimChatID', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P27_moved_from', X, Y],chk1,_,_), fact(['a1:P27i_was_origin_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P27i_was_origin_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P27i_was_origin_of', X, Y],chk1,_,_), fact(['a1:P27_moved_from', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P27_moved_from', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E42_Identifier', X1],chk1,_,_), fact(['a1:P37_assigned', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P37_assigned', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P116_starts', X, Y],chk1,_,_), fact(['a1:P116i_is_started_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P116i_is_started_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P116i_is_started_by', X, Y],chk1,_,_), fact(['a1:P116_starts', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P116_starts', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X],chk1,_,_), fact(['a3:sha1', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:sha1', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X1],chk1,_,_), fact(['a2:agent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:agent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E5_Event', X],chk1,_,_), fact(['a1:P12_occurred_in_the_presence_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P117i_includes', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P117i_includes', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14i_performed', X, Y],chk1,_,_), fact(['a1:P29i_received_custody_through', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P29i_received_custody_through', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E71_Man-Made_Thing', X],chk1,_,_), fact(['a1:P102_has_title', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P102_has_title', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P118_overlaps_in_time_with', X, Y],chk1,_,_), fact(['a1:P118i_is_overlapped_in_time_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P118i_is_overlapped_in_time_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P118i_is_overlapped_in_time_by', X, Y],chk1,_,_), fact(['a1:P118_overlaps_in_time_with', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P118_overlaps_in_time_with', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P89_falls_within', X, Z],chk1,_,_), fact(['a1:P89_falls_within', X, Y],O1,M1,U1), fact(['a1:P89_falls_within', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P89_falls_within', X, Y],chk1,M1,U1), fact(['a1:P89_falls_within', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P67i_is_referred_to_by', X, Y],chk1,_,_), fact(['a1:P138i_has_representation', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P138i_has_representation', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a2:father', X, Y1],O1,M1,U1), fact(['a2:father', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a2:father', X, Y1],chk1,M1,U1), fact(['a2:father', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:status', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:status', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P2_has_type', X, Y],chk1,_,_), fact(['a1:P137_exemplifies', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P137_exemplifies', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:event', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:event', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:followingEvent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:followingEvent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:E49_Time_Appellation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E49_Time_Appellation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:witness', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:witness', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1i_identifies', X, Y],chk1,_,_), fact(['a1:P48i_is_preferred_identifier_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P48i_is_preferred_identifier_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P26i_was_destination_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P26i_was_destination_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:openid', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:openid', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:organization', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:organization', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P14i_performed', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P14i_performed', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E42_Identifier', X],chk1,_,_), fact(['a1:P48i_is_preferred_identifier_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P48i_is_preferred_identifier_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:plan', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:plan', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P140i_was_attributed_by', X, Y],chk1,_,_), fact(['a1:P34i_was_assessed_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P34i_was_assessed_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P131i_identifies', X, Y],chk1,_,_), fact(['a1:P131_is_identified_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P131_is_identified_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P131_is_identified_by', X, Y],chk1,_,_), fact(['a1:P131i_identifies', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P131i_identifies', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X1],chk1,_,_), fact(['a1:P148i_is_component_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P148i_is_component_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X1],chk1,_,_), fact(['a1:P1_is_identified_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P1_is_identified_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P129_is_about', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P129_is_about', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P115i_is_finished_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P115i_is_finished_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P42i_was_assigned_by', X, Y],chk1,_,_), fact(['a1:P42_assigned', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P42_assigned', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P42_assigned', X, Y],chk1,_,_), fact(['a1:P42i_was_assigned_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P42i_was_assigned_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X1],chk1,_,_), fact(['a2:employer', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:employer', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E11_Modification', X],chk1,_,_), fact(['a1:P31_has_modified', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P31_has_modified', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P87i_identifies', X, Y],chk1,_,_), fact(['a1:P87_is_identified_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P87_is_identified_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P87_is_identified_by', X, Y],chk1,_,_), fact(['a1:P87i_identifies', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P87i_identifies', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:spectator', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:spectator', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E71_Man-Made_Thing', X],chk1,_,_), fact(['a1:E28_Conceptual_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E68_Dissolution', X],chk1,_,_), fact(['a1:P99_dissolved', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99_dissolved', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:event', X, Y],chk1,_,_), fact(['a2:birth', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:birth', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P135i_was_created_by', X, X2],O1,M1,U1), fact(['a1:P135i_was_created_by', X, X1],O2,M2,U2), fact(['a1:E55_Type', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P135i_was_created_by', X, X2],chk1,M1,U1), fact(['a1:P135i_was_created_by', X, X1],chk1,M2,U2), fact(['a1:E55_Type', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E9_Move', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E9_Move', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P128i_is_carried_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P128i_is_carried_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67i_is_referred_to_by', X, Y],chk1,_,_), fact(['a1:P71i_is_listed_in', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P71i_is_listed_in', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E3_Condition_State', X1],chk1,_,_), fact(['a1:P5_consists_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P5_consists_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E49_Time_Appellation', X],chk1,_,_), fact(['a1:P78i_identifies', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P78i_identifies', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P128i_is_carried_by', X, Y],chk1,_,_), fact(['a1:P65i_is_shown_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P65i_is_shown_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E8_Acquisition', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E8_Acquisition', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X1],chk1,_,_), fact(['a2:followingEvent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:followingEvent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Literal', X1],chk1,_,_), fact(['a3:icqChatID', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:icqChatID', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:MediaType', X],chk1,_,_), fact(['a5:PhysicalMedium', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:PhysicalMedium', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P70_documents', X, Y],chk1,_,_), fact(['a1:P70i_is_documented_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P70i_is_documented_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P70i_is_documented_in', X, Y],chk1,_,_), fact(['a1:P70_documents', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P70_documents', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:E75_Conceptual_Object_Appellation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E75_Conceptual_Object_Appellation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X],chk1,_,_), fact(['a1:P83i_was_minimum_duration_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P83i_was_minimum_duration_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:Group', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:Group', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E57_Material', X1],chk1,_,_), fact(['a1:P126_employed', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P126_employed', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X],chk1,_,_), fact(['a1:P40i_was_observed_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P40i_was_observed_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:agent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:agent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E32_Authority_Document', X],chk1,_,_), fact(['a1:P71_lists', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P71_lists', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P32i_was_technique_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P32i_was_technique_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X],chk1,_,_), fact(['a1:E20_Biological_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E20_Biological_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E44_Place_Appellation', X],chk1,_,_), fact(['a1:P87i_identifies', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P87i_identifies', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X1],chk1,_,_), fact(['a1:P130i_features_are_also_found_on', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P130i_features_are_also_found_on', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P119_meets_in_time_with', X, Y],chk1,_,_), fact(['a1:P119i_is_met_in_time_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P119i_is_met_in_time_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P119i_is_met_in_time_by', X, Y],chk1,_,_), fact(['a1:P119_meets_in_time_with', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P119_meets_in_time_with', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:interest', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:interest', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11i_participated_in', X, Y],chk1,_,_), fact(['a1:P146i_lost_member_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P146i_lost_member_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P30i_custody_transferred_through', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P30i_custody_transferred_through', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E30_Right', X1],chk1,_,_), fact(['a1:P104_is_subject_to', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P104_is_subject_to', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E79_Part_Addition', X],chk1,_,_), fact(['a1:P110_augmented', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P110_augmented', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a10:SpatialThing', X],chk1,_,_), fact(['a3:based_near', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:based_near', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X1],chk1,_,_), fact(['a1:P16_used_specific_object', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16_used_specific_object', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X],chk1,_,_), fact(['a1:E72_Legal_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E72_Legal_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P67i_is_referred_to_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E80_Part_Removal', X],chk1,_,_), fact(['a1:P112_diminished', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P112_diminished', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:NameChange', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:NameChange', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E36_Visual_Item', X],chk1,_,_), fact(['a1:E37_Mark', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E37_Mark', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedInformationObjects', X0, X3],chk1,_,_), fact(['a1:P_E73_Information_Object', X0, X1],O1,M1,U1), fact(['a1:P67_refers_to', X1, X2],O2,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E73_Information_Object', X0, X1],chk1,M1,U1), fact(['a1:P67_refers_to', X1, X2],chk1,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a3:Image', X],chk1,_,_), fact(['a3:depicts', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:depicts', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:page', X, Y],chk1,_,_), fact(['a3:isPrimaryTopicOf', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:isPrimaryTopicOf', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X],chk1,_,_), fact(['a1:P146i_lost_member_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P146i_lost_member_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P59i_is_located_on_or_within', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P59i_is_located_on_or_within', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:referredBySame', X0, X2],chk1,_,_), fact(['a1:P67_refers_to', X1, X0],O1,M1,U1), fact(['a1:P67_refers_to', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P67_refers_to', X1, X0],chk1,M1,U1), fact(['a1:P67_refers_to', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E10_Transfer_of_Custody', X1],chk1,_,_), fact(['a1:P28i_surrendered_custody_through', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P28i_surrendered_custody_through', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1i_identifies', X, Y],chk1,_,_), fact(['a1:P87i_identifies', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P87i_identifies', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E29_Design_or_Procedure', X1],chk1,_,_), fact(['a1:P68i_use_foreseen_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P68i_use_foreseen_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P17i_motivated', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P17i_motivated', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a1:P22_transferred_title_to', X, Y1],O1,M1,U1), fact(['a1:P22_transferred_title_to', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P22_transferred_title_to', X, Y1],chk1,M1,U1), fact(['a1:P22_transferred_title_to', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P86i_contains', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P86i_contains', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12i_was_present_at', X, Y],chk1,_,_), fact(['a1:P25i_moved_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P25i_moved_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141_assigned', X, Y],chk1,_,_), fact(['a1:P40_observed_dimension', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P40_observed_dimension', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P46i_forms_part_of', X, Y],chk1,_,_), fact(['a1:P46_is_composed_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P46_is_composed_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P46_is_composed_of', X, Y],chk1,_,_), fact(['a1:P46i_forms_part_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P46i_forms_part_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1_is_identified_by', X, Y],chk1,_,_), fact(['a1:P48_has_preferred_identifier', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P48_has_preferred_identifier', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E58_Measurement_Unit', X1],chk1,_,_), fact(['a1:P91_has_unit', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P91_has_unit', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P127_has_broader_term', X, Z],chk1,_,_), fact(['a1:P127_has_broader_term', X, Y],O1,M1,U1), fact(['a1:P127_has_broader_term', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P127_has_broader_term', X, Y],chk1,M1,U1), fact(['a1:P127_has_broader_term', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a2:Event', X1],chk1,_,_), fact(['a2:event', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:event', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:E3_Condition_State', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E3_Condition_State', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:OnlineAccount', X],chk1,_,_), fact(['a3:accountServiceHomepage', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:accountServiceHomepage', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67i_is_referred_to_by', X, Y],chk1,_,_), fact(['a1:P70i_is_documented_in', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P70i_is_documented_in', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:holdsAccount', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:holdsAccount', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:refersToDocument', X0, X2],chk1,_,_), fact(['a1:P67_refers_to', X0, X1],O1,M1,U1), fact(['a1:P_E31_Document', X1, X2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P67_refers_to', X0, X1],chk1,M1,U1), fact(['a1:P_E31_Document', X1, X2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E74_Group', X1],chk1,_,_), fact(['a1:P146_separated_from', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P146_separated_from', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E57_Material', X],chk1,_,_), fact(['a1:P45i_is_incorporated_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P45i_is_incorporated_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P88i_forms_part_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P88i_forms_part_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P24i_changed_ownership_through', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P24i_changed_ownership_through', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:jabberID', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:jabberID', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X1],chk1,_,_), fact(['a2:participant', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:participant', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P4_has_time-span', X, X2],O1,M1,U1), fact(['a1:P4_has_time-span', X, X1],O2,M2,U2), fact(['a1:E2_Temporal_Entity', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P4_has_time-span', X, X2],chk1,M1,U1), fact(['a1:P4_has_time-span', X, X1],chk1,M2,U2), fact(['a1:E2_Temporal_Entity', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P55_has_current_location', X, X2],O1,M1,U1), fact(['a1:P55_has_current_location', X, X1],O2,M2,U2), fact(['a1:E19_Physical_Object', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P55_has_current_location', X, X2],chk1,M1,U1), fact(['a1:P55_has_current_location', X, X1],chk1,M2,U2), fact(['a1:E19_Physical_Object', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:P120i_occurs_after', X, Z],chk1,_,_), fact(['a1:P120i_occurs_after', X, Y],O1,M1,U1), fact(['a1:P120i_occurs_after', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P120i_occurs_after', X, Y],chk1,M1,U1), fact(['a1:P120i_occurs_after', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E13_Attribute_Assignment', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a3:knows', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:knows', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:weblog', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:weblog', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:PositionChange', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:PositionChange', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P134i_was_continued_by', X, Y],chk1,_,_), fact(['a1:P134_continued', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P134_continued', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P134_continued', X, Y],chk1,_,_), fact(['a1:P134i_was_continued_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P134i_was_continued_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14_carried_out_by', X, Y],chk1,_,_), fact(['a1:P29_custody_received_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P29_custody_received_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X],chk1,_,_), fact(['a1:P43i_is_dimension_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P43i_is_dimension_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P137_exemplifies', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P137_exemplifies', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E36_Visual_Item', X],chk1,_,_), fact(['a1:P65i_is_shown_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P65i_is_shown_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P91_has_unit', X, Y],chk1,_,_), fact(['a1:P91i_is_unit_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P91i_is_unit_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P91i_is_unit_of', X, Y],chk1,_,_), fact(['a1:P91_has_unit', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P91_has_unit', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P53_has_former_or_current_location', X, Y],chk1,_,_), fact(['a1:P55_has_current_location', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P55_has_current_location', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P13i_was_destroyed_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P13i_was_destroyed_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P145_separated', X, Y],chk1,_,_), fact(['a1:P145i_left_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P145i_left_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P145i_left_by', X, Y],chk1,_,_), fact(['a1:P145_separated', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P145_separated', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E66_Formation', X],chk1,_,_), fact(['a1:P95_has_formed', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P95_has_formed', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E42_Identifier', X],chk1,_,_), fact(['a1:P38i_was_deassigned_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P38i_was_deassigned_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:immediatelyPrecedingEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:immediatelyPrecedingEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:primaryTopic', X, Y],chk1,_,_), fact(['a3:isPrimaryTopicOf', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:isPrimaryTopicOf', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:isPrimaryTopicOf', X, Y],chk1,_,_), fact(['a3:primaryTopic', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:primaryTopic', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E15_Identifier_Assignment', X],chk1,_,_), fact(['a1:P38_deassigned', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P38_deassigned', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P15_was_influenced_by', X, Y],chk1,_,_), fact(['a1:P17_was_motivated_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P17_was_motivated_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P4i_is_time-span_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P4i_is_time-span_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedDocuments', X0, X3],chk1,_,_), fact(['a1:P_E31_Document', X0, X1],O1,M1,U1), fact(['a1:referToSame', X1, X2],O2,M2,U2), fact(['a1:P_E31_Document', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E31_Document', X0, X1],chk1,M1,U1), fact(['a1:referToSame', X1, X2],chk1,M2,U2), fact(['a1:P_E31_Document', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a2:GroupEvent', X],chk1,_,_), fact(['a2:Performance', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Performance', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X],chk1,_,_), fact(['a3:PersonalProfileDocument', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:PersonalProfileDocument', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P17_was_motivated_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P17_was_motivated_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P19i_was_made_for', X, Y],chk1,_,_), fact(['a1:P19_was_intended_use_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P19_was_intended_use_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P19_was_intended_use_of', X, Y],chk1,_,_), fact(['a1:P19i_was_made_for', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P19i_was_made_for', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E10_Transfer_of_Custody', X1],chk1,_,_), fact(['a1:P29i_received_custody_through', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P29i_received_custody_through', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E10_Transfer_of_Custody', X],chk1,_,_), fact(['a1:P30_transferred_custody_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P30_transferred_custody_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:nick', X, Y],chk1,_,_), fact(['a3:skypeID', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:skypeID', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P101i_was_use_of', X, Y],chk1,_,_), fact(['a1:P101_had_as_general_use', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P101_had_as_general_use', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P101_had_as_general_use', X, Y],chk1,_,_), fact(['a1:P101i_was_use_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P101i_was_use_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1_is_identified_by', X, Y],chk1,_,_), fact(['a1:P131_is_identified_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P131_is_identified_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P46i_forms_part_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P46i_forms_part_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P76_has_contact_point', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P76_has_contact_point', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a2:death', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:death', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:followingEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:followingEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P58i_defines_section', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P58i_defines_section', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X],chk1,_,_), fact(['a1:P16i_was_used_for', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk1,_,_), fact(['a1:P95i_was_formed_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P95i_was_formed_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedDocuments', X, Y],chk1,_,_), fact(['a1:relatedDocuments', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:relatedDocuments', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E30_Right', X1],chk1,_,_), fact(['a1:P75_possesses', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P75_possesses', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:E5_Event', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E5_Event', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E82_Actor_Appellation', X],chk1,_,_), fact(['a1:P131i_identifies', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P131i_identifies', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E14_Condition_Assessment', X],chk1,_,_), fact(['a1:P35_has_identified', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P35_has_identified', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P143_joined', X, X2],O1,M1,U1), fact(['a1:P143_joined', X, X1],O2,M2,U2), fact(['a1:E85_Joining', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P143_joined', X, X2],chk1,M1,U1), fact(['a1:P143_joined', X, X1],chk1,M2,U2), fact(['a1:E85_Joining', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P135i_was_created_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P135i_was_created_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P83i_was_minimum_duration_of', X, Y],chk1,_,_), fact(['a1:P83_had_at_least_duration', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P83_had_at_least_duration', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P83_had_at_least_duration', X, Y],chk1,_,_), fact(['a1:P83i_was_minimum_duration_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P83i_was_minimum_duration_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P113_removed', X, Y],chk1,_,_), fact(['a1:P113i_was_removed_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P113i_was_removed_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P113i_was_removed_by', X, Y],chk1,_,_), fact(['a1:P113_removed', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P113_removed', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P7_took_place_at', X, Y],chk1,_,_), fact(['a1:P27_moved_from', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P27_moved_from', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedInformationObjects', X0, X3],chk1,_,_), fact(['a1:P_E73_Information_Object', X0, X1],O1,M1,U1), fact(['a1:referToSame', X1, X2],O2,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E73_Information_Object', X0, X1],chk1,M1,U1), fact(['a1:referToSame', X1, X2],chk1,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:P92_brought_into_existence', X, Y],chk1,_,_), fact(['a1:P108_has_produced', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108_has_produced', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E73_Information_Object', X],chk1,_,_), fact(['a1:E31_Document', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E31_Document', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X],chk1,_,_), fact(['a1:E40_Legal_Body', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E40_Legal_Body', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P106_is_composed_of', X, Z],chk1,_,_), fact(['a1:P106_is_composed_of', X, Y],O1,M1,U1), fact(['a1:P106_is_composed_of', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P106_is_composed_of', X, Y],chk1,M1,U1), fact(['a1:P106_is_composed_of', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P62_depicts', X, Y],chk1,_,_), fact(['a1:P62i_is_depicted_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P62i_is_depicted_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P62i_is_depicted_by', X, Y],chk1,_,_), fact(['a1:P62_depicts', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P62_depicts', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:birth', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:birth', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X],chk1,_,_), fact(['a1:E39_Actor', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E39_Actor', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E5_Event', X],chk1,_,_), fact(['a1:E64_End_of_Existence', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P74_has_current_or_former_residence', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P74_has_current_or_former_residence', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P31i_was_modified_by', X, Y],chk1,_,_), fact(['a1:P110i_was_augmented_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P110i_was_augmented_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P105i_has_right_on', X, Y],chk1,_,_), fact(['a1:P52i_is_current_owner_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P52i_is_current_owner_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X],chk1,_,_), fact(['a1:P101_had_as_general_use', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P101_had_as_general_use', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P13_destroyed', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P13_destroyed', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E15_Identifier_Assignment', X],chk1,_,_), fact(['a1:P142_used_constituent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P142_used_constituent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E51_Contact_Point', X],chk1,_,_), fact(['a1:E45_Address', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E45_Address', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P43_has_dimension', X, Y],chk1,_,_), fact(['a1:P43i_is_dimension_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P43i_is_dimension_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P43i_is_dimension_of', X, Y],chk1,_,_), fact(['a1:P43_has_dimension', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P43_has_dimension', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P21_had_general_purpose', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P21_had_general_purpose', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:relationship', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:relationship', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Class', X],chk1,_,_), fact(['a5:AgentClass', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:AgentClass', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P31_has_modified', X, Y],chk1,_,_), fact(['a1:P31i_was_modified_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P31i_was_modified_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P31i_was_modified_by', X, Y],chk1,_,_), fact(['a1:P31_has_modified', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P31_has_modified', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:partner', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:partner', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P98_brought_into_life', X, Y],chk1,_,_), fact(['a1:P98i_was_born', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P98i_was_born', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P98i_was_born', X, Y],chk1,_,_), fact(['a1:P98_brought_into_life', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P98_brought_into_life', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:immediatelyFollowingEvent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:immediatelyFollowingEvent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P15_was_influenced_by', X, Y],chk1,_,_), fact(['a1:P134_continued', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P134_continued', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E3_Condition_State', X1],chk1,_,_), fact(['a1:P35_has_identified', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P35_has_identified', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P51i_is_former_or_current_owner_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a6:childOf', X, Y],chk1,_,_), fact(['a2:mother', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:mother', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P115_finishes', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P115_finishes', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Image', X1],chk1,_,_), fact(['a3:thumbnail', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:thumbnail', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P2_has_type', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P2_has_type', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E3_Condition_State', X1],chk1,_,_), fact(['a1:P5i_forms_part_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P5i_forms_part_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P22_transferred_title_to', X, Y],chk1,_,_), fact(['a1:P22i_acquired_title_through', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P22i_acquired_title_through', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P22i_acquired_title_through', X, Y],chk1,_,_), fact(['a1:P22_transferred_title_to', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P22_transferred_title_to', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X1],chk1,_,_), fact(['a1:P25_moved', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P25_moved', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P127_has_broader_term', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P127_has_broader_term', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P69_is_associated_with', X, Y],chk1,_,_), fact(['a1:P69_is_associated_with', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P69_is_associated_with', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a2:father', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:father', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X1],chk1,_,_), fact(['a1:P139_has_alternative_form', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P139_has_alternative_form', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P26_moved_to', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P26_moved_to', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E81_Transformation', X],chk1,_,_), fact(['a1:P123_resulted_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P123_resulted_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X1],chk1,_,_), fact(['a1:P92_brought_into_existence', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P92_brought_into_existence', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:MediaType', X],chk1,_,_), fact(['a5:FileFormat', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:FileFormat', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P49_has_former_or_current_keeper', X, Y],chk1,_,_), fact(['a1:P50_has_current_keeper', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P50_has_current_keeper', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:firstName', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:firstName', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P2_has_type', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P2_has_type', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:E25_Man-Made_Feature', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E25_Man-Made_Feature', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X],chk1,_,_), fact(['a1:E73_Information_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E73_Information_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11i_participated_in', X, Y],chk1,_,_), fact(['a1:P96i_gave_birth', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P96i_gave_birth', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E10_Transfer_of_Custody', X],chk1,_,_), fact(['a1:P28_custody_surrendered_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P28_custody_surrendered_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P53i_is_former_or_current_location_of', X, Y],chk1,_,_), fact(['a1:P55i_currently_holds', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P55i_currently_holds', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1_is_identified_by', X, Y],chk1,_,_), fact(['a1:P87_is_identified_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P87_is_identified_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141_assigned', X, Y],chk1,_,_), fact(['a1:P37_assigned', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P37_assigned', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:workInfoHomepage', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:workInfoHomepage', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:E22_Man-Made_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E22_Man-Made_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P109i_is_current_or_former_curator_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P109i_is_current_or_former_curator_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P15i_influenced', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P15i_influenced', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P73i_is_translation_of', X, X2],O1,M1,U1), fact(['a1:P73i_is_translation_of', X, X1],O2,M2,U2), fact(['a1:E33_Linguistic_Object', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P73i_is_translation_of', X, X2],chk1,M1,U1), fact(['a1:P73i_is_translation_of', X, X1],chk1,M2,U2), fact(['a1:E33_Linguistic_Object', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E66_Formation', X1],chk1,_,_), fact(['a1:P95i_was_formed_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P95i_was_formed_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67_refers_to', X, Y],chk1,_,_), fact(['a1:P129_is_about', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P129_is_about', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E63_Beginning_of_Existence', X],chk1,_,_), fact(['a1:E81_Transformation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E81_Transformation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedDocuments', X0, X3],chk1,_,_), fact(['a1:P_E31_Document', X0, X1],O1,M1,U1), fact(['a1:refersToDocument', X1, X2],O2,M2,U2), fact(['a1:refersToDocument', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E31_Document', X0, X1],chk1,M1,U1), fact(['a1:refersToDocument', X1, X2],chk1,M2,U2), fact(['a1:refersToDocument', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:P33_used_specific_technique', X, Y],chk1,_,_), fact(['a1:P33i_was_used_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P33i_was_used_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P33i_was_used_by', X, Y],chk1,_,_), fact(['a1:P33_used_specific_technique', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P33_used_specific_technique', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P111_added', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P111_added', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P129i_is_subject_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P129i_is_subject_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:P9i_forms_part_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P9i_forms_part_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P14_carried_out_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E11_Modification', X1],chk1,_,_), fact(['a1:P126i_was_employed_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P126i_was_employed_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedManMadeThings', X0, X3],chk1,_,_), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,M1,U1), fact(['a1:referredBySame', X1, X2],O2,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E71_Man-Made_Thing', X0, X1],chk1,M1,U1), fact(['a1:referredBySame', X1, X2],chk1,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E46_Section_Definition', X],chk1,_,_), fact(['a1:P58i_defines_section', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P58i_defines_section', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11i_participated_in', X, Y],chk1,_,_), fact(['a1:P14i_performed', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P14i_performed', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:P139_has_alternative_form', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P139_has_alternative_form', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P75i_is_possessed_by', X, Y],chk1,_,_), fact(['a1:P75_possesses', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P75_possesses', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P75_possesses', X, Y],chk1,_,_), fact(['a1:P75i_is_possessed_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P75i_is_possessed_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:position', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:position', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P145i_left_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P145i_left_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X1],chk1,_,_), fact(['a1:P10_falls_within', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P10_falls_within', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E44_Place_Appellation', X],chk1,_,_), fact(['a1:E45_Address', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E45_Address', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:followingEvent', X, Y],chk1,_,_), fact(['a2:immediatelyFollowingEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:immediatelyFollowingEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E33_Linguistic_Object', X1],chk1,_,_), fact(['a1:P73i_is_translation_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P73i_is_translation_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Employment', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Employment', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:LocationPeriodOrJurisdiction', X],chk1,_,_), fact(['a5:Location', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:Location', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P33i_was_used_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P33i_was_used_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X],chk1,_,_), fact(['a3:topic', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:topic', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12i_was_present_at', X, Y],chk1,_,_), fact(['a1:P12_occurred_in_the_presence_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk1,_,_), fact(['a1:P12i_was_present_at', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P12i_was_present_at', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P117_occurs_during', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P117_occurs_during', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E51_Contact_Point', X],chk1,_,_), fact(['a1:P76i_provides_access_to', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P76i_provides_access_to', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E31_Document', X],chk1,_,_), fact(['a1:P70_documents', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P70_documents', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:MediaTypeOrExtent', X],chk1,_,_), fact(['a5:MediaType', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:MediaType', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X1],chk1,_,_), fact(['a3:maker', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:maker', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:primaryTopic', X, Y1],O1,M1,U1), fact(['a3:primaryTopic', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:primaryTopic', X, Y1],chk1,M1,U1), fact(['a3:primaryTopic', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:mbox_sha1sum', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:mbox_sha1sum', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P108_has_produced', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108_has_produced', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E14_Condition_Assessment', X1],chk1,_,_), fact(['a1:P35i_was_identified_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P35i_was_identified_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E51_Contact_Point', X1],chk1,_,_), fact(['a1:P76_has_contact_point', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P76_has_contact_point', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E22_Man-Made_Object', X],chk1,_,_), fact(['a1:E84_Information_Carrier', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E84_Information_Carrier', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P48i_is_preferred_identifier_of', X, Y],chk1,_,_), fact(['a1:P48_has_preferred_identifier', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P48_has_preferred_identifier', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P48_has_preferred_identifier', X, Y],chk1,_,_), fact(['a1:P48i_is_preferred_identifier_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P48i_is_preferred_identifier_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:BasMitzvah', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:BasMitzvah', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P124_transformed', X, Y],chk1,_,_), fact(['a1:P124i_was_transformed_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P124i_was_transformed_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P124i_was_transformed_by', X, Y],chk1,_,_), fact(['a1:P124_transformed', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P124_transformed', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk1,_,_), fact(['a1:P92_brought_into_existence', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P93_took_out_of_existence', X, Y],chk1,_,_), fact(['a1:P13_destroyed', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P13_destroyed', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P8i_witnessed', X, Y],chk1,_,_), fact(['a1:P8_took_place_on_or_within', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P8_took_place_on_or_within', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P8_took_place_on_or_within', X, Y],chk1,_,_), fact(['a1:P8i_witnessed', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P8i_witnessed', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P76_has_contact_point', X, Y],chk1,_,_), fact(['a1:P76i_provides_access_to', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P76i_provides_access_to', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P76i_provides_access_to', X, Y],chk1,_,_), fact(['a1:P76_has_contact_point', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P76_has_contact_point', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E90_Symbolic_Object', X1],chk1,_,_), fact(['a1:P106i_forms_part_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P106i_forms_part_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P46_is_composed_of', X, Y],chk1,_,_), fact(['a1:P56_bears_feature', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P56_bears_feature', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11i_participated_in', X, Y],chk1,_,_), fact(['a1:P145i_left_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P145i_left_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:mbox', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:mbox', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P53_has_former_or_current_location', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P53_has_former_or_current_location', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X],chk1,_,_), fact(['a1:P99i_was_dissolved_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99i_was_dissolved_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk1,_,_), fact(['a1:P25_moved', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P25_moved', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X1],chk1,_,_), fact(['a2:immediatelyFollowingEvent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:immediatelyFollowingEvent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E21_Person', X1],chk1,_,_), fact(['a1:P96_by_mother', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P96_by_mother', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:nick', X, Y],chk1,_,_), fact(['a3:msnChatID', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:msnChatID', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P146_separated_from', X, Y],chk1,_,_), fact(['a1:P146i_lost_member_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P146i_lost_member_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P146i_lost_member_by', X, Y],chk1,_,_), fact(['a1:P146_separated_from', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P146_separated_from', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X1],chk1,_,_), fact(['a1:P40_observed_dimension', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P40_observed_dimension', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:mother', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:mother', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E29_Design_or_Procedure', X1],chk1,_,_), fact(['a1:P33_used_specific_technique', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P33_used_specific_technique', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P140i_was_attributed_by', X, Y],chk1,_,_), fact(['a1:P41i_was_classified_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P41i_was_classified_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:schoolHomepage', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:schoolHomepage', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P52_has_current_owner', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P52_has_current_owner', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P7i_witnessed', X, Y],chk1,_,_), fact(['a1:P7_took_place_at', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P7_took_place_at', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P7_took_place_at', X, Y],chk1,_,_), fact(['a1:P7i_witnessed', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P7i_witnessed', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X1],chk1,_,_), fact(['a1:P95_has_formed', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P95_has_formed', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:Person', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:Person', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P127i_has_narrower_term', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P127i_has_narrower_term', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E64_End_of_Existence', X],chk1,_,_), fact(['a1:E6_Destruction', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E6_Destruction', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P53i_is_former_or_current_location_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P53i_is_former_or_current_location_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P134_continued', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P134_continued', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:OnlineAccount', X1],chk1,_,_), fact(['a3:account', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:account', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P127_has_broader_term', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P127_has_broader_term', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X1],chk1,_,_), fact(['a1:P93_took_out_of_existence', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P93_took_out_of_existence', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P137i_is_exemplified_by', X, Y],chk1,_,_), fact(['a1:P137_exemplifies', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P137_exemplifies', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P137_exemplifies', X, Y],chk1,_,_), fact(['a1:P137i_is_exemplified_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P137i_is_exemplified_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E8_Acquisition', X],chk1,_,_), fact(['a1:P22_transferred_title_to', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P22_transferred_title_to', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:OnlineAccount', X],chk1,_,_), fact(['a3:accountName', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:accountName', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:mother', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:mother', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E10_Transfer_of_Custody', X1],chk1,_,_), fact(['a1:P30i_custody_transferred_through', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P30i_custody_transferred_through', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P86_falls_within', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P86_falls_within', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk1,_,_), fact(['a1:P13i_was_destroyed_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P13i_was_destroyed_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P20i_was_purpose_of', X, Y],chk1,_,_), fact(['a1:P20_had_specific_purpose', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P20_had_specific_purpose', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P20_had_specific_purpose', X, Y],chk1,_,_), fact(['a1:P20i_was_purpose_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P20i_was_purpose_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P89i_contains', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P89i_contains', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E3_Condition_State', X],chk1,_,_), fact(['a1:P5i_forms_part_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P5i_forms_part_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P49i_is_former_or_current_keeper_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E73_Information_Object', X],chk1,_,_), fact(['a1:P128i_is_carried_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P128i_is_carried_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Imprisonment', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Imprisonment', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:tipjar', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:tipjar', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12i_was_present_at', X, Y],chk1,_,_), fact(['a1:P92i_was_brought_into_existence_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk1,_,_), fact(['a1:P98i_was_born', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P98i_was_born', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:organization', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:organization', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:concurrentEvent', X, Y],chk1,_,_), fact(['a2:concurrentEvent', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:concurrentEvent', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:yahooChatID', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:yahooChatID', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P42_assigned', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P42_assigned', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X],chk1,_,_), fact(['a1:P91_has_unit', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P91_has_unit', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Retirement', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Retirement', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:page', X, Y],chk1,_,_), fact(['a3:tipjar', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:tipjar', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P62_depicts', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P62_depicts', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Interval', X1],chk1,_,_), fact(['a2:interval', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:interval', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a2:olb', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:olb', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P117i_includes', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P117i_includes', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P88i_forms_part_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P88i_forms_part_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a2:mother', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:mother', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P130i_features_are_also_found_on', X, Y],chk1,_,_), fact(['a1:P73i_is_translation_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P73i_is_translation_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:father', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:father', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E83_Type_Creation', X],chk1,_,_), fact(['a1:P135_created_type', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P135_created_type', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P59i_is_located_on_or_within', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P59i_is_located_on_or_within', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Dismissal', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Dismissal', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E67_Birth', X1],chk1,_,_), fact(['a1:P96i_gave_birth', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P96i_gave_birth', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E26_Physical_Feature', X],chk1,_,_), fact(['a1:E27_Site', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E27_Site', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a2:principal', X, X2],O1,M1,U1), fact(['a2:principal', X, X1],O2,M2,U2), fact(['a2:IndividualEvent', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a2:principal', X, X2],chk1,M1,U1), fact(['a2:principal', X, X1],chk1,M2,U2), fact(['a2:IndividualEvent', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['rdfs:Literal', X1],chk1,_,_), fact(['a3:msnChatID', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:msnChatID', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:homepage', Y1, X],O1,M1,U1), fact(['a3:homepage', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:homepage', Y1, X],chk1,M1,U1), fact(['a3:homepage', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P1i_identifies', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P1i_identifies', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P10_falls_within', X, Z],chk1,_,_), fact(['a1:P10_falls_within', X, Y],O1,M1,U1), fact(['a1:P10_falls_within', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P10_falls_within', X, Y],chk1,M1,U1), fact(['a1:P10_falls_within', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E67_Birth', X],chk1,_,_), fact(['a1:P96_by_mother', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P96_by_mother', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Enrolment', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Enrolment', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P75_possesses', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P75_possesses', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E64_End_of_Existence', X1],chk1,_,_), fact(['a1:P93i_was_taken_out_of_existence_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E21_Person', X1],chk1,_,_), fact(['a1:P100_was_death_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P100_was_death_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E57_Material', X],chk1,_,_), fact(['a1:P126i_was_employed_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P126i_was_employed_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X1],chk1,_,_), fact(['a1:P9i_forms_part_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P9i_forms_part_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a10:SpatialThing', X],chk1,_,_), fact(['a3:Person', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:Person', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12_occurred_in_the_presence_of', X, Y],chk1,_,_), fact(['a1:P16_used_specific_object', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X],chk1,_,_), fact(['a1:P92i_was_brought_into_existence_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P54i_is_current_permanent_location_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P54i_is_current_permanent_location_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P51i_is_former_or_current_owner_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P51i_is_former_or_current_owner_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P115i_is_finished_by', X, Z],chk1,_,_), fact(['a1:P115i_is_finished_by', X, Y],O1,M1,U1), fact(['a1:P115i_is_finished_by', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P115i_is_finished_by', X, Y],chk1,M1,U1), fact(['a1:P115i_is_finished_by', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P2i_is_type_of', X, Y],chk1,_,_), fact(['a1:P137i_is_exemplified_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P137i_is_exemplified_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X1],chk1,_,_), fact(['a2:concludingEvent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:concludingEvent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Image', X],chk1,_,_), fact(['a3:thumbnail', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:thumbnail', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P27i_was_origin_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P27i_was_origin_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:parent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:parent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E3_Condition_State', X],chk1,_,_), fact(['a1:P44i_is_condition_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P44i_is_condition_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11i_participated_in', X, Y],chk1,_,_), fact(['a1:P144i_gained_member_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P144i_gained_member_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P118i_is_overlapped_in_time_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P118i_is_overlapped_in_time_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X1],chk1,_,_), fact(['a1:P129i_is_subject_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P129i_is_subject_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X1],chk1,_,_), fact(['a1:P99_dissolved', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99_dissolved', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E5_Event', X1],chk1,_,_), fact(['a1:P20_had_specific_purpose', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P20_had_specific_purpose', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E67_Birth', X1],chk1,_,_), fact(['a1:P98i_was_born', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P98i_was_born', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P125i_was_type_of_object_used_in', X, Y],chk1,_,_), fact(['a1:P32i_was_technique_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P32i_was_technique_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P15_was_influenced_by', X, Y],chk1,_,_), fact(['a1:P16_used_specific_object', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:P65_shows_visual_item', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P65_shows_visual_item', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67i_is_referred_to_by', X, Y],chk1,_,_), fact(['a1:P129i_is_subject_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P129i_is_subject_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P134i_was_continued_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P134i_was_continued_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:msnChatID', Y1, X],O1,M1,U1), fact(['a3:msnChatID', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:msnChatID', Y1, X],chk1,M1,U1), fact(['a3:msnChatID', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P87_is_identified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P87_is_identified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['a3:Person', X],O1,M1,U1), fact(['a3:Project', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:Person', X],chk1,M1,U1), fact(['a3:Project', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E73_Information_Object', X],chk1,_,_), fact(['a1:E33_Linguistic_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:geekcode', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:geekcode', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:officiator', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:officiator', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P114_is_equal_in_time_to', X, Y],chk1,_,_), fact(['a1:P114_is_equal_in_time_to', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P114_is_equal_in_time_to', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:partner', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:partner', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:spectator', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:spectator', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14i_performed', X, Y],chk1,_,_), fact(['a1:P28i_surrendered_custody_through', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P28i_surrendered_custody_through', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P15i_influenced', X, Y],chk1,_,_), fact(['a1:P136i_supported_type_creation', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P136i_supported_type_creation', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E56_Language', X],chk1,_,_), fact(['a1:P72i_is_language_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P72i_is_language_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11_had_participant', X, Y],chk1,_,_), fact(['a1:P96_by_mother', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P96_by_mother', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P116_starts', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P116_starts', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:img', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:img', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E21_Person', X],chk1,_,_), fact(['a1:P100i_died_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P100i_died_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E21_Person', X],chk1,_,_), fact(['a1:P96i_gave_birth', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P96i_gave_birth', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk1,_,_), fact(['a1:P108i_was_produced_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108i_was_produced_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:familyName', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:familyName', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P148_has_component', X, Z],chk1,_,_), fact(['a1:P148_has_component', X, Y],O1,M1,U1), fact(['a1:P148_has_component', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P148_has_component', X, Y],chk1,M1,U1), fact(['a1:P148_has_component', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X1],chk1,_,_), fact(['a1:P55i_currently_holds', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P55i_currently_holds', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a11:Event', X],chk1,_,_), fact(['a2:Event', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Event', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P97_from_father', X, Y],chk1,_,_), fact(['a1:P97i_was_father_for', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P97i_was_father_for', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P97i_was_father_for', X, Y],chk1,_,_), fact(['a1:P97_from_father', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P97_from_father', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E9_Move', X],chk1,_,_), fact(['a1:P26_moved_to', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P26_moved_to', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['a1:E52_Time-Span', X],O1,M1,U1), fact(['a1:E53_Place', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:E52_Time-Span', X],chk1,M1,U1), fact(['a1:E53_Place', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P89_falls_within', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P89_falls_within', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:E56_Language', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E56_Language', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:spectator', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:spectator', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P40_observed_dimension', X, Y],chk1,_,_), fact(['a1:P40i_was_observed_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P40i_was_observed_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P40i_was_observed_in', X, Y],chk1,_,_), fact(['a1:P40_observed_dimension', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P40_observed_dimension', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedManMadeThings', X0, X3],chk1,_,_), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,M1,U1), fact(['a1:P67_refers_to', X1, X2],O2,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E71_Man-Made_Thing', X0, X1],chk1,M1,U1), fact(['a1:P67_refers_to', X1, X2],chk1,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Adoption', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Adoption', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141i_was_assigned_by', X, Y],chk1,_,_), fact(['a1:P42i_was_assigned_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P42i_was_assigned_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92_brought_into_existence', X, Y],chk1,_,_), fact(['a1:P95_has_formed', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P95_has_formed', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12i_was_present_at', X, Y],chk1,_,_), fact(['a1:P31i_was_modified_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P46i_forms_part_of', X, Y],chk1,_,_), fact(['a1:P56i_is_found_on', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P56i_is_found_on', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P117_occurs_during', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P117_occurs_during', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P93_took_out_of_existence', X, Y],chk1,_,_), fact(['a1:P99_dissolved', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99_dissolved', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P41_classified', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P41_classified', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:msnChatID', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:msnChatID', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P89i_contains', X, Z],chk1,_,_), fact(['a1:P89i_contains', X, Y],O1,M1,U1), fact(['a1:P89i_contains', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P89i_contains', X, Y],chk1,M1,U1), fact(['a1:P89i_contains', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:relatedDocuments', X0, X3],chk1,_,_), fact(['a1:P_E31_Document', X0, X1],O1,M1,U1), fact(['a1:P67_refers_to', X1, X2],O2,M2,U2), fact(['a1:P_E31_Document', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E31_Document', X0, X1],chk1,M1,U1), fact(['a1:P67_refers_to', X1, X2],chk1,M2,U2), fact(['a1:P_E31_Document', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P137i_is_exemplified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P137i_is_exemplified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P130i_features_are_also_found_on', X, Y],chk1,_,_), fact(['a1:P130_shows_features_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P130_shows_features_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P130_shows_features_of', X, Y],chk1,_,_), fact(['a1:P130i_features_are_also_found_on', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P130i_features_are_also_found_on', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P51i_is_former_or_current_owner_of', X, Y],chk1,_,_), fact(['a1:P52i_is_current_owner_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P52i_is_current_owner_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P46i_forms_part_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P46i_forms_part_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P19i_was_made_for', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P19i_was_made_for', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E13_Attribute_Assignment', X],chk1,_,_), fact(['a1:E17_Type_Assignment', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E17_Type_Assignment', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E31_Document', X],chk1,_,_), fact(['a1:E32_Authority_Document', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E32_Authority_Document', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P135_created_type', X, Y],chk1,_,_), fact(['a1:P135i_was_created_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P135i_was_created_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P135i_was_created_by', X, Y],chk1,_,_), fact(['a1:P135_created_type', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P135_created_type', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P120i_occurs_after', X, Y],chk1,_,_), fact(['a1:P120_occurs_before', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P120_occurs_before', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P120_occurs_before', X, Y],chk1,_,_), fact(['a1:P120i_occurs_after', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P120i_occurs_after', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P107i_is_current_or_former_member_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P107i_is_current_or_former_member_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:gender', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:gender', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E71_Man-Made_Thing', X],chk1,_,_), fact(['a1:P19i_was_made_for', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P19i_was_made_for', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P86_falls_within', X, Z],chk1,_,_), fact(['a1:P86_falls_within', X, Y],O1,M1,U1), fact(['a1:P86_falls_within', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P86_falls_within', X, Y],chk1,M1,U1), fact(['a1:P86_falls_within', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P120_occurs_before', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P120_occurs_before', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:E19_Physical_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E19_Physical_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P7i_witnessed', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P7i_witnessed', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P75i_is_possessed_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P75i_is_possessed_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdf:Property', X],chk1,_,_), fact(['rdfs:ContainerMembershipProperty', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['rdfs:ContainerMembershipProperty', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P16_used_specific_object', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E9_Move', X1],chk1,_,_), fact(['a1:P27i_was_origin_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P27i_was_origin_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E63_Beginning_of_Existence', X1],chk1,_,_), fact(['a1:P92i_was_brought_into_existence_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E80_Part_Removal', X1],chk1,_,_), fact(['a1:P113i_was_removed_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P113i_was_removed_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P103_was_intended_for', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P103_was_intended_for', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:child', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:child', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:page', X, Y],chk1,_,_), fact(['a3:homepage', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:homepage', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:partner', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:partner', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P140i_was_attributed_by', X, Y],chk1,_,_), fact(['a1:P39i_was_measured_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P39i_was_measured_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P_E53_Place', X, X],chk1,_,_), fact(['a1:E48_Place_Name', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E48_Place_Name', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:schoolHomepage', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:schoolHomepage', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E14_Condition_Assessment', X],chk1,_,_), fact(['a1:P34_concerned', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P34_concerned', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Redundancy', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Redundancy', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P28i_surrendered_custody_through', X, Y],chk1,_,_), fact(['a1:P28_custody_surrendered_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P28_custody_surrendered_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P28_custody_surrendered_by', X, Y],chk1,_,_), fact(['a1:P28i_surrendered_custody_through', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P28i_surrendered_custody_through', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P27_moved_from', X, Z],chk1,_,_), fact(['a1:P27_moved_from', X, Y],O1,M1,U1), fact(['a1:P27_moved_from', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P27_moved_from', X, Y],chk1,M1,U1), fact(['a1:P27_moved_from', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E11_Modification', X],chk1,_,_), fact(['a1:E80_Part_Removal', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E80_Part_Removal', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E35_Title', X],chk1,_,_), fact(['a1:P102i_is_title_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P102i_is_title_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P116i_is_started_by', X, Z],chk1,_,_), fact(['a1:P116i_is_started_by', X, Y],O1,M1,U1), fact(['a1:P116i_is_started_by', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P116i_is_started_by', X, Y],chk1,M1,U1), fact(['a1:P116i_is_started_by', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:E44_Place_Appellation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P54_has_current_permanent_location', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P54_has_current_permanent_location', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P38_deassigned', X, Y],chk1,_,_), fact(['a1:P38i_was_deassigned_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P38i_was_deassigned_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P38i_was_deassigned_by', X, Y],chk1,_,_), fact(['a1:P38_deassigned', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P38_deassigned', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E67_Birth', X1],chk1,_,_), fact(['a1:P97i_was_father_for', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P97i_was_father_for', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P4_has_time-span', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P4_has_time-span', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Formation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Formation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:agent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:agent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P137_exemplifies', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P137_exemplifies', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P137i_is_exemplified_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P137i_is_exemplified_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P80_end_is_qualified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P80_end_is_qualified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:knows', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:knows', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Disbanding', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Disbanding', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P148i_is_component_of', X, Z],chk1,_,_), fact(['a1:P148i_is_component_of', X, Y],O1,M1,U1), fact(['a1:P148i_is_component_of', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P148i_is_component_of', X, Y],chk1,M1,U1), fact(['a1:P148i_is_component_of', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a3:nick', X, Y],chk1,_,_), fact(['a3:yahooChatID', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:yahooChatID', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:event', X, Y],chk1,_,_), fact(['a2:death', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:death', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P89_falls_within', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P89_falls_within', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P115_finishes', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P115_finishes', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Death', X1],chk1,_,_), fact(['a2:death', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:death', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141i_was_assigned_by', X, Y],chk1,_,_), fact(['a1:P35i_was_identified_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P35i_was_identified_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E79_Part_Addition', X],chk1,_,_), fact(['a1:P111_added', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P111_added', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E42_Identifier', X],chk1,_,_), fact(['a1:P37i_was_assigned_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P37i_was_assigned_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E17_Type_Assignment', X],chk1,_,_), fact(['a1:P42_assigned', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P42_assigned', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E90_Symbolic_Object', X],chk1,_,_), fact(['a1:E73_Information_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E73_Information_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P31_has_modified', X, Y],chk1,_,_), fact(['a1:P110_augmented', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P110_augmented', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1i_identifies', X, Y],chk1,_,_), fact(['a1:P78i_identifies', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P78i_identifies', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X1],chk1,_,_), fact(['a1:P91i_is_unit_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P91i_is_unit_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E86_Leaving', X],chk1,_,_), fact(['a1:P146_separated_from', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P146_separated_from', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:position', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:position', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X1],chk1,_,_), fact(['a1:P86i_contains', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P86i_contains', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:mbox_sha1sum', Y1, X],O1,M1,U1), fact(['a3:mbox_sha1sum', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:mbox_sha1sum', Y1, X],chk1,M1,U1), fact(['a3:mbox_sha1sum', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:E74_Group', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E74_Group', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141i_was_assigned_by', X, Y],chk1,_,_), fact(['a1:P37i_was_assigned_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P37i_was_assigned_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Literal', X1],chk1,_,_), fact(['a3:yahooChatID', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:yahooChatID', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P127i_has_narrower_term', X, Z],chk1,_,_), fact(['a1:P127i_has_narrower_term', X, Y],O1,M1,U1), fact(['a1:P127i_has_narrower_term', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P127i_has_narrower_term', X, Y],chk1,M1,U1), fact(['a1:P127i_has_narrower_term', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a3:Agent', X1],chk1,_,_), fact(['a3:member', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:member', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P21i_was_purpose_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P21i_was_purpose_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E73_Information_Object', X],chk1,_,_), fact(['a1:E29_Design_or_Procedure', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Death', X],chk1,_,_), fact(['a2:Execution', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Execution', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P71i_is_listed_in', X, Y],chk1,_,_), fact(['a1:P71_lists', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P71_lists', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P71_lists', X, Y],chk1,_,_), fact(['a1:P71i_is_listed_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P71i_is_listed_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P84_had_at_most_duration', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P84_had_at_most_duration', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P101i_was_use_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P101i_was_use_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P142i_was_used_in', X, Y],chk1,_,_), fact(['a1:P142_used_constituent', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P142_used_constituent', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P142_used_constituent', X, Y],chk1,_,_), fact(['a1:P142i_was_used_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P142i_was_used_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:position', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:position', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E87_Curation_Activity', X1],chk1,_,_), fact(['a1:P147i_was_curated_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P147i_was_curated_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],chk1,_,_), fact(['a1:P49_has_former_or_current_keeper', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P49_has_former_or_current_keeper', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P49_has_former_or_current_keeper', X, Y],chk1,_,_), fact(['a1:P49i_is_former_or_current_keeper_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P49i_is_former_or_current_keeper_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141i_was_assigned_by', X, Y],chk1,_,_), fact(['a1:P38i_was_deassigned_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P38i_was_deassigned_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E86_Leaving', X1],chk1,_,_), fact(['a1:P145i_left_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P145i_left_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P91_has_unit', X, X2],O1,M1,U1), fact(['a1:P91_has_unit', X, X1],O2,M2,U2), fact(['a1:E54_Dimension', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P91_has_unit', X, X2],chk1,M1,U1), fact(['a1:P91_has_unit', X, X1],chk1,M2,U2), fact(['a1:E54_Dimension', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a2:Relationship', X1],chk1,_,_), fact(['a2:relationship', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:relationship', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E33_Linguistic_Object', X],chk1,_,_), fact(['a1:P73i_is_translation_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P73i_is_translation_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E30_Right', X],chk1,_,_), fact(['a1:P75i_is_possessed_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P75i_is_possessed_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:principal', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:principal', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:OnlineAccount', X],chk1,_,_), fact(['a3:OnlineEcommerceAccount', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:OnlineEcommerceAccount', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P2i_is_type_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P2i_is_type_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P_E31_Document', X, X],chk1,_,_), fact(['a1:E31_Document', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E31_Document', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:principal', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:principal', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X],chk1,_,_), fact(['a1:P144i_gained_member_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P144i_gained_member_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P74i_is_current_or_former_residence_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P74i_is_current_or_former_residence_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:OnlineAccount', X1],chk1,_,_), fact(['a3:holdsAccount', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:holdsAccount', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X],chk1,_,_), fact(['a1:P90_has_value', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P90_has_value', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:weblog', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:weblog', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E17_Type_Assignment', X1],chk1,_,_), fact(['a1:P41i_was_classified_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P41i_was_classified_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92_brought_into_existence', X, Y],chk1,_,_), fact(['a1:P123_resulted_in', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P123_resulted_in', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E64_End_of_Existence', X],chk1,_,_), fact(['a1:P93_took_out_of_existence', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:concurrentEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:concurrentEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P49i_is_former_or_current_keeper_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P49i_is_former_or_current_keeper_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Class', X],chk1,_,_), fact(['rdfs:Datatype', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['rdfs:Datatype', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P111i_was_added_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P111i_was_added_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a2:father', X, Anon0],O1,M1,U1), fact(['a2:mother', X, Anon0],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a2:father', X, Anon0],chk1,M1,U1), fact(['a2:mother', X, Anon0],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P125i_was_type_of_object_used_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P125i_was_type_of_object_used_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11_had_participant', X, Y],chk1,_,_), fact(['a1:P145_separated', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P145_separated', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X],chk1,_,_), fact(['a1:P57_has_number_of_parts', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P57_has_number_of_parts', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P39_measured', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P39_measured', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Investiture', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Investiture', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E87_Curation_Activity', X],chk1,_,_), fact(['a1:P147_curated', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P147_curated', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E36_Visual_Item', X1],chk1,_,_), fact(['a1:P138i_has_representation', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P138i_has_representation', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67_refers_to', X, Y],chk1,_,_), fact(['a1:P67i_is_referred_to_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67i_is_referred_to_by', X, Y],chk1,_,_), fact(['a1:P67_refers_to', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P67_refers_to', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P50i_is_current_keeper_of', X, Y],chk1,_,_), fact(['a1:P50_has_current_keeper', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P50_has_current_keeper', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P50_has_current_keeper', X, Y],chk1,_,_), fact(['a1:P50i_is_current_keeper_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P50i_is_current_keeper_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E36_Visual_Item', X],chk1,_,_), fact(['a1:P138_represents', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P138_represents', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P130_shows_features_of', X, Y],chk1,_,_), fact(['a1:P73_has_translation', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P73_has_translation', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:concurrentEvent', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:concurrentEvent', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:LocationPeriodOrJurisdiction', X],chk1,_,_), fact(['a5:PeriodOfTime', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:PeriodOfTime', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P143i_was_joined_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P143i_was_joined_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P121_overlaps_with', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P121_overlaps_with', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P34_concerned', X, Y],chk1,_,_), fact(['a1:P34i_was_assessed_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P34i_was_assessed_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P34i_was_assessed_by', X, Y],chk1,_,_), fact(['a1:P34_concerned', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P34_concerned', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E12_Production', X1],chk1,_,_), fact(['a1:P108i_was_produced_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108i_was_produced_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P140i_was_attributed_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P117i_includes', X, Z],chk1,_,_), fact(['a1:P117i_includes', X, Y],O1,M1,U1), fact(['a1:P117i_includes', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P117i_includes', X, Y],chk1,M1,U1), fact(['a1:P117i_includes', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P1i_identifies', X, Y],chk1,_,_), fact(['a1:P102i_is_title_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P102i_is_title_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:referToSame', X0, X2],chk1,_,_), fact(['a1:P67_refers_to', X0, X1],O1,M1,U1), fact(['a1:P67_refers_to', X2, X1],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P67_refers_to', X0, X1],chk1,M1,U1), fact(['a1:P67_refers_to', X2, X1],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E70_Thing', X],chk1,_,_), fact(['a1:E71_Man-Made_Thing', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P141_assigned', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P141_assigned', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P74_has_current_or_former_residence', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P74_has_current_or_former_residence', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P84_had_at_most_duration', X, Y],chk1,_,_), fact(['a1:P84i_was_maximum_duration_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P84i_was_maximum_duration_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P84i_was_maximum_duration_of', X, Y],chk1,_,_), fact(['a1:P84_had_at_most_duration', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P84_had_at_most_duration', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:page', X, Y],chk1,_,_), fact(['a3:weblog', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:weblog', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:E77_Persistent_Item', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P104_is_subject_to', X, Y],chk1,_,_), fact(['a1:P104i_applies_to', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P104i_applies_to', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P104i_applies_to', X, Y],chk1,_,_), fact(['a1:P104_is_subject_to', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P104_is_subject_to', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E87_Curation_Activity', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E87_Curation_Activity', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:isPrimaryTopicOf', Y1, X],O1,M1,U1), fact(['a3:isPrimaryTopicOf', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:isPrimaryTopicOf', Y1, X],chk1,M1,U1), fact(['a3:isPrimaryTopicOf', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a6:Relationship', X],chk1,_,_), fact(['a2:Relationship', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Relationship', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Relationship', X],chk1,_,_), fact(['a6:Relationship', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a6:Relationship', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:logo', Y1, X],O1,M1,U1), fact(['a3:logo', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:logo', Y1, X],chk1,M1,U1), fact(['a3:logo', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E63_Beginning_of_Existence', X],chk1,_,_), fact(['a1:P92_brought_into_existence', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E44_Place_Appellation', X],chk1,_,_), fact(['a1:E48_Place_Name', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E48_Place_Name', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11i_participated_in', X, Y],chk1,_,_), fact(['a1:P143i_was_joined_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P143i_was_joined_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['a1:E2_Temporal_Entity', X],O1,M1,U1), fact(['a1:E77_Persistent_Item', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:E2_Temporal_Entity', X],chk1,M1,U1), fact(['a1:E77_Persistent_Item', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X1],chk1,_,_), fact(['a1:P54i_is_current_permanent_location_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P54i_is_current_permanent_location_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P145_separated', X, X2],O1,M1,U1), fact(['a1:P145_separated', X, X1],O2,M2,U2), fact(['a1:E86_Leaving', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P145_separated', X, X2],chk1,M1,U1), fact(['a1:P145_separated', X, X1],chk1,M2,U2), fact(['a1:E86_Leaving', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk1,_,_), fact(['a1:P99i_was_dissolved_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P99i_was_dissolved_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Inauguration', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Inauguration', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P125_used_object_of_type', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P125_used_object_of_type', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E9_Move', X1],chk1,_,_), fact(['a1:P25i_moved_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P25i_moved_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P72_has_language', X, Y],chk1,_,_), fact(['a1:P72i_is_language_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P72i_is_language_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P72i_is_language_of', X, Y],chk1,_,_), fact(['a1:P72_has_language', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P72_has_language', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X1],chk1,_,_), fact(['a1:P101i_was_use_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P101i_was_use_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X],chk1,_,_), fact(['a1:P123i_resulted_from', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P123i_resulted_from', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E63_Beginning_of_Existence', X],chk1,_,_), fact(['a1:E66_Formation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E66_Formation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:P1i_identifies', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P1i_identifies', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:MediaTypeOrExtent', X],chk1,_,_), fact(['a5:SizeOrDuration', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:SizeOrDuration', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk1,_,_), fact(['a1:P92_brought_into_existence', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P92_brought_into_existence', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92_brought_into_existence', X, Y],chk1,_,_), fact(['a1:P92i_was_brought_into_existence_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:icqChatID', Y1, X],O1,M1,U1), fact(['a3:icqChatID', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:icqChatID', Y1, X],chk1,M1,U1), fact(['a3:icqChatID', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a3:OnlineAccount', X],chk1,_,_), fact(['a3:OnlineChatAccount', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:OnlineChatAccount', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E21_Person', X1],chk1,_,_), fact(['a1:P97_from_father', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P97_from_father', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P65i_is_shown_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P65i_is_shown_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P86i_contains', X, Z],chk1,_,_), fact(['a1:P86i_contains', X, Y],O1,M1,U1), fact(['a1:P86i_contains', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P86i_contains', X, Y],chk1,M1,U1), fact(['a1:P86i_contains', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Coronation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Coronation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X],chk1,_,_), fact(['a1:P148i_is_component_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P148i_is_component_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E14_Condition_Assessment', X1],chk1,_,_), fact(['a1:P34i_was_assessed_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P34i_was_assessed_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P49_has_former_or_current_keeper', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P49_has_former_or_current_keeper', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X1],chk1,_,_), fact(['a1:P43i_is_dimension_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P43i_is_dimension_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E85_Joining', X1],chk1,_,_), fact(['a1:P143i_was_joined_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P143i_was_joined_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P21i_was_purpose_of', X, Y],chk1,_,_), fact(['a1:P21_had_general_purpose', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P21_had_general_purpose', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P21_had_general_purpose', X, Y],chk1,_,_), fact(['a1:P21i_was_purpose_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P21i_was_purpose_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P87i_identifies', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P87i_identifies', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Funeral', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Funeral', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11_had_participant', X, Y],chk1,_,_), fact(['a1:P11i_participated_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P11i_participated_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P11i_participated_in', X, Y],chk1,_,_), fact(['a1:P11_had_participant', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P11_had_participant', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P111i_was_added_by', X, Y],chk1,_,_), fact(['a1:P111_added', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P111_added', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P111_added', X, Y],chk1,_,_), fact(['a1:P111i_was_added_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P111i_was_added_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P67_refers_to', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P67_refers_to', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P_E73_Information_Object', X, X],chk1,_,_), fact(['a1:E73_Information_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E73_Information_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E80_Part_Removal', X],chk1,_,_), fact(['a1:P113_removed', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P113_removed', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P16i_was_used_for', X, Y],chk1,_,_), fact(['a1:P142i_was_used_in', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P142i_was_used_in', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:topic', X, Y],chk1,_,_), fact(['a3:page', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:page', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:page', X, Y],chk1,_,_), fact(['a3:topic', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:topic', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P94i_was_created_by', X, Y],chk1,_,_), fact(['a1:P135i_was_created_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P135i_was_created_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P101_had_as_general_use', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P101_had_as_general_use', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:isPrimaryTopicOf', X, Y],chk1,_,_), fact(['a3:homepage', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:homepage', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P127i_has_narrower_term', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P127i_has_narrower_term', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P25_moved', X, Y],chk1,_,_), fact(['a1:P25i_moved_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P25i_moved_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P25i_moved_by', X, Y],chk1,_,_), fact(['a1:P25_moved', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P25_moved', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P3_has_note', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P3_has_note', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141_assigned', X, Y],chk1,_,_), fact(['a1:P38_deassigned', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P38_deassigned', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:E42_Identifier', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E42_Identifier', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X],chk1,_,_), fact(['a1:P148_has_component', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P148_has_component', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P122_borders_with', X, Y],chk1,_,_), fact(['a1:P122_borders_with', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P122_borders_with', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P59i_is_located_on_or_within', X, X2],O1,M1,U1), fact(['a1:P59i_is_located_on_or_within', X, X1],O2,M2,U2), fact(['a1:E53_Place', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P59i_is_located_on_or_within', X, X2],chk1,M1,U1), fact(['a1:P59i_is_located_on_or_within', X, X1],chk1,M2,U2), fact(['a1:E53_Place', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E9_Move', X1],chk1,_,_), fact(['a1:P26i_was_destination_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P26i_was_destination_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:accountServiceHomepage', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:accountServiceHomepage', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P68i_use_foreseen_by', X, Y],chk1,_,_), fact(['a1:P68_foresees_use_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P68_foresees_use_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P68_foresees_use_of', X, Y],chk1,_,_), fact(['a1:P68i_use_foreseen_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P68i_use_foreseen_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:eventInterval', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:eventInterval', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E73_Information_Object', X1],chk1,_,_), fact(['a1:P128_carries', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P128_carries', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E65_Creation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E65_Creation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Literal', X1],chk1,_,_), fact(['a3:mbox_sha1sum', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:mbox_sha1sum', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Relationship', X],chk1,_,_), fact(['a2:interval', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:interval', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P67_refers_to', X, Z],chk1,_,_), fact(['a1:P67_refers_to', X, Y],O1,M1,U1), fact(['a1:P67_refers_to', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P67_refers_to', X, Y],chk1,M1,U1), fact(['a1:P67_refers_to', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E11_Modification', X],chk1,_,_), fact(['a1:E12_Production', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E12_Production', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X],chk1,_,_), fact(['a1:P12i_was_present_at', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P48_has_preferred_identifier', X, X2],O1,M1,U1), fact(['a1:P48_has_preferred_identifier', X, X1],O2,M2,U2), fact(['a1:E1_CRM_Entity', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P48_has_preferred_identifier', X, X2],chk1,M1,U1), fact(['a1:P48_has_preferred_identifier', X, X1],chk1,M2,U2), fact(['a1:E1_CRM_Entity', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X1],chk1,_,_), fact(['a1:P148_has_component', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P148_has_component', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X1],chk1,_,_), fact(['a1:P12_occurred_in_the_presence_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:P31i_was_modified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E28_Conceptual_Object', X],chk1,_,_), fact(['a1:P94i_was_created_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P94i_was_created_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X],chk1,_,_), fact(['a1:P107_has_current_or_former_member', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P107_has_current_or_former_member', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:P103i_was_intention_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P103i_was_intention_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E5_Event', X1],chk1,_,_), fact(['a1:P12i_was_present_at', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P12i_was_present_at', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141_assigned', X, Y],chk1,_,_), fact(['a1:P42_assigned', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P42_assigned', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E17_Type_Assignment', X],chk1,_,_), fact(['a1:P41_classified', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P41_classified', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P62i_is_depicted_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P62i_is_depicted_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P4i_is_time-span_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P4i_is_time-span_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E90_Symbolic_Object', X],chk1,_,_), fact(['a1:P106i_forms_part_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P106i_forms_part_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:E26_Physical_Feature', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E26_Physical_Feature', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:precedingEvent', X, Y],chk1,_,_), fact(['a2:immediatelyPrecedingEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:immediatelyPrecedingEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Resignation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Resignation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:BarMitzvah', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:BarMitzvah', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:E2_Temporal_Entity', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk1,_,_), fact(['a1:P123i_resulted_from', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P123i_resulted_from', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:E54_Dimension', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E54_Dimension', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P131i_identifies', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P131i_identifies', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Baptism', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Baptism', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P122_borders_with', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P122_borders_with', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92_brought_into_existence', X, Y],chk1,_,_), fact(['a1:P94_has_created', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P94_has_created', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P115_finishes', X, Z],chk1,_,_), fact(['a1:P115_finishes', X, Y],O1,M1,U1), fact(['a1:P115_finishes', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P115_finishes', X, Y],chk1,M1,U1), fact(['a1:P115_finishes', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:openid', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:openid', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1_is_identified_by', X, Y],chk1,_,_), fact(['a1:P1i_identifies', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P1i_identifies', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1i_identifies', X, Y],chk1,_,_), fact(['a1:P1_is_identified_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P1_is_identified_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P51_has_former_or_current_owner', X, Y],chk1,_,_), fact(['a1:P52_has_current_owner', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P52_has_current_owner', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P102_has_title', X, Y],chk1,_,_), fact(['a1:P102i_is_title_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P102i_is_title_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P102i_is_title_of', X, Y],chk1,_,_), fact(['a1:P102_has_title', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P102_has_title', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P59_has_section', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P59_has_section', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P79_beginning_is_qualified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P79_beginning_is_qualified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:jabberID', Y1, X],O1,M1,U1), fact(['a3:jabberID', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:jabberID', Y1, X],chk1,M1,U1), fact(['a3:jabberID', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P140i_was_attributed_by', X, Y],chk1,_,_), fact(['a1:P140_assigned_attribute_to', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P140_assigned_attribute_to', X, Y],chk1,_,_), fact(['a1:P140i_was_attributed_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P140i_was_attributed_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E21_Person', X1],chk1,_,_), fact(['a1:P98_brought_into_life', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P98_brought_into_life', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:P8_took_place_on_or_within', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P8_took_place_on_or_within', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X1],chk1,_,_), fact(['a1:P8_took_place_on_or_within', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P8_took_place_on_or_within', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X],chk1,_,_), fact(['a1:E22_Man-Made_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E22_Man-Made_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P114_is_equal_in_time_to', X, Z],chk1,_,_), fact(['a1:P114_is_equal_in_time_to', X, Y],O1,M1,U1), fact(['a1:P114_is_equal_in_time_to', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P114_is_equal_in_time_to', X, Y],chk1,M1,U1), fact(['a1:P114_is_equal_in_time_to', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:relatedInformationObjects', X0, X3],chk1,_,_), fact(['a1:P_E73_Information_Object', X0, X1],O1,M1,U1), fact(['a1:referredBySame', X1, X2],O2,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E73_Information_Object', X0, X1],chk1,M1,U1), fact(['a1:referredBySame', X1, X2],chk1,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Burial', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Burial', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E13_Attribute_Assignment', X1],chk1,_,_), fact(['a1:P140i_was_attributed_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P140i_was_attributed_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P_E53_Place', X, X],chk1,_,_), fact(['a1:E53_Place', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E53_Place', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P23i_surrendered_title_through', X, Y],chk1,_,_), fact(['a1:P23_transferred_title_from', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P23_transferred_title_from', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P23_transferred_title_from', X, Y],chk1,_,_), fact(['a1:P23i_surrendered_title_through', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P23i_surrendered_title_through', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P27i_was_origin_of', X, Z],chk1,_,_), fact(['a1:P27i_was_origin_of', X, Y],O1,M1,U1), fact(['a1:P27i_was_origin_of', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P27i_was_origin_of', X, Y],chk1,M1,U1), fact(['a1:P27i_was_origin_of', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E29_Design_or_Procedure', X],chk1,_,_), fact(['a1:P33i_was_used_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P33i_was_used_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P74_has_current_or_former_residence', X, Y],chk1,_,_), fact(['a1:P74i_is_current_or_former_residence_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P74i_is_current_or_former_residence_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P74i_is_current_or_former_residence_of', X, Y],chk1,_,_), fact(['a1:P74_has_current_or_former_residence', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P74_has_current_or_former_residence', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E28_Conceptual_Object', X],chk1,_,_), fact(['a1:E90_Symbolic_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P107i_is_current_or_former_member_of', X, Y],chk1,_,_), fact(['a1:P107_has_current_or_former_member', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P107_has_current_or_former_member', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P107_has_current_or_former_member', X, Y],chk1,_,_), fact(['a1:P107i_is_current_or_former_member_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P107i_is_current_or_former_member_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P1i_identifies', X, Y],chk1,_,_), fact(['a1:P131i_identifies', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P131i_identifies', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a2:keywords', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:keywords', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E44_Place_Appellation', X1],chk1,_,_), fact(['a1:P87_is_identified_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P87_is_identified_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P15i_influenced', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P15i_influenced', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P109_has_current_or_former_curator', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P109_has_current_or_former_curator', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P141i_was_assigned_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E13_Attribute_Assignment', X],chk1,_,_), fact(['a1:E16_Measurement', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E16_Measurement', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X1],chk1,_,_), fact(['a1:P124_transformed', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P124_transformed', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P120i_occurs_after', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P120i_occurs_after', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedPlaces', X0, X3],chk1,_,_), fact(['a1:P_E53_Place', X0, X1],O1,M1,U1), fact(['a1:P67_refers_to', X1, X2],O2,M2,U2), fact(['a1:P_E53_Place', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E53_Place', X0, X1],chk1,M1,U1), fact(['a1:P67_refers_to', X1, X2],chk1,M2,U2), fact(['a1:P_E53_Place', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a5:Agent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:Agent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:Agent', X],chk1,_,_), fact(['a3:Agent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:Agent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:P62_depicts', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P62_depicts', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E36_Visual_Item', X1],chk1,_,_), fact(['a1:P65_shows_visual_item', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P65_shows_visual_item', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:initiatingEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:initiatingEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E5_Event', X1],chk1,_,_), fact(['a1:P11i_participated_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P11i_participated_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P140_assigned_attribute_to', X, Y],chk1,_,_), fact(['a1:P39_measured', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P39_measured', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E83_Type_Creation', X1],chk1,_,_), fact(['a1:P136i_supported_type_creation', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P136i_supported_type_creation', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E28_Conceptual_Object', X],chk1,_,_), fact(['a1:E55_Type', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E55_Type', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:officiator', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:officiator', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedPlaces', X, Y],chk1,_,_), fact(['a1:relatedPlaces', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:relatedPlaces', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P147i_was_curated_by', X, Y],chk1,_,_), fact(['a1:P147_curated', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P147_curated', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P147_curated', X, Y],chk1,_,_), fact(['a1:P147i_was_curated_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P147i_was_curated_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P53_has_former_or_current_location', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P53_has_former_or_current_location', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Birth', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Birth', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a12:subject', X, Y],chk1,_,_), fact(['a2:keywords', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:keywords', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E3_Condition_State', X],chk1,_,_), fact(['a1:P5_consists_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P5_consists_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:nick', X, Y],chk1,_,_), fact(['a3:icqChatID', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:icqChatID', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P118i_is_overlapped_in_time_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P118i_is_overlapped_in_time_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E42_Identifier', X1],chk1,_,_), fact(['a1:P48_has_preferred_identifier', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P48_has_preferred_identifier', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P44i_is_condition_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P44i_is_condition_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E29_Design_or_Procedure', X],chk1,_,_), fact(['a1:P69_is_associated_with', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P69_is_associated_with', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E11_Modification', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E11_Modification', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P93_took_out_of_existence', X, Y],chk1,_,_), fact(['a1:P93i_was_taken_out_of_existence_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk1,_,_), fact(['a1:P93_took_out_of_existence', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P93_took_out_of_existence', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E78_Collection', X1],chk1,_,_), fact(['a1:P109i_is_current_or_former_curator_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P109i_is_current_or_former_curator_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P76i_provides_access_to', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P76i_provides_access_to', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92i_was_brought_into_existence_by', X, Y],chk1,_,_), fact(['a1:P94i_was_created_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P94i_was_created_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:E86_Leaving', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E86_Leaving', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:Nothing', X],chk1,_,_), fact(['a3:Document', X],O1,M1,U1), fact(['a3:Project', X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:Document', X],chk1,M1,U1), fact(['a3:Project', X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P20i_was_purpose_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P20i_was_purpose_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a13:Event', X],chk1,_,_), fact(['a2:Event', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Event', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P27_moved_from', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P27_moved_from', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:birthday', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:birthday', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E85_Joining', X],chk1,_,_), fact(['a1:P143_joined', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P143_joined', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P115i_is_finished_by', X, Y],chk1,_,_), fact(['a1:P115_finishes', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P115_finishes', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P115_finishes', X, Y],chk1,_,_), fact(['a1:P115i_is_finished_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P115i_is_finished_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X],chk1,_,_), fact(['a1:P25i_moved_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P25i_moved_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:witness', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:witness', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E36_Visual_Item', X],chk1,_,_), fact(['a1:E38_Image', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E38_Image', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E33_Linguistic_Object', X],chk1,_,_), fact(['a1:P73_has_translation', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P73_has_translation', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P7i_witnessed', X, Y],chk1,_,_), fact(['a1:P26i_was_destination_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P26i_was_destination_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:weblog', Y1, X],O1,M1,U1), fact(['a3:weblog', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:weblog', Y1, X],chk1,M1,U1), fact(['a3:weblog', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P15i_influenced', X, Y],chk1,_,_), fact(['a1:P17i_motivated', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P17i_motivated', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X1],chk1,_,_), fact(['a1:P142_used_constituent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P142_used_constituent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P125_used_object_of_type', X, Y],chk1,_,_), fact(['a1:P125i_was_type_of_object_used_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P125i_was_type_of_object_used_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P125i_was_type_of_object_used_in', X, Y],chk1,_,_), fact(['a1:P125_used_object_of_type', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P125_used_object_of_type', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:workplaceHomepage', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:workplaceHomepage', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P134i_was_continued_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P134i_was_continued_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E28_Conceptual_Object', X],chk1,_,_), fact(['a1:E89_Propositional_Object', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Literal', X1],chk1,_,_), fact(['a3:skypeID', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:skypeID', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:isPrimaryTopicOf', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:isPrimaryTopicOf', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P88i_forms_part_of', X, Y],chk1,_,_), fact(['a1:P88_consists_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P88_consists_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P88_consists_of', X, Y],chk1,_,_), fact(['a1:P88i_forms_part_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P88i_forms_part_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:participant', X, Y],chk1,_,_), fact(['a2:relationship', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:relationship', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:relationship', X, Y],chk1,_,_), fact(['a2:participant', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:participant', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P21i_was_purpose_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P21i_was_purpose_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X1],chk1,_,_), fact(['a1:P17_was_motivated_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P17_was_motivated_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P140_assigned_attribute_to', X, Y],chk1,_,_), fact(['a1:P34_concerned', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P34_concerned', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E9_Move', X],chk1,_,_), fact(['a1:P25_moved', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P25_moved', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Accession', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Accession', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:interest', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:interest', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X],chk1,_,_), fact(['a1:E58_Measurement_Unit', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E58_Measurement_Unit', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P105_right_held_by', X, Y],chk1,_,_), fact(['a1:P105i_has_right_on', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P105i_has_right_on', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P105i_has_right_on', X, Y],chk1,_,_), fact(['a1:P105_right_held_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P105_right_held_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Murder', X],chk1,_,_), fact(['a2:Assassination', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Assassination', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E12_Production', X],chk1,_,_), fact(['a1:P108_has_produced', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P108_has_produced', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E33_Linguistic_Object', X],chk1,_,_), fact(['a1:E35_Title', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E35_Title', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:spectator', X, Y],chk1,_,_), fact(['a2:witness', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:witness', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E65_Creation', X],chk1,_,_), fact(['a1:E83_Type_Creation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E83_Type_Creation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a2:mother', X, Y1],O1,M1,U1), fact(['a2:mother', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a2:mother', X, Y1],chk1,M1,U1), fact(['a2:mother', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P32i_was_technique_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P32i_was_technique_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P128_carries', X, Y],chk1,_,_), fact(['a1:P65_shows_visual_item', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P65_shows_visual_item', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E29_Design_or_Procedure', X1],chk1,_,_), fact(['a1:P69_is_associated_with', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P69_is_associated_with', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P135_created_type', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P135_created_type', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14_carried_out_by', X, Y],chk1,_,_), fact(['a1:P22_transferred_title_to', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P22_transferred_title_to', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P49_has_former_or_current_keeper', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P49_has_former_or_current_keeper', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E30_Right', X],chk1,_,_), fact(['a1:P104i_applies_to', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P104i_applies_to', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P86_falls_within', X, Y],chk1,_,_), fact(['a1:P86i_contains', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P86i_contains', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P86i_contains', X, Y],chk1,_,_), fact(['a1:P86_falls_within', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P86_falls_within', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E5_Event', X],chk1,_,_), fact(['a1:P11_had_participant', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P11_had_participant', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P2_has_type', X, Y],chk1,_,_), fact(['a1:P2i_is_type_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P2i_is_type_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P2i_is_type_of', X, Y],chk1,_,_), fact(['a1:P2_has_type', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P2_has_type', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:workplaceHomepage', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:workplaceHomepage', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:E52_Time-Span', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E52_Time-Span', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E6_Destruction', X1],chk1,_,_), fact(['a1:P13i_was_destroyed_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P13i_was_destroyed_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X],chk1,_,_), fact(['a1:P129_is_about', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P129_is_about', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P103_was_intended_for', X, Y],chk1,_,_), fact(['a1:P103i_was_intention_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P103i_was_intention_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P103i_was_intention_of', X, Y],chk1,_,_), fact(['a1:P103_was_intended_for', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P103_was_intended_for', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:birthday', X, Y1],O1,M1,U1), fact(['a3:birthday', X, Y2],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:birthday', X, Y1],chk1,M1,U1), fact(['a3:birthday', X, Y2],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E33_Linguistic_Object', X],chk1,_,_), fact(['a1:E34_Inscription', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E34_Inscription', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P21_had_general_purpose', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P21_had_general_purpose', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E64_End_of_Existence', X],chk1,_,_), fact(['a1:E69_Death', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E69_Death', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E72_Legal_Object', X],chk1,_,_), fact(['a1:E18_Physical_Thing', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:relatedPlaces', X0, X3],chk1,_,_), fact(['a1:P_E53_Place', X0, X1],O1,M1,U1), fact(['a1:referToSame', X1, X2],O2,M2,U2), fact(['a1:P_E53_Place', X2, X3],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P_E53_Place', X0, X1],chk1,M1,U1), fact(['a1:referToSame', X1, X2],chk1,M2,U2), fact(['a1:P_E53_Place', X2, X3],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:P11_had_participant', X, Y],chk1,_,_), fact(['a1:P143_joined', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P143_joined', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141_assigned', X, Y],chk1,_,_), fact(['a1:P35_has_identified', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P35_has_identified', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:employer', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:employer', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E86_Leaving', X],chk1,_,_), fact(['a1:P145_separated', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P145_separated', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P98i_was_born', X, X2],O1,M1,U1), fact(['a1:P98i_was_born', X, X1],O2,M2,U2), fact(['a1:E21_Person', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P98i_was_born', X, X2],chk1,M1,U1), fact(['a1:P98i_was_born', X, X1],chk1,M2,U2), fact(['a1:E21_Person', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P114_is_equal_in_time_to', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P114_is_equal_in_time_to', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E5_Event', X],chk1,_,_), fact(['a1:P20i_was_purpose_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P20i_was_purpose_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E15_Identifier_Assignment', X1],chk1,_,_), fact(['a1:P38i_was_deassigned_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P38i_was_deassigned_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E54_Dimension', X1],chk1,_,_), fact(['a1:P83_had_at_least_duration', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P83_had_at_least_duration', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X1],chk1,_,_), fact(['a3:page', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:page', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:precedingEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:precedingEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P15i_influenced', X, Y],chk1,_,_), fact(['a1:P134i_was_continued_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P134i_was_continued_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E63_Beginning_of_Existence', X],chk1,_,_), fact(['a1:E67_Birth', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E67_Birth', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X1],chk1,_,_), fact(['a1:P133_is_separated_from', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P133_is_separated_from', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:pastProject', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:pastProject', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:differentFrom', X, Y],chk1,_,_), fact(['a2:concludingEvent', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:concludingEvent', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P19_was_intended_use_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P19_was_intended_use_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:E35_Title', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E35_Title', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E67_Birth', X],chk1,_,_), fact(['a1:P98_brought_into_life', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P98_brought_into_life', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E57_Material', X1],chk1,_,_), fact(['a1:P68_foresees_use_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P68_foresees_use_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P16_used_specific_object', X, Y],chk1,_,_), fact(['a1:P33_used_specific_technique', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P33_used_specific_technique', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X1],chk1,_,_), fact(['a2:precedingEvent', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:precedingEvent', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P17i_motivated', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P17i_motivated', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E64_End_of_Existence', X],chk1,_,_), fact(['a1:E68_Dissolution', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E68_Dissolution', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P12i_was_present_at', X, Y],chk1,_,_), fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P52i_is_current_owner_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P52i_is_current_owner_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P120_occurs_before', X, Z],chk1,_,_), fact(['a1:P120_occurs_before', X, Y],O1,M1,U1), fact(['a1:P120_occurs_before', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P120_occurs_before', X, Y],chk1,M1,U1), fact(['a1:P120_occurs_before', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P89_falls_within', X, Y],chk1,_,_), fact(['a1:P89i_contains', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P89i_contains', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P89i_contains', X, Y],chk1,_,_), fact(['a1:P89_falls_within', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P89_falls_within', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P121_overlaps_with', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P121_overlaps_with', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P88_consists_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P88_consists_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P129i_is_subject_of', X, Y],chk1,_,_), fact(['a1:P129_is_about', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P129_is_about', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P129_is_about', X, Y],chk1,_,_), fact(['a1:P129i_is_subject_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P129i_is_subject_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:agent', X, Y],chk1,_,_), fact(['a2:state', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:state', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],chk1,_,_), fact(['a1:P50i_is_current_keeper_of', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P50i_is_current_keeper_of', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:precedingEvent', X, Z],chk1,_,_), fact(['a2:precedingEvent', X, Y],O1,M1,U1), fact(['a2:precedingEvent', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a2:precedingEvent', X, Y],chk1,M1,U1), fact(['a2:precedingEvent', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a3:Group', X],chk1,_,_), fact(['a3:member', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:member', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['rdfs:Resource', X],chk1,_,_), fact(['rdfs:Class', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['rdfs:Class', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P4_has_time-span', X, Y],chk1,_,_), fact(['a1:P4i_is_time-span_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P4i_is_time-span_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P4i_is_time-span_of', X, Y],chk1,_,_), fact(['a1:P4_has_time-span', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P4_has_time-span', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E72_Legal_Object', X],chk1,_,_), fact(['a1:P105_right_held_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P105_right_held_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:aimChatID', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:aimChatID', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P122_borders_with', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P122_borders_with', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:OnlineAccount', X],chk1,_,_), fact(['a3:OnlineGamingAccount', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:OnlineGamingAccount', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P7_took_place_at', X, Y],chk1,_,_), fact(['a1:P26_moved_to', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P26_moved_to', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X1],chk1,_,_), fact(['a1:P31_has_modified', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P31_has_modified', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P83_had_at_least_duration', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P83_had_at_least_duration', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:GroupEvent', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:GroupEvent', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X1],chk1,_,_), fact(['a1:P86_falls_within', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P86_falls_within', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', Y1, Y2],chk1,_,_), fact(['a3:yahooChatID', Y1, X],O1,M1,U1), fact(['a3:yahooChatID', Y2, X],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a3:yahooChatID', Y1, X],chk1,M1,U1), fact(['a3:yahooChatID', Y2, X],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P106_is_composed_of', X, Y],chk1,_,_), fact(['a1:P106i_forms_part_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P106i_forms_part_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P106i_forms_part_of', X, Y],chk1,_,_), fact(['a1:P106_is_composed_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P106_is_composed_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P141i_was_assigned_by', X, Y],chk1,_,_), fact(['a1:P40i_was_observed_in', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P40i_was_observed_in', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P133_is_separated_from', X, Y],chk1,_,_), fact(['a1:P133_is_separated_from', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P133_is_separated_from', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E70_Thing', X],chk1,_,_), fact(['a1:P130_shows_features_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P130_shows_features_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a14:ProperInterval', X],chk1,_,_), fact(['a2:Interval', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Interval', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P52_has_current_owner', X, Y],chk1,_,_), fact(['a1:P52i_is_current_owner_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P52i_is_current_owner_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P52i_is_current_owner_of', X, Y],chk1,_,_), fact(['a1:P52_has_current_owner', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P52_has_current_owner', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E69_Death', X1],chk1,_,_), fact(['a1:P100i_died_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P100i_died_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:made', X, Y],chk1,_,_), fact(['a3:maker', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:maker', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:maker', X, Y],chk1,_,_), fact(['a3:made', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:made', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E81_Transformation', X],chk1,_,_), fact(['a1:P124_transformed', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P124_transformed', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E41_Appellation', X],chk1,_,_), fact(['a1:E82_Actor_Appellation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E82_Actor_Appellation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E55_Type', X1],chk1,_,_), fact(['a1:P32_used_general_technique', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P32_used_general_technique', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P123_resulted_in', X, Y],chk1,_,_), fact(['a1:P123i_resulted_from', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P123i_resulted_from', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P123i_resulted_from', X, Y],chk1,_,_), fact(['a1:P123_resulted_in', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P123_resulted_in', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P10i_contains', X, Z],chk1,_,_), fact(['a1:P10i_contains', X, Y],O1,M1,U1), fact(['a1:P10i_contains', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P10i_contains', X, Y],chk1,M1,U1), fact(['a1:P10i_contains', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:P51_has_former_or_current_owner', X, Y],chk1,_,_), fact(['a1:P51i_is_former_or_current_owner_of', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P51i_is_former_or_current_owner_of', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P51i_is_former_or_current_owner_of', X, Y],chk1,_,_), fact(['a1:P51_has_former_or_current_owner', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P51_has_former_or_current_owner', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E15_Identifier_Assignment', X1],chk1,_,_), fact(['a1:P142i_was_used_in', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P142i_was_used_in', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Death', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Death', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P92_brought_into_existence', X, Y],chk1,_,_), fact(['a1:P98_brought_into_life', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P98_brought_into_life', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X],chk1,_,_), fact(['a1:P93i_was_taken_out_of_existence_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P39i_was_measured_by', X, Y],chk1,_,_), fact(['a1:P39_measured', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P39_measured', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P39_measured', X, Y],chk1,_,_), fact(['a1:P39i_was_measured_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P39i_was_measured_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X1],chk1,_,_), fact(['a1:P116i_is_started_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P116i_is_started_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E90_Symbolic_Object', X],chk1,_,_), fact(['a1:E41_Appellation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E41_Appellation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P106i_forms_part_of', X, Z],chk1,_,_), fact(['a1:P106i_forms_part_of', X, Y],O1,M1,U1), fact(['a1:P106i_forms_part_of', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P106i_forms_part_of', X, Y],chk1,M1,U1), fact(['a1:P106i_forms_part_of', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P50_has_current_keeper', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P50_has_current_keeper', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X],chk1,_,_), fact(['a1:P9_consists_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P9_consists_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E74_Group', X1],chk1,_,_), fact(['a1:P144_joined_with', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P144_joined_with', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X],chk1,_,_), fact(['a3:publications', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:publications', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P46_is_composed_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P46_is_composed_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P59_has_section', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P59_has_section', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E73_Information_Object', X],chk1,_,_), fact(['a1:E36_Visual_Item', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E36_Visual_Item', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E80_Part_Removal', X1],chk1,_,_), fact(['a1:P112i_was_diminished_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P112i_was_diminished_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X],chk1,_,_), fact(['a1:P11i_participated_in', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P11i_participated_in', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X],chk1,_,_), fact(['a1:P78_is_identified_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P78_is_identified_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X1],chk1,_,_), fact(['a1:P34_concerned', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P34_concerned', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:P112i_was_diminished_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P112i_was_diminished_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E1_CRM_Entity', X],chk1,_,_), fact(['a1:P136i_supported_type_creation', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P136i_supported_type_creation', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P144_joined_with', X, Y],chk1,_,_), fact(['a1:P144i_gained_member_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P144i_gained_member_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P144i_gained_member_by', X, Y],chk1,_,_), fact(['a1:P144_joined_with', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P144_joined_with', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Cremation', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Cremation', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P119_meets_in_time_with', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P119_meets_in_time_with', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a7:WeddingEvent_Generic', X],chk1,_,_), fact(['a2:Marriage', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Marriage', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Marriage', X],chk1,_,_), fact(['a7:WeddingEvent_Generic', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a7:WeddingEvent_Generic', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X1],chk1,_,_), fact(['a1:P16i_was_used_for', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16i_was_used_for', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Document', X],chk1,_,_), fact(['a3:Image', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:Image', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P143i_was_joined_by', X, Y],chk1,_,_), fact(['a1:P143_joined', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P143_joined', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P143_joined', X, Y],chk1,_,_), fact(['a1:P143i_was_joined_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P143i_was_joined_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E8_Acquisition', X1],chk1,_,_), fact(['a1:P24i_changed_ownership_through', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P24i_changed_ownership_through', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E2_Temporal_Entity', X],chk1,_,_), fact(['a1:P115i_is_finished_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P115i_is_finished_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E71_Man-Made_Thing', X],chk1,_,_), fact(['a1:P103_was_intended_for', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P103_was_intended_for', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X],chk1,_,_), fact(['a1:P53i_is_former_or_current_location_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:P128_carries', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P128_carries', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a5:RightsStatement', X],chk1,_,_), fact(['a5:LicenseDocument', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a5:LicenseDocument', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E29_Design_or_Procedure', X],chk1,_,_), fact(['a1:P68_foresees_use_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P68_foresees_use_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E53_Place', X1],chk1,_,_), fact(['a1:P89i_contains', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P89i_contains', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E7_Activity', X],chk1,_,_), fact(['a1:P20_had_specific_purpose', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P20_had_specific_purpose', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P46_is_composed_of', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P46_is_composed_of', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X1],chk1,_,_), fact(['a1:P7i_witnessed', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P7i_witnessed', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Naturalization', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Naturalization', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14i_performed', X, Y],chk1,_,_), fact(['a1:P23i_surrendered_title_through', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P23i_surrendered_title_through', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E89_Propositional_Object', X],chk1,_,_), fact(['a1:E30_Right', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E30_Right', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E4_Period', X1],chk1,_,_), fact(['a1:P9_consists_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P9_consists_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E90_Symbolic_Object', X1],chk1,_,_), fact(['a1:P106_is_composed_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P106_is_composed_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:tipjar', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:tipjar', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:account', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:account', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E77_Persistent_Item', X],chk1,_,_), fact(['a1:E70_Thing', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E70_Thing', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P14i_performed', X, Y],chk1,_,_), fact(['a1:P22i_acquired_title_through', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P22i_acquired_title_through', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E9_Move', X],chk1,_,_), fact(['a1:P27_moved_from', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P27_moved_from', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E39_Actor', X1],chk1,_,_), fact(['a1:P105_right_held_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P105_right_held_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Agent', X],chk1,_,_), fact(['a3:icqChatID', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a3:icqChatID', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E24_Physical_Man-Made_Thing', X],chk1,_,_), fact(['a1:E78_Collection', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E78_Collection', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['owl:sameAs', X1, X2],chk1,_,_), fact(['a1:P13i_was_destroyed_by', X, X2],O1,M1,U1), fact(['a1:P13i_was_destroyed_by', X, X1],O2,M2,U2), fact(['a1:E18_Physical_Thing', X],O3,M3,U3) ==> \+member(del,[O1,O2,O3]) | fact(['a1:P13i_was_destroyed_by', X, X2],chk1,M1,U1), fact(['a1:P13i_was_destroyed_by', X, X1],chk1,M2,U2), fact(['a1:E18_Physical_Thing', X],chk1,M3,U3), applied_rules(1,bwd).
fact(['a1:P15_was_influenced_by', X, Y],chk1,_,_), fact(['a1:P136_was_based_on', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P136_was_based_on', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P16_used_specific_object', X, Y],chk1,_,_), fact(['a1:P16i_was_used_for', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16i_was_used_for', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P16i_was_used_for', X, Y],chk1,_,_), fact(['a1:P16_used_specific_object', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P16_used_specific_object', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P88_consists_of', X, Z],chk1,_,_), fact(['a1:P88_consists_of', X, Y],O1,M1,U1), fact(['a1:P88_consists_of', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P88_consists_of', X, Y],chk1,M1,U1), fact(['a1:P88_consists_of', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a2:Performance', X],chk1,_,_), fact(['a15:Performance', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a15:Performance', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a15:Performance', X],chk1,_,_), fact(['a2:Performance', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Performance', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E19_Physical_Object', X],chk1,_,_), fact(['a1:P54_has_current_permanent_location', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P54_has_current_permanent_location', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P88i_forms_part_of', X, Z],chk1,_,_), fact(['a1:P88i_forms_part_of', X, Y],O1,M1,U1), fact(['a1:P88i_forms_part_of', Y, Z],O2,M2,U2) ==> \+member(del,[O1,O2]) | fact(['a1:P88i_forms_part_of', X, Y],chk1,M1,U1), fact(['a1:P88i_forms_part_of', Y, Z],chk1,M2,U2), applied_rules(1,bwd).
fact(['a1:E26_Physical_Feature', X],chk1,_,_), fact(['a1:E25_Man-Made_Feature', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:E25_Man-Made_Feature', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E65_Creation', X],chk1,_,_), fact(['a1:P94_has_created', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P94_has_created', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P128i_is_carried_by', X, Y],chk1,_,_), fact(['a1:P128_carries', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P128_carries', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P128_carries', X, Y],chk1,_,_), fact(['a1:P128i_is_carried_by', Y, X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P128i_is_carried_by', Y, X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:IndividualEvent', X],chk1,_,_), fact(['a2:Emigration', X],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:Emigration', X],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P31_has_modified', X, Y],chk1,_,_), fact(['a1:P112_diminished', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P112_diminished', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:P16i_was_used_for', X, Y],chk1,_,_), fact(['a1:P33i_was_used_by', X, Y],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P33i_was_used_by', X, Y],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E52_Time-Span', X1],chk1,_,_), fact(['a1:P83i_was_minimum_duration_of', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P83i_was_minimum_duration_of', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a2:Event', X],chk1,_,_), fact(['a2:organization', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:organization', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E18_Physical_Thing', X],chk1,_,_), fact(['a1:P113i_was_removed_by', X, Anon0],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P113i_was_removed_by', X, Anon0],chk1,M1,U1), applied_rules(1,bwd).
fact(['a3:Person', X1],chk1,_,_), fact(['a2:child', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a2:child', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).
fact(['a1:E49_Time_Appellation', X1],chk1,_,_), fact(['a1:P78_is_identified_by', Anon0, X1],O1,M1,U1) ==> \+member(del,[O1]) | fact(['a1:P78_is_identified_by', Anon0, X1],chk1,M1,U1), applied_rules(1,bwd).

	
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
phase(5), fact(['a1:P22i_acquired_title_through', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P24_transferred_title_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P110i_was_augmented_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E79_Part_Addition', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', X, X2],add,M1,U1), fact(['a1:P41_classified', X, X1],add,M2,U2), fact(['a1:E17_Type_Assignment', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P41_classified',M1),('a1:P41_classified',M2),('a1:E17_Type_Assignment',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P33_used_specific_technique', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P116_starts', X, Y],add,M1,U1), fact(['a1:P116_starts', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P116_starts',M1),('a1:P116_starts',M2)],M), fact(['a1:P116_starts', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P124i_was_transformed_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E81_Transformation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P104_is_subject_to', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P114_is_equal_in_time_to', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P127_has_broader_term', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P127i_has_narrower_term', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P127i_has_narrower_term', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P127_has_broader_term', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:followingEvent', X, Y],add,M1,U1), fact(['a2:followingEvent', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a2:followingEvent',M1),('a2:followingEvent',M2)],M), fact(['a2:followingEvent', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E34_Inscription', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E37_Mark', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P94i_was_created_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E65_Creation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:aimChatID', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E7_Activity', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:depiction', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Image', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P23_transferred_title_from', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Murder', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Death', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E14_Condition_Assessment', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P31_has_modified', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P123i_resulted_from', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E81_Transformation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:homepage', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P96_by_mother', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P96i_gave_birth', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P96i_gave_birth', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P96_by_mother', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P100_was_death_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E69_Death', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41i_was_classified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P71i_is_listed_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41i_was_classified_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P41_classified', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P41i_was_classified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P14_carried_out_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P93_took_out_of_existence', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P54_has_current_permanent_location', X, X2],add,M1,U1), fact(['a1:P54_has_current_permanent_location', X, X1],add,M2,U2), fact(['a1:E19_Physical_Object', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P54_has_current_permanent_location',M1),('a1:P54_has_current_permanent_location',M2),('a1:E19_Physical_Object',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P146_separated_from', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P17_was_motivated_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P17i_motivated', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P17i_motivated', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P17_was_motivated_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39i_was_measured_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P113_removed', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73_has_translation', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P73i_is_translation_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P73_has_translation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P2i_is_type_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P141i_was_assigned_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P102_has_title', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P38_deassigned', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P54_has_current_permanent_location', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P54i_is_current_permanent_location_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P54i_is_current_permanent_location_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P54_has_current_permanent_location', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E21_Person', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E20_Biological_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['rdfs:Container', X],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Resource', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:publications', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedInformationObjects', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:relatedInformationObjects', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P126_employed', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:death', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Divorce', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:GroupEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P136_was_based_on', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E83_Type_Creation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Graduation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P29i_received_custody_through', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P29_custody_received_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P29_custody_received_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P29i_received_custody_through', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P10_falls_within', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P10i_contains', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P10i_contains', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P10_falls_within', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P142_used_constituent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P16_used_specific_object', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P147i_was_curated_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E78_Collection', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E53_Place', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P72i_is_language_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P70_documents', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P124_transformed', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Person', X],add,M1,U1) ==> member(U,[U1]) | fact(['a4:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P148i_is_component_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P148_has_component', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P148_has_component', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P148i_is_component_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P15_was_influenced_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P107_has_current_or_former_member', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:made', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P30_transferred_custody_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P30i_custody_transferred_through', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P30i_custody_transferred_through', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P30_transferred_custody_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P125_used_object_of_type', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:birth', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E65_Creation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E81_Transformation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P24i_changed_ownership_through', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P24_transferred_title_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P24_transferred_title_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P24i_changed_ownership_through', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Annulment', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:GroupEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Promotion', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:PositionChange', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P31_has_modified', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Ordination', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P130_shows_features_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P118_overlaps_in_time_with', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P144i_gained_member_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E85_Joining', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P124i_was_transformed_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P15_was_influenced_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E79_Part_Addition', X],add,M1,U1), fact(['a1:E80_Part_Removal', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:E79_Part_Addition',M1),('a1:E80_Part_Removal',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P135_created_type', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P94_has_created', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P7_took_place_at', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:Jurisdiction', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:LocationPeriodOrJurisdiction', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P56i_is_found_on', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E26_Physical_Feature', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P1_is_identified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P126i_was_employed_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P126_employed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P126_employed', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P126i_was_employed_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:principal', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:myersBriggs', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Demotion', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:PositionChange', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:relationship', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P112_diminished', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P112i_was_diminished_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P112i_was_diminished_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P112_diminished', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:openid', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:isPrimaryTopicOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P141_assigned', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P141i_was_assigned_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P44_has_condition', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P45_consists_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P50i_is_current_keeper_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P26_moved_to', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P26i_was_destination_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P26i_was_destination_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P26_moved_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:img', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:depiction', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P24_transferred_title_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P133_is_separated_from', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P94_has_created', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P94i_was_created_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P94i_was_created_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P94_has_created', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67i_is_referred_to_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P9_consists_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P9i_forms_part_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P9i_forms_part_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P9_consists_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P51_has_former_or_current_owner', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P68i_use_foreseen_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:IndividualEvent', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P138i_has_representation', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P138_represents', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P138_represents', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P138i_has_representation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P51_has_former_or_current_owner', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Organization', X],add,M1,U1), fact(['a3:Person', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:Organization',M1),('a3:Person',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:state', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a6:childOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P55i_currently_holds', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P19_was_intended_use_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E47_Spatial_Coordinates', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:workInfoHomepage', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:depicts', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:depiction', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:depiction', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:depicts', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['rdfs:Literal', X],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Resource', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P52_has_current_owner', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P105_right_held_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:concurrentEvent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P58_has_section_definition', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E46_Section_Definition', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:surname', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P56i_is_found_on', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P144_joined_with', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E85_Joining', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P130i_features_are_also_found_on', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:event', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P43_has_dimension', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P56_bears_feature', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P56i_is_found_on', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P56i_is_found_on', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P56_bears_feature', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P83_had_at_least_duration', X, X2],add,M1,U1), fact(['a1:P83_had_at_least_duration', X, X1],add,M2,U2), fact(['a1:E52_Time-Span', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P83_had_at_least_duration',M1),('a1:P83_had_at_least_duration',M2),('a1:E52_Time-Span',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:participant', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Relationship', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P140_assigned_attribute_to', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P4_has_time-span', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13_destroyed', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P13i_was_destroyed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P13_destroyed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P107i_is_current_or_former_member_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E12_Production', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:employer', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E15_Identifier_Assignment', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P117_occurs_during', X, Y],add,M1,U1), fact(['a1:P117_occurs_during', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P117_occurs_during',M1),('a1:P117_occurs_during',M2)],M), fact(['a1:P117_occurs_during', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E63_Beginning_of_Existence', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P117i_includes', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P117_occurs_during', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P117_occurs_during', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P117i_includes', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P10i_contains', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P120i_occurs_after', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P28_custody_surrendered_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P84i_was_maximum_duration_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P37i_was_assigned_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', X, X2],add,M1,U1), fact(['a1:P39_measured', X, X1],add,M2,U2), fact(['a1:E16_Measurement', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P39_measured',M1),('a1:P39_measured',M2),('a1:E16_Measurement',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P147_curated', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E78_Collection', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E68_Dissolution', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P65i_is_shown_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P65_shows_visual_item', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P65_shows_visual_item', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P65i_is_shown_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P56_bears_feature', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E90_Symbolic_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P120_occurs_before', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E85_Joining', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P58_has_section_definition', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P146i_lost_member_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E86_Leaving', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P8i_witnessed', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P37_assigned', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P118_overlaps_in_time_with', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E4_Period', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Event', X],add,M1,U1) ==> member(U,[U1]) | fact(['a7:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:officiator', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P62i_is_depicted_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P72_has_language', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E56_Language', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P138_represents', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P70i_is_documented_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E31_Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P32_used_general_technique', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:aimChatID', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P105i_has_right_on', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:age', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P100_was_death_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P100i_died_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P100i_died_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P100_was_death_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:skypeID', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:participant', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P11_had_participant', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:father', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P82_at_some_time_within', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P31i_was_modified_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:gender', X, Y1],add,M1,U1), fact(['a3:gender', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:gender',M1),('a3:gender',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedPlaces', X, Y],add,M1,U1), fact(['a1:relatedPlaces', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:relatedPlaces',M1),('a1:relatedPlaces',M2)],M), fact(['a1:relatedPlaces', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P141_assigned', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Document', X],add,M1,U1), fact(['a3:Organization', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:Document',M1),('a3:Organization',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P72_has_language', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P105i_has_right_on', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P97_from_father', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P110i_was_augmented_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P136_was_based_on', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P136i_supported_type_creation', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P136i_supported_type_creation', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P136_was_based_on', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P22i_acquired_title_through', Y1, X],add,M1,U1), fact(['a1:P22i_acquired_title_through', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P22i_acquired_title_through',M1),('a1:P22i_acquired_title_through',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P100_was_death_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P45_consists_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P45i_is_incorporated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P45i_is_incorporated_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P45_consists_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:jabberID', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P78i_identifies', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:primaryTopic', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P53_has_former_or_current_location', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P53i_is_former_or_current_location_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P53_has_former_or_current_location', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P37_assigned', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P37i_was_assigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P37i_was_assigned_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P37_assigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:lastName', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P84i_was_maximum_duration_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P32_used_general_technique', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P125_used_object_of_type', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P32_used_general_technique', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P32i_was_technique_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P32i_was_technique_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P32_used_general_technique', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P59i_is_located_on_or_within', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P59_has_section', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P59_has_section', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P59i_is_located_on_or_within', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox', Y1, X],add,M1,U1), fact(['a3:mbox', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:mbox',M1),('a3:mbox',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:Marriage', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:GroupEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E79_Part_Addition', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P35_has_identified', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P35i_was_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P35i_was_identified_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P35_has_identified', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:focus', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a8:Concept', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:img', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Image', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Organization', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:topic_interest', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:eventInterval', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Interval', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P116i_is_started_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P31i_was_modified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:birth', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Birth', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P132_overlaps_with', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P132_overlaps_with', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E71_Man-Made_Thing', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P_E71_Man-Made_Thing', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E66_Formation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P40_observed_dimension', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E16_Measurement', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyPrecedingEvent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P70_documents', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P131_is_identified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P102i_is_title_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P11i_participated_in', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P29_custody_received_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:event', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:agent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:event', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P109_has_current_or_former_curator', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E78_Collection', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P136_was_based_on', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P30_transferred_custody_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyFollowingEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P124i_was_transformed_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P132_overlaps_with', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P110_augmented', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P110i_was_augmented_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P110i_was_augmented_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P110_augmented', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P142i_was_used_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E21_Person', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P44_has_condition', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P78_is_identified_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P78i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P78i_identifies', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P78_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P112_diminished', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P8i_witnessed', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P5i_forms_part_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P5_consists_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P5_consists_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P5i_forms_part_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P116_starts', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39i_was_measured_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E16_Measurement', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:precedingEvent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,M1,U1), fact(['a1:referToSame', X1, X2],add,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E71_Man-Made_Thing',M1),('a1:referToSame',M2),('a1:P_E71_Man-Made_Thing',M3)],M), fact(['a1:relatedManMadeThings', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P5i_forms_part_of', X, X2],add,M1,U1), fact(['a1:P5i_forms_part_of', X, X1],add,M2,U2), fact(['a1:E3_Condition_State', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P5i_forms_part_of',M1),('a1:P5i_forms_part_of',M2),('a1:E3_Condition_State',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P10i_contains', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P125i_was_type_of_object_used_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P138_represents', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P10_falls_within', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P56_bears_feature', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E26_Physical_Feature', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E44_Place_Appellation', X],add,M1,U1), fact(['a1:E49_Time_Appellation', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:E44_Place_Appellation',M1),('a1:E49_Time_Appellation',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P71_lists', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyPrecedingEvent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:child', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Event', X],add,M1,U1) ==> member(U,[U1]) | fact(['a9:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P91i_is_unit_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E58_Measurement_Unit', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E50_Date', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E49_Time_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P23_transferred_title_from', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P110_augmented', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P55i_currently_holds', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P55i_currently_holds', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P55_has_current_location', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E31_Document', X0, X1],add,M1,U1), fact(['a1:referredBySame', X1, X2],add,M2,U2), fact(['a1:P_E31_Document', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E31_Document',M1),('a1:referredBySame',M2),('a1:P_E31_Document',M3)],M), fact(['a1:relatedDocuments', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedManMadeThings', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:relatedManMadeThings', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P74i_is_current_or_former_residence_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P103i_was_intention_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P84_had_at_most_duration', X, X2],add,M1,U1), fact(['a1:P84_had_at_most_duration', X, X1],add,M2,U2), fact(['a1:E52_Time-Span', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P84_had_at_most_duration',M1),('a1:P84_had_at_most_duration',M2),('a1:E52_Time-Span',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P88_consists_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E83_Type_Creation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P119i_is_met_in_time_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E16_Measurement', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P97i_was_father_for', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P42i_was_assigned_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E17_Type_Assignment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P106_is_composed_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P43_has_dimension', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P81_ongoing_throughout', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:family_name', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P140_assigned_attribute_to', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P70i_is_documented_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P7_took_place_at', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P45i_is_incorporated_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E10_Transfer_of_Custody', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73_has_translation', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', X, X2],add,M1,U1), fact(['a1:P95i_was_formed_by', X, X1],add,M2,U2), fact(['a1:E74_Group', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P95i_was_formed_by',M1),('a1:P95i_was_formed_by',M2),('a1:E74_Group',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P134_continued', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P138i_has_representation', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P109_has_current_or_former_curator', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P109i_is_current_or_former_curator_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P109i_is_current_or_former_curator_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P109_has_current_or_former_curator', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P11_had_participant', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P71_lists', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P44_has_condition', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P44i_is_condition_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P44i_is_condition_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P44_has_condition', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:openid', Y1, X],add,M1,U1), fact(['a3:openid', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:openid',M1),('a3:openid',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P132_overlaps_with', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P111i_was_added_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E79_Part_Addition', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P40i_was_observed_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E16_Measurement', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P102_has_title', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E35_Title', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P99_dissolved', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P99i_was_dissolved_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P119_meets_in_time_with', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P144_joined_with', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:parent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P140_assigned_attribute_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:initiatingEvent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P104i_applies_to', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P71i_is_listed_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E32_Authority_Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P35i_was_identified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E57_Material', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E53_Place', X0, X1],add,M1,U1), fact(['a1:referredBySame', X1, X2],add,M2,U2), fact(['a1:P_E53_Place', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E53_Place',M1),('a1:referredBySame',M2),('a1:P_E53_Place',M3)],M), fact(['a1:relatedPlaces', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P34i_was_assessed_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P121_overlaps_with', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P121_overlaps_with', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13_destroyed', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E6_Destruction', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P84_had_at_most_duration', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P45_consists_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P100i_died_in', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P123_resulted_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E51_Contact_Point', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, X2],add,M1,U1), fact(['a2:father', X, X1],add,M2,U2), fact(['a3:Person', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a2:father',M1),('a2:father',M2),('a3:Person',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, X4],add,M1,U1), fact(['a2:mother', X, X3],add,M2,U2), fact(['a3:Person', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a2:mother',M1),('a2:mother',M2),('a3:Person',M3)],M), fact(['owl:sameAs', X3, X4],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P9i_forms_part_of', X, X2],add,M1,U1), fact(['a1:P9i_forms_part_of', X, X1],add,M2,U2), fact(['a1:E4_Period', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P9i_forms_part_of',M1),('a1:P9i_forms_part_of',M2),('a1:E4_Period',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P15i_influenced', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P15_was_influenced_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:parent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P14i_performed', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P14_carried_out_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P95_has_formed', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P95i_was_formed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P95_has_formed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P42i_was_assigned_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P94_has_created', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P131_is_identified_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E82_Actor_Appellation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:based_near', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a10:SpatialThing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P108i_was_produced_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P108_has_produced', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P112i_was_diminished_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P31i_was_modified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E46_Section_Definition', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P58i_defines_section', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P58_has_section_definition', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P58_has_section_definition', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P58i_defines_section', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:age', X, Y1],add,M1,U1), fact(['a3:age', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:age',M1),('a3:age',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P23i_surrendered_title_through', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P78_is_identified_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P7i_witnessed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:currentProject', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P119i_is_met_in_time_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:aimChatID', Y1, X],add,M1,U1), fact(['a3:aimChatID', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:aimChatID',M1),('a3:aimChatID',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P27_moved_from', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P27i_was_origin_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P37_assigned', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P116i_is_started_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P116_starts', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P116_starts', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P116i_is_started_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:sha1', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:agent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P12_occurred_in_the_presence_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P117i_includes', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P29i_received_custody_through', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P102_has_title', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P118i_is_overlapped_in_time_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P118_overlaps_in_time_with', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P118_overlaps_in_time_with', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P118i_is_overlapped_in_time_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P89_falls_within', X, Y],add,M1,U1), fact(['a1:P89_falls_within', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P89_falls_within',M1),('a1:P89_falls_within',M2)],M), fact(['a1:P89_falls_within', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P138i_has_representation', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, Y1],add,M1,U1), fact(['a2:father', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a2:father',M1),('a2:father',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:status', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P137_exemplifies', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P2_has_type', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:event', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:followingEvent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E49_Time_Appellation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:witness', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P48i_is_preferred_identifier_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P26i_was_destination_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:openid', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:organization', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P14i_performed', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P48i_is_preferred_identifier_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:plan', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P34i_was_assessed_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P140i_was_attributed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P131_is_identified_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P131i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P131i_identifies', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P131_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P148i_is_component_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P1_is_identified_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P129_is_about', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P115i_is_finished_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P42_assigned', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P42i_was_assigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P42i_was_assigned_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P42_assigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:employer', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P31_has_modified', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P87_is_identified_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P87i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P87i_identifies', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P87_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:spectator', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E28_Conceptual_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E68_Dissolution', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:birth', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:event', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', X, X2],add,M1,U1), fact(['a1:P135i_was_created_by', X, X1],add,M2,U2), fact(['a1:E55_Type', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P135i_was_created_by',M1),('a1:P135i_was_created_by',M2),('a1:E55_Type',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E9_Move', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P128i_is_carried_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P71i_is_listed_in', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P5_consists_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P78i_identifies', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E49_Time_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P65i_is_shown_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P128i_is_carried_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E8_Acquisition', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:followingEvent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:icqChatID', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:PhysicalMedium', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:MediaType', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P70i_is_documented_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P70_documents', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P70_documents', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P70i_is_documented_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E75_Conceptual_Object_Appellation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P83i_was_minimum_duration_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Group', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P126_employed', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P40i_was_observed_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:agent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P71_lists', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E32_Authority_Document', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P32i_was_technique_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E20_Biological_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P87i_identifies', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P130i_features_are_also_found_on', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P119i_is_met_in_time_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P119_meets_in_time_with', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P119_meets_in_time_with', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P119i_is_met_in_time_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:interest', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P146i_lost_member_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P30i_custody_transferred_through', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P104_is_subject_to', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E30_Right', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P110_augmented', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E79_Part_Addition', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:based_near', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a10:SpatialThing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E72_Legal_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67i_is_referred_to_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P112_diminished', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E80_Part_Removal', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:NameChange', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E37_Mark', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E73_Information_Object', X0, X1],add,M1,U1), fact(['a1:P67_refers_to', X1, X2],add,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E73_Information_Object',M1),('a1:P67_refers_to',M2),('a1:P_E73_Information_Object',M3)],M), fact(['a1:relatedInformationObjects', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:depicts', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Image', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:isPrimaryTopicOf', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P146i_lost_member_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P59i_is_located_on_or_within', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X1, X0],add,M1,U1), fact(['a1:P67_refers_to', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P67_refers_to',M1),('a1:P67_refers_to',M2)],M), fact(['a1:referredBySame', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P28i_surrendered_custody_through', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P87i_identifies', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P68i_use_foreseen_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P17i_motivated', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P22_transferred_title_to', X, Y1],add,M1,U1), fact(['a1:P22_transferred_title_to', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P22_transferred_title_to',M1),('a1:P22_transferred_title_to',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P86i_contains', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P25i_moved_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P40_observed_dimension', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P46_is_composed_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P46i_forms_part_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P46i_forms_part_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P46_is_composed_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P48_has_preferred_identifier', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P91_has_unit', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E58_Measurement_Unit', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P127_has_broader_term', X, Y],add,M1,U1), fact(['a1:P127_has_broader_term', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P127_has_broader_term',M1),('a1:P127_has_broader_term',M2)],M), fact(['a1:P127_has_broader_term', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:event', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E3_Condition_State', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:accountServiceHomepage', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P70i_is_documented_in', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:holdsAccount', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X0, X1],add,M1,U1), fact(['a1:P_E31_Document', X1, X2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P67_refers_to',M1),('a1:P_E31_Document',M2)],M), fact(['a1:refersToDocument', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P146_separated_from', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P45i_is_incorporated_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P88i_forms_part_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P24i_changed_ownership_through', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:jabberID', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:participant', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P4_has_time-span', X, X2],add,M1,U1), fact(['a1:P4_has_time-span', X, X1],add,M2,U2), fact(['a1:E2_Temporal_Entity', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P4_has_time-span',M1),('a1:P4_has_time-span',M2),('a1:E2_Temporal_Entity',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', X, X2],add,M1,U1), fact(['a1:P55_has_current_location', X, X1],add,M2,U2), fact(['a1:E19_Physical_Object', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P55_has_current_location',M1),('a1:P55_has_current_location',M2),('a1:E19_Physical_Object',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P120i_occurs_after', X, Y],add,M1,U1), fact(['a1:P120i_occurs_after', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P120i_occurs_after',M1),('a1:P120i_occurs_after',M2)],M), fact(['a1:P120i_occurs_after', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E13_Attribute_Assignment', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:knows', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:weblog', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:PositionChange', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P134_continued', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P134i_was_continued_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P134i_was_continued_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P134_continued', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P29_custody_received_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P43i_is_dimension_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P137_exemplifies', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P65i_is_shown_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P91i_is_unit_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P91_has_unit', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P91_has_unit', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P91i_is_unit_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P53_has_former_or_current_location', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P145i_left_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P145_separated', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P145_separated', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P145i_left_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P95_has_formed', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E66_Formation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P38i_was_deassigned_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyPrecedingEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:isPrimaryTopicOf', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:primaryTopic', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:primaryTopic', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:isPrimaryTopicOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P38_deassigned', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P17_was_motivated_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P4i_is_time-span_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E31_Document', X0, X1],add,M1,U1), fact(['a1:referToSame', X1, X2],add,M2,U2), fact(['a1:P_E31_Document', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E31_Document',M1),('a1:referToSame',M2),('a1:P_E31_Document',M3)],M), fact(['a1:relatedDocuments', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:Performance', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:GroupEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:PersonalProfileDocument', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P17_was_motivated_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P19_was_intended_use_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P19i_was_made_for', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P19i_was_made_for', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P19_was_intended_use_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P29i_received_custody_through', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P30_transferred_custody_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:skypeID', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P101_had_as_general_use', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P101i_was_use_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P101i_was_use_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P101_had_as_general_use', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P131_is_identified_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P46i_forms_part_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P76_has_contact_point', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:death', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:followingEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P58i_defines_section', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedDocuments', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:relatedDocuments', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P75_possesses', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E30_Right', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E5_Event', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P131i_identifies', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E82_Actor_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P35_has_identified', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E14_Condition_Assessment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P143_joined', X, X2],add,M1,U1), fact(['a1:P143_joined', X, X1],add,M2,U2), fact(['a1:E85_Joining', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P143_joined',M1),('a1:P143_joined',M2),('a1:E85_Joining',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P83_had_at_least_duration', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P83i_was_minimum_duration_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P83i_was_minimum_duration_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P83_had_at_least_duration', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P113i_was_removed_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P113_removed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P113_removed', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P113i_was_removed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P7_took_place_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E73_Information_Object', X0, X1],add,M1,U1), fact(['a1:referToSame', X1, X2],add,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E73_Information_Object',M1),('a1:referToSame',M2),('a1:P_E73_Information_Object',M3)],M), fact(['a1:relatedInformationObjects', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E31_Document', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E40_Legal_Body', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P106_is_composed_of', X, Y],add,M1,U1), fact(['a1:P106_is_composed_of', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P106_is_composed_of',M1),('a1:P106_is_composed_of',M2)],M), fact(['a1:P106_is_composed_of', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P62i_is_depicted_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P62_depicts', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P62_depicts', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P62i_is_depicted_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:birth', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E39_Actor', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E64_End_of_Existence', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P74_has_current_or_former_residence', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P110i_was_augmented_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P31i_was_modified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P52i_is_current_owner_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P105i_has_right_on', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P101_had_as_general_use', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13_destroyed', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P142_used_constituent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E45_Address', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E51_Contact_Point', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P43i_is_dimension_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P43_has_dimension', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P43_has_dimension', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P43i_is_dimension_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P21_had_general_purpose', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:relationship', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:AgentClass', X],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Class', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P31i_was_modified_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P31_has_modified', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P31_has_modified', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P31i_was_modified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:partner', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P98_brought_into_life', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98_brought_into_life', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P98i_was_born', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyFollowingEvent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P134_continued', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P35_has_identified', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P51i_is_former_or_current_owner_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a6:childOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P115_finishes', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:thumbnail', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Image', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P2_has_type', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P5i_forms_part_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P22i_acquired_title_through', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P22_transferred_title_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P22_transferred_title_to', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P22i_acquired_title_through', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P25_moved', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P127_has_broader_term', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P69_is_associated_with', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P69_is_associated_with', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P139_has_alternative_form', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P26_moved_to', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P123_resulted_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E81_Transformation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P92_brought_into_existence', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:FileFormat', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:MediaType', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P50_has_current_keeper', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:firstName', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P2_has_type', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E25_Man-Made_Feature', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E73_Information_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P96i_gave_birth', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P28_custody_surrendered_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P55i_currently_holds', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P87_is_identified_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P37_assigned', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:workInfoHomepage', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E22_Man-Made_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P109i_is_current_or_former_curator_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P15i_influenced', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', X, X2],add,M1,U1), fact(['a1:P73i_is_translation_of', X, X1],add,M2,U2), fact(['a1:E33_Linguistic_Object', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P73i_is_translation_of',M1),('a1:P73i_is_translation_of',M2),('a1:E33_Linguistic_Object',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E66_Formation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P129_is_about', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E81_Transformation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E31_Document', X0, X1],add,M1,U1), fact(['a1:refersToDocument', X1, X2],add,M2,U2), fact(['a1:refersToDocument', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E31_Document',M1),('a1:refersToDocument',M2),('a1:refersToDocument',M3)],M), fact(['a1:relatedDocuments', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P33i_was_used_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P33_used_specific_technique', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P33_used_specific_technique', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P33i_was_used_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P111_added', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P129i_is_subject_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P9i_forms_part_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P14_carried_out_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P126i_was_employed_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,M1,U1), fact(['a1:referredBySame', X1, X2],add,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E71_Man-Made_Thing',M1),('a1:referredBySame',M2),('a1:P_E71_Man-Made_Thing',M3)],M), fact(['a1:relatedManMadeThings', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P58i_defines_section', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E46_Section_Definition', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P14i_performed', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P139_has_alternative_form', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P75_possesses', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P75i_is_possessed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P75i_is_possessed_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P75_possesses', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:position', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P145i_left_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P10_falls_within', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E45_Address', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyFollowingEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:followingEvent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Employment', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:Location', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:LocationPeriodOrJurisdiction', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P33i_was_used_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:topic', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P12_occurred_in_the_presence_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P12i_was_present_at', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P117_occurs_during', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P76i_provides_access_to', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E51_Contact_Point', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P70_documents', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E31_Document', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:MediaType', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:MediaTypeOrExtent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:maker', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:primaryTopic', X, Y1],add,M1,U1), fact(['a3:primaryTopic', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:primaryTopic',M1),('a3:primaryTopic',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox_sha1sum', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P35i_was_identified_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E14_Condition_Assessment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P76_has_contact_point', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E51_Contact_Point', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E84_Information_Carrier', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E22_Man-Made_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P48_has_preferred_identifier', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P48i_is_preferred_identifier_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P48i_is_preferred_identifier_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P48_has_preferred_identifier', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:BasMitzvah', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P124i_was_transformed_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P124_transformed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P124_transformed', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P124i_was_transformed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P92_brought_into_existence', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13_destroyed', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P8_took_place_on_or_within', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P8i_witnessed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P8i_witnessed', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P8_took_place_on_or_within', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P76i_provides_access_to', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P76_has_contact_point', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P76_has_contact_point', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P76i_provides_access_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P106i_forms_part_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P56_bears_feature', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P46_is_composed_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P145i_left_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P53_has_former_or_current_location', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P25_moved', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyFollowingEvent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P96_by_mother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:msnChatID', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P146i_lost_member_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P146_separated_from', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P146_separated_from', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P146i_lost_member_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P40_observed_dimension', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P33_used_specific_technique', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41i_was_classified_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P140i_was_attributed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:schoolHomepage', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P52_has_current_owner', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P7_took_place_at', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P7i_witnessed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P7i_witnessed', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P7_took_place_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P95_has_formed', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Person', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P127i_has_narrower_term', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E6_Destruction', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P53i_is_former_or_current_location_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P134_continued', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:account', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P127_has_broader_term', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P93_took_out_of_existence', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P137_exemplifies', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P137i_is_exemplified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P137i_is_exemplified_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P137_exemplifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P22_transferred_title_to', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:accountName', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P30i_custody_transferred_through', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P86_falls_within', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P20_had_specific_purpose', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P20i_was_purpose_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P20i_was_purpose_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P20_had_specific_purpose', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P89i_contains', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P5i_forms_part_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P49i_is_former_or_current_keeper_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P128i_is_carried_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Imprisonment', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:tipjar', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:organization', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:concurrentEvent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:concurrentEvent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:yahooChatID', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P42_assigned', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P91_has_unit', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Retirement', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:tipjar', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P62_depicts', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:interval', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Interval', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:olb', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P117i_includes', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P88i_forms_part_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P135_created_type', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E83_Type_Creation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P59i_is_located_on_or_within', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Dismissal', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P96i_gave_birth', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E27_Site', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E26_Physical_Feature', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:principal', X, X2],add,M1,U1), fact(['a2:principal', X, X1],add,M2,U2), fact(['a2:IndividualEvent', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a2:principal',M1),('a2:principal',M2),('a2:IndividualEvent',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:msnChatID', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:homepage', Y1, X],add,M1,U1), fact(['a3:homepage', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:homepage',M1),('a3:homepage',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P1i_identifies', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P10_falls_within', X, Y],add,M1,U1), fact(['a1:P10_falls_within', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P10_falls_within',M1),('a1:P10_falls_within',M2)],M), fact(['a1:P10_falls_within', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P96_by_mother', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Enrolment', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P75_possesses', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P93i_was_taken_out_of_existence_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P100_was_death_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P126i_was_employed_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P9i_forms_part_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Person', X],add,M1,U1) ==> member(U,[U1]) | fact(['a10:SpatialThing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P92i_was_brought_into_existence_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P54i_is_current_permanent_location_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P51i_is_former_or_current_owner_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P115i_is_finished_by', X, Y],add,M1,U1), fact(['a1:P115i_is_finished_by', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P115i_is_finished_by',M1),('a1:P115i_is_finished_by',M2)],M), fact(['a1:P115i_is_finished_by', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P137i_is_exemplified_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P2i_is_type_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:concludingEvent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:thumbnail', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Image', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:parent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P44i_is_condition_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P144i_gained_member_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P118i_is_overlapped_in_time_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P129i_is_subject_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P20_had_specific_purpose', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P32i_was_technique_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P65_shows_visual_item', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P129i_is_subject_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P134i_was_continued_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:msnChatID', Y1, X],add,M1,U1), fact(['a3:msnChatID', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:msnChatID',M1),('a3:msnChatID',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P87_is_identified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Person', X],add,M1,U1), fact(['a3:Project', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:Person',M1),('a3:Project',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E33_Linguistic_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:geekcode', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:officiator', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P114_is_equal_in_time_to', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P114_is_equal_in_time_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:partner', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:spectator', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P28i_surrendered_custody_through', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P136i_supported_type_creation', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P72i_is_language_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E56_Language', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P96_by_mother', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P116_starts', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:img', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P100i_died_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P96i_gave_birth', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:familyName', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P148_has_component', X, Y],add,M1,U1), fact(['a1:P148_has_component', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P148_has_component',M1),('a1:P148_has_component',M2)],M), fact(['a1:P148_has_component', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P55i_currently_holds', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Event', X],add,M1,U1) ==> member(U,[U1]) | fact(['a11:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P97i_was_father_for', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P97_from_father', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P97_from_father', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P97i_was_father_for', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P26_moved_to', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E52_Time-Span', X],add,M1,U1), fact(['a1:E53_Place', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:E52_Time-Span',M1),('a1:E53_Place',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P89_falls_within', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E56_Language', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:spectator', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P40i_was_observed_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P40_observed_dimension', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P40_observed_dimension', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P40i_was_observed_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,M1,U1), fact(['a1:P67_refers_to', X1, X2],add,M2,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E71_Man-Made_Thing',M1),('a1:P67_refers_to',M2),('a1:P_E71_Man-Made_Thing',M3)],M), fact(['a1:relatedManMadeThings', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:Adoption', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P42i_was_assigned_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P95_has_formed', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P31i_was_modified_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P56i_is_found_on', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P46i_forms_part_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P117_occurs_during', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:msnChatID', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P89i_contains', X, Y],add,M1,U1), fact(['a1:P89i_contains', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P89i_contains',M1),('a1:P89i_contains',M2)],M), fact(['a1:P89i_contains', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E31_Document', X0, X1],add,M1,U1), fact(['a1:P67_refers_to', X1, X2],add,M2,U2), fact(['a1:P_E31_Document', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E31_Document',M1),('a1:P67_refers_to',M2),('a1:P_E31_Document',M3)],M), fact(['a1:relatedDocuments', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P137i_is_exemplified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P130_shows_features_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P130i_features_are_also_found_on', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P130_shows_features_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P52i_is_current_owner_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P46i_forms_part_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P19i_was_made_for', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E17_Type_Assignment', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E32_Authority_Document', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E31_Document', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P135_created_type', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P135_created_type', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P135i_was_created_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P120_occurs_before', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P120i_occurs_after', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P120i_occurs_after', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P120_occurs_before', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P107i_is_current_or_former_member_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:gender', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P19i_was_made_for', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P86_falls_within', X, Y],add,M1,U1), fact(['a1:P86_falls_within', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P86_falls_within',M1),('a1:P86_falls_within',M2)],M), fact(['a1:P86_falls_within', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P120_occurs_before', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E19_Physical_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P7i_witnessed', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P75i_is_possessed_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['rdfs:ContainerMembershipProperty', X],add,M1,U1) ==> member(U,[U1]) | fact(['rdf:Property', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P92i_was_brought_into_existence_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P113i_was_removed_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E80_Part_Removal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P103_was_intended_for', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:child', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:homepage', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:partner', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39i_was_measured_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P140i_was_attributed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E48_Place_Name', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P_E53_Place', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:schoolHomepage', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P34_concerned', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E14_Condition_Assessment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Redundancy', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P28_custody_surrendered_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P28i_surrendered_custody_through', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P28i_surrendered_custody_through', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P28_custody_surrendered_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', X, Y],add,M1,U1), fact(['a1:P27_moved_from', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P27_moved_from',M1),('a1:P27_moved_from',M2)],M), fact(['a1:P27_moved_from', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E80_Part_Removal', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P102i_is_title_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E35_Title', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P116i_is_started_by', X, Y],add,M1,U1), fact(['a1:P116i_is_started_by', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P116i_is_started_by',M1),('a1:P116i_is_started_by',M2)],M), fact(['a1:P116i_is_started_by', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E44_Place_Appellation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P54_has_current_permanent_location', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P38i_was_deassigned_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P38_deassigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P38_deassigned', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P38i_was_deassigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P97i_was_father_for', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P4_has_time-span', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Formation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:agent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P137_exemplifies', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P137i_is_exemplified_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P80_end_is_qualified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:knows', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Disbanding', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P148i_is_component_of', X, Y],add,M1,U1), fact(['a1:P148i_is_component_of', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P148i_is_component_of',M1),('a1:P148i_is_component_of',M2)],M), fact(['a1:P148i_is_component_of', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:yahooChatID', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:death', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:event', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P89_falls_within', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P115_finishes', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:death', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Death', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P35i_was_identified_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P111_added', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E79_Part_Addition', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P37i_was_assigned_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P42_assigned', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E17_Type_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E73_Information_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P110_augmented', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P31_has_modified', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P78i_identifies', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P91i_is_unit_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P146_separated_from', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E86_Leaving', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:position', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P86i_contains', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox_sha1sum', Y1, X],add,M1,U1), fact(['a3:mbox_sha1sum', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:mbox_sha1sum',M1),('a3:mbox_sha1sum',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E74_Group', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P37i_was_assigned_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:yahooChatID', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P127i_has_narrower_term', X, Y],add,M1,U1), fact(['a1:P127i_has_narrower_term', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P127i_has_narrower_term',M1),('a1:P127i_has_narrower_term',M2)],M), fact(['a1:P127i_has_narrower_term', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:member', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P21i_was_purpose_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E29_Design_or_Procedure', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Execution', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Death', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P71_lists', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P71i_is_listed_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P71i_is_listed_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P71_lists', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P84_had_at_most_duration', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P101i_was_use_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P142_used_constituent', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P142i_was_used_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P142i_was_used_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P142_used_constituent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:position', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P147i_was_curated_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E87_Curation_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P49_has_former_or_current_keeper', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P49i_is_former_or_current_keeper_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P38i_was_deassigned_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P145i_left_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E86_Leaving', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P91_has_unit', X, X2],add,M1,U1), fact(['a1:P91_has_unit', X, X1],add,M2,U2), fact(['a1:E54_Dimension', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P91_has_unit',M1),('a1:P91_has_unit',M2),('a1:E54_Dimension',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:relationship', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Relationship', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P75i_is_possessed_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E30_Right', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:principal', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:OnlineEcommerceAccount', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P2i_is_type_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E31_Document', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P_E31_Document', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:principal', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P144i_gained_member_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P74i_is_current_or_former_residence_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:holdsAccount', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P90_has_value', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:weblog', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41i_was_classified_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E17_Type_Assignment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P123_resulted_in', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P93_took_out_of_existence', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:concurrentEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P49i_is_former_or_current_keeper_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['rdfs:Datatype', X],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Class', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P111i_was_added_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, _],add,M1,U1), fact(['a2:mother', X, _],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a2:father',M1),('a2:mother',M2)],M), fact(['a3:Person', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P125i_was_type_of_object_used_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P145_separated', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P57_has_number_of_parts', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Investiture', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P147_curated', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E87_Curation_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P138i_has_representation', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67i_is_referred_to_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P50_has_current_keeper', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P50i_is_current_keeper_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P50i_is_current_keeper_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P50_has_current_keeper', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P138_represents', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73_has_translation', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P130_shows_features_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:concurrentEvent', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:PeriodOfTime', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:LocationPeriodOrJurisdiction', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P143i_was_joined_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P121_overlaps_with', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P34i_was_assessed_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P34_concerned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P34_concerned', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P34i_was_assessed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E12_Production', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P140i_was_attributed_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P117i_includes', X, Y],add,M1,U1), fact(['a1:P117i_includes', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P117i_includes',M1),('a1:P117i_includes',M2)],M), fact(['a1:P117i_includes', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P102i_is_title_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X0, X1],add,M1,U1), fact(['a1:P67_refers_to', X2, X1],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P67_refers_to',M1),('a1:P67_refers_to',M2)],M), fact(['a1:referToSame', X0, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E71_Man-Made_Thing', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P141_assigned', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P74_has_current_or_former_residence', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P84i_was_maximum_duration_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P84_had_at_most_duration', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P84_had_at_most_duration', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P84i_was_maximum_duration_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:weblog', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E77_Persistent_Item', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P104i_applies_to', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P104_is_subject_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P104_is_subject_to', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P104i_applies_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E87_Curation_Activity', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:isPrimaryTopicOf', Y1, X],add,M1,U1), fact(['a3:isPrimaryTopicOf', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:isPrimaryTopicOf',M1),('a3:isPrimaryTopicOf',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:Relationship', X],add,M1,U1) ==> member(U,[U1]) | fact(['a6:Relationship', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a6:Relationship', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Relationship', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:logo', Y1, X],add,M1,U1), fact(['a3:logo', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:logo',M1),('a3:logo',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P92_brought_into_existence', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E48_Place_Name', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P143i_was_joined_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E2_Temporal_Entity', X],add,M1,U1), fact(['a1:E77_Persistent_Item', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:E2_Temporal_Entity',M1),('a1:E77_Persistent_Item',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P54i_is_current_permanent_location_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P145_separated', X, X2],add,M1,U1), fact(['a1:P145_separated', X, X1],add,M2,U2), fact(['a1:E86_Leaving', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P145_separated',M1),('a1:P145_separated',M2),('a1:E86_Leaving',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Inauguration', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P125_used_object_of_type', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P25i_moved_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P72i_is_language_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P72_has_language', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P72_has_language', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P72i_is_language_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P101i_was_use_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P123i_resulted_from', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E66_Formation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P1i_identifies', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:SizeOrDuration', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:MediaTypeOrExtent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P92_brought_into_existence', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P92i_was_brought_into_existence_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:icqChatID', Y1, X],add,M1,U1), fact(['a3:icqChatID', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:icqChatID',M1),('a3:icqChatID',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:OnlineChatAccount', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P97_from_father', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P65i_is_shown_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P86i_contains', X, Y],add,M1,U1), fact(['a1:P86i_contains', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P86i_contains',M1),('a1:P86i_contains',M2)],M), fact(['a1:P86i_contains', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:Coronation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P148i_is_component_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P34i_was_assessed_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E14_Condition_Assessment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P49_has_former_or_current_keeper', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P43i_is_dimension_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P143i_was_joined_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E85_Joining', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P21_had_general_purpose', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P21i_was_purpose_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P21i_was_purpose_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P21_had_general_purpose', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P87i_identifies', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Funeral', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P11i_participated_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P11_had_participant', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P111_added', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P111i_was_added_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P111i_was_added_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P111_added', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E73_Information_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P_E73_Information_Object', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P113_removed', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E80_Part_Removal', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P142i_was_used_in', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P16i_was_used_for', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:page', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:topic', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:topic', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P94i_was_created_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P101_had_as_general_use', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:homepage', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:isPrimaryTopicOf', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P127i_has_narrower_term', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P25i_moved_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P25_moved', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P25_moved', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P25i_moved_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P3_has_note', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P38_deassigned', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E42_Identifier', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P148_has_component', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P122_borders_with', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P122_borders_with', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P59i_is_located_on_or_within', X, X2],add,M1,U1), fact(['a1:P59i_is_located_on_or_within', X, X1],add,M2,U2), fact(['a1:E53_Place', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P59i_is_located_on_or_within',M1),('a1:P59i_is_located_on_or_within',M2),('a1:E53_Place',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P26i_was_destination_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:accountServiceHomepage', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P68_foresees_use_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P68i_use_foreseen_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P68i_use_foreseen_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P68_foresees_use_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:eventInterval', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P128_carries', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E65_Creation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox_sha1sum', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:interval', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Relationship', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X, Y],add,M1,U1), fact(['a1:P67_refers_to', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P67_refers_to',M1),('a1:P67_refers_to',M2)],M), fact(['a1:P67_refers_to', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E12_Production', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P12i_was_present_at', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P48_has_preferred_identifier', X, X2],add,M1,U1), fact(['a1:P48_has_preferred_identifier', X, X1],add,M2,U2), fact(['a1:E1_CRM_Entity', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P48_has_preferred_identifier',M1),('a1:P48_has_preferred_identifier',M2),('a1:E1_CRM_Entity',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P148_has_component', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P12_occurred_in_the_presence_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P31i_was_modified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P94i_was_created_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P107_has_current_or_former_member', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P103i_was_intention_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P12i_was_present_at', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P42_assigned', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E17_Type_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P62i_is_depicted_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P4i_is_time-span_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P106i_forms_part_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E26_Physical_Feature', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyPrecedingEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:precedingEvent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Resignation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:BarMitzvah', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E2_Temporal_Entity', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P123i_resulted_from', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E54_Dimension', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P131i_identifies', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Baptism', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P122_borders_with', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P94_has_created', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P115_finishes', X, Y],add,M1,U1), fact(['a1:P115_finishes', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P115_finishes',M1),('a1:P115_finishes',M2)],M), fact(['a1:P115_finishes', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:openid', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P1i_identifies', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P1_is_identified_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P52_has_current_owner', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P102i_is_title_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P102_has_title', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P102_has_title', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P102i_is_title_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P59_has_section', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P79_beginning_is_qualified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:jabberID', Y1, X],add,M1,U1), fact(['a3:jabberID', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:jabberID',M1),('a3:jabberID',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P140_assigned_attribute_to', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P140i_was_attributed_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P140i_was_attributed_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P140_assigned_attribute_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98_brought_into_life', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P8_took_place_on_or_within', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P8_took_place_on_or_within', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E22_Man-Made_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P114_is_equal_in_time_to', X, Y],add,M1,U1), fact(['a1:P114_is_equal_in_time_to', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P114_is_equal_in_time_to',M1),('a1:P114_is_equal_in_time_to',M2)],M), fact(['a1:P114_is_equal_in_time_to', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E73_Information_Object', X0, X1],add,M1,U1), fact(['a1:referredBySame', X1, X2],add,M2,U2), fact(['a1:P_E73_Information_Object', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E73_Information_Object',M1),('a1:referredBySame',M2),('a1:P_E73_Information_Object',M3)],M), fact(['a1:relatedInformationObjects', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a2:Burial', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P140i_was_attributed_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E53_Place', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P_E53_Place', X, X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P23_transferred_title_from', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P23i_surrendered_title_through', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P23i_surrendered_title_through', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P23_transferred_title_from', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', X, Y],add,M1,U1), fact(['a1:P27i_was_origin_of', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P27i_was_origin_of',M1),('a1:P27i_was_origin_of',M2)],M), fact(['a1:P27i_was_origin_of', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P33i_was_used_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P74i_is_current_or_former_residence_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P74_has_current_or_former_residence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P74_has_current_or_former_residence', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P74i_is_current_or_former_residence_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E90_Symbolic_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P107_has_current_or_former_member', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P107i_is_current_or_former_member_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P107i_is_current_or_former_member_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P107_has_current_or_former_member', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P131i_identifies', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:keywords', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P87_is_identified_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P15i_influenced', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P109_has_current_or_former_curator', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P141i_was_assigned_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E16_Measurement', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P124_transformed', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P120i_occurs_after', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E53_Place', X0, X1],add,M1,U1), fact(['a1:P67_refers_to', X1, X2],add,M2,U2), fact(['a1:P_E53_Place', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E53_Place',M1),('a1:P67_refers_to',M2),('a1:P_E53_Place',M3)],M), fact(['a1:relatedPlaces', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a5:Agent', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Agent', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P62_depicts', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P65_shows_visual_item', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:initiatingEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P11i_participated_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P140_assigned_attribute_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P136i_supported_type_creation', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E83_Type_Creation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E55_Type', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:officiator', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedPlaces', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:relatedPlaces', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P147_curated', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P147i_was_curated_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P147i_was_curated_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P147_curated', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P53_has_former_or_current_location', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Birth', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:keywords', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a12:subject', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P5_consists_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:icqChatID', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P118i_is_overlapped_in_time_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P48_has_preferred_identifier', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P44i_is_condition_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P69_is_associated_with', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E11_Modification', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P93i_was_taken_out_of_existence_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P93_took_out_of_existence', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P109i_is_current_or_former_curator_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E78_Collection', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P76i_provides_access_to', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P94i_was_created_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E86_Leaving', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Document', X],add,M1,U1), fact(['a3:Project', X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:Document',M1),('a3:Project',M2)],M), fact(['owl:Nothing', X],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P20i_was_purpose_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Event', X],add,M1,U1) ==> member(U,[U1]) | fact(['a13:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:birthday', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P143_joined', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E85_Joining', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P115_finishes', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P115i_is_finished_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P115i_is_finished_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P115_finishes', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P25i_moved_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:witness', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E38_Image', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P73_has_translation', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P26i_was_destination_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P7i_witnessed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:weblog', Y1, X],add,M1,U1), fact(['a3:weblog', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:weblog',M1),('a3:weblog',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P17i_motivated', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P142_used_constituent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P125i_was_type_of_object_used_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P125_used_object_of_type', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P125_used_object_of_type', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:workplaceHomepage', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P134i_was_continued_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E89_Propositional_Object', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:skypeID', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:isPrimaryTopicOf', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P88_consists_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P88i_forms_part_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P88i_forms_part_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P88_consists_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:relationship', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:participant', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:relationship', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P21i_was_purpose_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P17_was_motivated_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P34_concerned', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P140_assigned_attribute_to', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P25_moved', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Accession', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:interest', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E58_Measurement_Unit', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P105i_has_right_on', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P105_right_held_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P105_right_held_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P105i_has_right_on', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Assassination', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Murder', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E12_Production', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E35_Title', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:witness', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:spectator', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E83_Type_Creation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E65_Creation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, Y1],add,M1,U1), fact(['a2:mother', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a2:mother',M1),('a2:mother',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P32i_was_technique_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P65_shows_visual_item', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P128_carries', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P69_is_associated_with', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P135_created_type', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P22_transferred_title_to', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P49_has_former_or_current_keeper', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P104i_applies_to', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E30_Right', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P86i_contains', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P86_falls_within', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P86_falls_within', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P86i_contains', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P11_had_participant', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P2i_is_type_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P2_has_type', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P2_has_type', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P2i_is_type_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:workplaceHomepage', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E52_Time-Span', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E6_Destruction', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P129_is_about', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P103i_was_intention_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P103_was_intended_for', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P103_was_intended_for', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P103i_was_intention_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:birthday', X, Y1],add,M1,U1), fact(['a3:birthday', X, Y2],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:birthday',M1),('a3:birthday',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E34_Inscription', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P21_had_general_purpose', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E69_Death', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E18_Physical_Thing', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E53_Place', X0, X1],add,M1,U1), fact(['a1:referToSame', X1, X2],add,M2,U2), fact(['a1:P_E53_Place', X2, X3],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P_E53_Place',M1),('a1:referToSame',M2),('a1:P_E53_Place',M3)],M), fact(['a1:relatedPlaces', X0, X3],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P143_joined', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P35_has_identified', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:employer', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P145_separated', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E86_Leaving', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', X, X2],add,M1,U1), fact(['a1:P98i_was_born', X, X1],add,M2,U2), fact(['a1:E21_Person', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P98i_was_born',M1),('a1:P98i_was_born',M2),('a1:E21_Person',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P114_is_equal_in_time_to', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P20i_was_purpose_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P38i_was_deassigned_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P83_had_at_least_duration', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:page', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:precedingEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P134i_was_continued_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E67_Birth', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P133_is_separated_from', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:pastProject', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:concludingEvent', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P19_was_intended_use_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E35_Title', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98_brought_into_life', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P68_foresees_use_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P33_used_specific_technique', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P16_used_specific_object', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:precedingEvent', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P17i_motivated', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E68_Dissolution', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P52i_is_current_owner_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P120_occurs_before', X, Y],add,M1,U1), fact(['a1:P120_occurs_before', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P120_occurs_before',M1),('a1:P120_occurs_before',M2)],M), fact(['a1:P120_occurs_before', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P89i_contains', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P89_falls_within', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P89_falls_within', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P89i_contains', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P121_overlaps_with', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P88_consists_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P129_is_about', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P129i_is_subject_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P129i_is_subject_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P129_is_about', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:state', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P50i_is_current_keeper_of', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:precedingEvent', X, Y],add,M1,U1), fact(['a2:precedingEvent', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a2:precedingEvent',M1),('a2:precedingEvent',M2)],M), fact(['a2:precedingEvent', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a3:member', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Group', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['rdfs:Class', X],add,M1,U1) ==> member(U,[U1]) | fact(['rdfs:Resource', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P4i_is_time-span_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P4_has_time-span', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P4_has_time-span', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P4i_is_time-span_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P105_right_held_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:aimChatID', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P122_borders_with', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:OnlineGamingAccount', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P26_moved_to', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P7_took_place_at', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P31_has_modified', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P83_had_at_least_duration', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:GroupEvent', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P86_falls_within', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:yahooChatID', Y1, X],add,M1,U1), fact(['a3:yahooChatID', Y2, X],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a3:yahooChatID',M1),('a3:yahooChatID',M2)],M), fact(['owl:sameAs', Y1, Y2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P106i_forms_part_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P106_is_composed_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P106_is_composed_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P106i_forms_part_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P40i_was_observed_in', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P133_is_separated_from', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P133_is_separated_from', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P130_shows_features_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Interval', X],add,M1,U1) ==> member(U,[U1]) | fact(['a14:ProperInterval', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P52i_is_current_owner_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P52_has_current_owner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P52_has_current_owner', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P52i_is_current_owner_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P100i_died_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E69_Death', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:maker', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:made', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:made', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:maker', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P124_transformed', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E81_Transformation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E82_Actor_Appellation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P32_used_general_technique', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P123i_resulted_from', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P123_resulted_in', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P123_resulted_in', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P123i_resulted_from', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P10i_contains', X, Y],add,M1,U1), fact(['a1:P10i_contains', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P10i_contains',M1),('a1:P10i_contains',M2)],M), fact(['a1:P10i_contains', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P51i_is_former_or_current_owner_of', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P51_has_former_or_current_owner', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P142i_was_used_in', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Death', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P98_brought_into_life', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P93i_was_taken_out_of_existence_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P39i_was_measured_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P39i_was_measured_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P39_measured', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P116i_is_started_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E41_Appellation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P106i_forms_part_of', X, Y],add,M1,U1), fact(['a1:P106i_forms_part_of', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P106i_forms_part_of',M1),('a1:P106i_forms_part_of',M2)],M), fact(['a1:P106i_forms_part_of', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P50_has_current_keeper', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P9_consists_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P144_joined_with', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:publications', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P46_is_composed_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P59_has_section', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E36_Visual_Item', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P112i_was_diminished_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E80_Part_Removal', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P11i_participated_in', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P78_is_identified_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P34_concerned', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P112i_was_diminished_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P136i_supported_type_creation', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P144i_gained_member_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P144_joined_with', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P144_joined_with', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P144i_gained_member_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Cremation', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P119_meets_in_time_with', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Marriage', X],add,M1,U1) ==> member(U,[U1]) | fact(['a7:WeddingEvent_Generic', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a7:WeddingEvent_Generic', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Marriage', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:Image', X],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P143_joined', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P143i_was_joined_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P143i_was_joined_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P143_joined', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P24i_changed_ownership_through', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P115i_is_finished_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P103_was_intended_for', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P53i_is_former_or_current_location_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P128_carries', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a5:LicenseDocument', X],add,M1,U1) ==> member(U,[U1]) | fact(['a5:RightsStatement', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P68_foresees_use_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P89i_contains', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P20_had_specific_purpose', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P46_is_composed_of', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P7i_witnessed', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Naturalization', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P23i_surrendered_title_through', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E30_Right', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P9_consists_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P106_is_composed_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:tipjar', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:account', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E70_Thing', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P22i_acquired_title_through', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P105_right_held_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a3:icqChatID', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:E78_Collection', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', X, X2],add,M1,U1), fact(['a1:P13i_was_destroyed_by', X, X1],add,M2,U2), fact(['a1:E18_Physical_Thing', X],add,M3,U3) ==> member(U,[U1,U2,U3]) | check_neg_mark([('a1:P13i_was_destroyed_by',M1),('a1:P13i_was_destroyed_by',M2),('a1:E18_Physical_Thing',M3)],M), fact(['owl:sameAs', X1, X2],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:P136_was_based_on', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P16_used_specific_object', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P16i_was_used_for', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P88_consists_of', X, Y],add,M1,U1), fact(['a1:P88_consists_of', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P88_consists_of',M1),('a1:P88_consists_of',M2)],M), fact(['a1:P88_consists_of', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a15:Performance', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Performance', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Performance', X],add,M1,U1) ==> member(U,[U1]) | fact(['a15:Performance', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P54_has_current_permanent_location', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P88i_forms_part_of', X, Y],add,M1,U1), fact(['a1:P88i_forms_part_of', Y, Z],add,M2,U2) ==> member(U,[U1,U2]) | check_neg_mark([('a1:P88i_forms_part_of',M1),('a1:P88i_forms_part_of',M2)],M), fact(['a1:P88i_forms_part_of', X, Z],add,M,U), applied_rules(1,ins).
phase(5), fact(['a1:E25_Man-Made_Feature', X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E26_Physical_Feature', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P94_has_created', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E65_Creation', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P128_carries', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P128i_is_carried_by', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P128i_is_carried_by', Y, X],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P128_carries', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:Emigration', X],add,M1,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P112_diminished', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P31_has_modified', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P33i_was_used_by', X, Y],add,M1,U1) ==> member(U,[U1]) | fact(['a1:P16i_was_used_for', X, Y],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P83i_was_minimum_duration_of', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:organization', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P113i_was_removed_by', X, _],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a2:child', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,M1,U), applied_rules(1,ins).
phase(5), fact(['a1:P78_is_identified_by', _, X1],add,M1,U1) ==> member(U,[U1]) | fact(['a1:E49_Time_Appellation', X1],add,M1,U), applied_rules(1,ins).

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
explicit('a1:E34_Inscription').
explicit('a3:aimChatID').
explicit('a3:homepage').
explicit('rdfs:Container').
explicit('a3:publications').
explicit('a2:death').
explicit('a2:Divorce').
explicit('a2:Graduation').
explicit('a2:birth').
explicit('a2:Annulment').
explicit('a2:Promotion').
explicit('a2:Ordination').
explicit('a5:Jurisdiction').
explicit('a2:principal').
explicit('a3:myersBriggs').
explicit('a2:Demotion').
explicit('a3:openid').
explicit('a3:img').
explicit('a3:Organization').
explicit('a2:state').
explicit('a2:father').
explicit('a1:E47_Spatial_Coordinates').
explicit('a3:workInfoHomepage').
explicit('a3:surname').
explicit('a2:employer').
explicit('a2:officiator').
explicit('a3:age').
explicit('a3:skypeID').
explicit('a1:P82_at_some_time_within').
explicit('a3:gender').
explicit('a3:jabberID').
explicit('a3:lastName').
explicit('a3:mbox').
explicit('a3:focus').
explicit('a3:topic_interest').
explicit('a2:eventInterval').
explicit('a2:immediatelyPrecedingEvent').
explicit('a2:immediatelyFollowingEvent').
explicit('a2:child').
explicit('a1:E50_Date').
explicit('a1:P81_ongoing_throughout').
explicit('a3:family_name').
explicit('a2:parent').
explicit('a2:initiatingEvent').
explicit('a2:mother').
explicit('a3:based_near').
explicit('a3:currentProject').
explicit('a3:sha1').
explicit('a3:status').
explicit('a2:witness').
explicit('a2:organization').
explicit('a3:plan').
explicit('a3:icqChatID').
explicit('a5:PhysicalMedium').
explicit('a1:E75_Conceptual_Object_Appellation').
explicit('a3:interest').
explicit('a2:NameChange').
explicit('a3:accountServiceHomepage').
explicit('a3:holdsAccount').
explicit('a3:knows').
explicit('a3:weblog').
explicit('a3:PersonalProfileDocument').
explicit('a1:E40_Legal_Body').
explicit('a1:E45_Address').
explicit('a5:AgentClass').
explicit('a2:partner').
explicit('a3:thumbnail').
explicit('a1:P139_has_alternative_form').
explicit('a5:FileFormat').
explicit('a3:firstName').
explicit('a1:E25_Man-Made_Feature').
explicit('a2:position').
explicit('a2:Employment').
explicit('a5:Location').
explicit('a3:mbox_sha1sum').
explicit('a1:E84_Information_Carrier').
explicit('a2:BasMitzvah').
explicit('a3:msnChatID').
explicit('a3:schoolHomepage').
explicit('a3:account').
explicit('a3:accountName').
explicit('a2:Imprisonment').
explicit('a3:tipjar').
explicit('a3:yahooChatID').
explicit('a2:Retirement').
explicit('a2:interval').
explicit('a2:olb').
explicit('a2:Dismissal').
explicit('a1:E27_Site').
explicit('a2:Enrolment').
explicit('a2:concludingEvent').
explicit('a3:Project').
explicit('a3:geekcode').
explicit('a3:familyName').
explicit('a2:Adoption').
explicit('rdfs:ContainerMembershipProperty').
explicit('a1:E48_Place_Name').
explicit('a2:Redundancy').
explicit('a2:Formation').
explicit('a1:P80_end_is_qualified_by').
explicit('a2:Disbanding').
explicit('a3:member').
explicit('a2:Execution').
explicit('a3:OnlineEcommerceAccount').
explicit('a1:P90_has_value').
explicit('rdfs:Datatype').
explicit('a1:P57_has_number_of_parts').
explicit('a2:Investiture').
explicit('a5:PeriodOfTime').
explicit('a3:logo').
explicit('a2:Inauguration').
explicit('a5:SizeOrDuration').
explicit('a3:OnlineChatAccount').
explicit('a2:Coronation').
explicit('a2:Funeral').
explicit('a1:P3_has_note').
explicit('a2:Resignation').
explicit('a2:BarMitzvah').
explicit('a2:Baptism').
explicit('a1:P79_beginning_is_qualified_by').
explicit('a2:Burial').
explicit('a2:keywords').
explicit('a3:birthday').
explicit('a1:E38_Image').
explicit('a3:workplaceHomepage').
explicit('a2:Accession').
explicit('a2:Assassination').
explicit('a3:pastProject').
explicit('a3:OnlineGamingAccount').
explicit('a2:Cremation').
explicit('a5:LicenseDocument').
explicit('a2:Naturalization').
explicit('a2:Emigration').
