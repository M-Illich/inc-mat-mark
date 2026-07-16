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
phase(1), fact(['a1:P22i_acquired_title_through', _, X1],O1,_) \ fact(['a1:E8_Acquisition', X1],add,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P24_transferred_title_of', X, _],O1,_) \ fact(['a1:E8_Acquisition', X],add,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P110i_was_augmented_by', _, X1],O1,_) \ fact(['a1:E79_Part_Addition', X1],add,U) <=> member(del,[O1]) | fact(['a1:E79_Part_Addition', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', X, X2],O1,_), fact(['a1:P41_classified', X, X1],O2,_), fact(['a1:E17_Type_Assignment', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P33_used_specific_technique', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P116_starts', X, Y],O1,_), fact(['a1:P116_starts', Y, Z],O2,_) \ fact(['a1:P116_starts', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P116_starts', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P124i_was_transformed_by', _, X1],O1,_) \ fact(['a1:E81_Transformation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E81_Transformation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P104_is_subject_to', X, _],O1,_) \ fact(['a1:E72_Legal_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P114_is_equal_in_time_to', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P127_has_broader_term', Y, X],O1,_) \ fact(['a1:P127i_has_narrower_term', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P127i_has_narrower_term', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P127i_has_narrower_term', Y, X],O1,_) \ fact(['a1:P127_has_broader_term', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P127_has_broader_term', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:followingEvent', X, Y],O1,_), fact(['a2:followingEvent', Y, Z],O2,_) \ fact(['a2:followingEvent', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a2:followingEvent', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:E34_Inscription', X],O1,_) \ fact(['a1:E37_Mark', X],add,U) <=> member(del,[O1]) | fact(['a1:E37_Mark', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P94i_was_created_by', _, X1],O1,_) \ fact(['a1:E65_Creation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E65_Creation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:aimChatID', _, X1],O1,_) \ fact(['rdfs:Literal', X1],add,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E7_Activity', X],O1,_) \ fact(['a1:E5_Event', X],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:depiction', _, X1],O1,_) \ fact(['a3:Image', X1],add,U) <=> member(del,[O1]) | fact(['a3:Image', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P23_transferred_title_from', X, _],O1,_) \ fact(['a1:E8_Acquisition', X],add,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Murder', X],O1,_) \ fact(['a2:Death', X],add,U) <=> member(del,[O1]) | fact(['a2:Death', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E14_Condition_Assessment', X],O1,_) \ fact(['a1:E13_Attribute_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', X, Y],O1,_) \ fact(['a1:P31_has_modified', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', X, Y],O1,_) \ fact(['a1:P15i_influenced', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P123i_resulted_from', _, X1],O1,_) \ fact(['a1:E81_Transformation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E81_Transformation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:homepage', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P96_by_mother', Y, X],O1,_) \ fact(['a1:P96i_gave_birth', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P96i_gave_birth', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P96i_gave_birth', Y, X],O1,_) \ fact(['a1:P96_by_mother', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P96_by_mother', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P100_was_death_of', X, _],O1,_) \ fact(['a1:E69_Death', X],add,U) <=> member(del,[O1]) | fact(['a1:E69_Death', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41i_was_classified_by', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P71i_is_listed_in', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41i_was_classified_by', Y, X],O1,_) \ fact(['a1:P41_classified', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P41_classified', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', Y, X],O1,_) \ fact(['a1:P41i_was_classified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P41i_was_classified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P14_carried_out_by', X, Y],O1,_) \ fact(['a1:P11_had_participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P93_took_out_of_existence', X, Y],O1,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P54_has_current_permanent_location', X, X2],O1,_), fact(['a1:P54_has_current_permanent_location', X, X1],O2,_), fact(['a1:E19_Physical_Object', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P146_separated_from', X, Y],O1,_) \ fact(['a1:P11_had_participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P17_was_motivated_by', Y, X],O1,_) \ fact(['a1:P17i_motivated', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P17i_motivated', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P17i_motivated', Y, X],O1,_) \ fact(['a1:P17_was_motivated_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P17_was_motivated_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39i_was_measured_by', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P113_removed', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73_has_translation', Y, X],O1,_) \ fact(['a1:P73i_is_translation_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P73i_is_translation_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', Y, X],O1,_) \ fact(['a1:P73_has_translation', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P73_has_translation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P2i_is_type_of', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P141i_was_assigned_by', _, X1],O1,_) \ fact(['a1:E13_Attribute_Assignment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P102_has_title', X, Y],O1,_) \ fact(['a1:P1_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P38_deassigned', _, X1],O1,_) \ fact(['a1:E42_Identifier', X1],add,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P54_has_current_permanent_location', Y, X],O1,_) \ fact(['a1:P54i_is_current_permanent_location_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P54i_is_current_permanent_location_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P54i_is_current_permanent_location_of', Y, X],O1,_) \ fact(['a1:P54_has_current_permanent_location', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P54_has_current_permanent_location', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E21_Person', X],O1,_) \ fact(['a1:E20_Biological_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E20_Biological_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['rdfs:Container', X],O1,_) \ fact(['rdfs:Resource', X],add,U) <=> member(del,[O1]) | fact(['rdfs:Resource', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:publications', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:relatedInformationObjects', Y, X],O1,_) \ fact(['a1:relatedInformationObjects', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:relatedInformationObjects', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P126_employed', X, _],O1,_) \ fact(['a1:E11_Modification', X],add,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:death', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:Divorce', X],O1,_) \ fact(['a2:GroupEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:GroupEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', X, _],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P136_was_based_on', X, _],O1,_) \ fact(['a1:E83_Type_Creation', X],add,U) <=> member(del,[O1]) | fact(['a1:E83_Type_Creation', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Graduation', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P29i_received_custody_through', Y, X],O1,_) \ fact(['a1:P29_custody_received_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P29_custody_received_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P29_custody_received_by', Y, X],O1,_) \ fact(['a1:P29i_received_custody_through', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P29i_received_custody_through', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P10_falls_within', Y, X],O1,_) \ fact(['a1:P10i_contains', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P10i_contains', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P10i_contains', Y, X],O1,_) \ fact(['a1:P10_falls_within', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P10_falls_within', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P142_used_constituent', X, Y],O1,_) \ fact(['a1:P16_used_specific_object', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P147i_was_curated_by', X, _],O1,_) \ fact(['a1:E78_Collection', X],add,U) <=> member(del,[O1]) | fact(['a1:E78_Collection', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E53_Place', X],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P72i_is_language_of', _, X1],O1,_) \ fact(['a1:E33_Linguistic_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P70_documents', X, Y],O1,_) \ fact(['a1:P67_refers_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P124_transformed', X, Y],O1,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:Person', X],O1,_) \ fact(['a4:Person', X],add,U) <=> member(del,[O1]) | fact(['a4:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E24_Physical_Man-Made_Thing', X],O1,_) \ fact(['a1:E71_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P148i_is_component_of', Y, X],O1,_) \ fact(['a1:P148_has_component', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P148_has_component', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P148_has_component', Y, X],O1,_) \ fact(['a1:P148i_is_component_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P148i_is_component_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P15_was_influenced_by', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P107_has_current_or_former_member', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:made', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P30_transferred_custody_of', Y, X],O1,_) \ fact(['a1:P30i_custody_transferred_through', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P30i_custody_transferred_through', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P30i_custody_transferred_through', Y, X],O1,_) \ fact(['a1:P30_transferred_custody_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P30_transferred_custody_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P125_used_object_of_type', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:birth', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E65_Creation', X],O1,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E81_Transformation', X],O1,_) \ fact(['a1:E64_End_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P24i_changed_ownership_through', Y, X],O1,_) \ fact(['a1:P24_transferred_title_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P24_transferred_title_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P24_transferred_title_of', Y, X],O1,_) \ fact(['a1:P24i_changed_ownership_through', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P24i_changed_ownership_through', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:Annulment', X],O1,_) \ fact(['a2:GroupEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:GroupEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Promotion', X],O1,_) \ fact(['a2:PositionChange', X],add,U) <=> member(del,[O1]) | fact(['a2:PositionChange', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P31_has_modified', X, Y],O1,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:Ordination', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P130_shows_features_of', _, X1],O1,_) \ fact(['a1:E70_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P118_overlaps_in_time_with', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P144i_gained_member_by', _, X1],O1,_) \ fact(['a1:E85_Joining', X1],add,U) <=> member(del,[O1]) | fact(['a1:E85_Joining', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P124i_was_transformed_by', X, Y],O1,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P15_was_influenced_by', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E79_Part_Addition', X],O1,_), fact(['a1:E80_Part_Removal', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135_created_type', X, Y],O1,_) \ fact(['a1:P94_has_created', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P94_has_created', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P7_took_place_at', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a5:Jurisdiction', X],O1,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],add,U) <=> member(del,[O1]) | fact(['a5:LocationPeriodOrJurisdiction', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P56i_is_found_on', X, _],O1,_) \ fact(['a1:E26_Physical_Feature', X],add,U) <=> member(del,[O1]) | fact(['a1:E26_Physical_Feature', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P1_is_identified_by', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P126i_was_employed_in', Y, X],O1,_) \ fact(['a1:P126_employed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P126_employed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P126_employed', Y, X],O1,_) \ fact(['a1:P126i_was_employed_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P126i_was_employed_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:principal', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:myersBriggs', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Demotion', X],O1,_) \ fact(['a2:PositionChange', X],add,U) <=> member(del,[O1]) | fact(['a2:PositionChange', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:relationship', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P112_diminished', Y, X],O1,_) \ fact(['a1:P112i_was_diminished_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P112i_was_diminished_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P112i_was_diminished_by', Y, X],O1,_) \ fact(['a1:P112_diminished', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P112_diminished', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:openid', X, Y],O1,_) \ fact(['a3:isPrimaryTopicOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:isPrimaryTopicOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P141_assigned', Y, X],O1,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P141i_was_assigned_by', Y, X],O1,_) \ fact(['a1:P141_assigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P44_has_condition', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P45_consists_of', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P50i_is_current_keeper_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P26_moved_to', Y, X],O1,_) \ fact(['a1:P26i_was_destination_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P26i_was_destination_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P26i_was_destination_of', Y, X],O1,_) \ fact(['a1:P26_moved_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P26_moved_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:img', X, Y],O1,_) \ fact(['a3:depiction', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:depiction', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P24_transferred_title_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P133_is_separated_from', X, _],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P94_has_created', Y, X],O1,_) \ fact(['a1:P94i_was_created_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P94i_was_created_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P94i_was_created_by', Y, X],O1,_) \ fact(['a1:P94_has_created', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P94_has_created', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67i_is_referred_to_by', _, X1],O1,_) \ fact(['a1:E89_Propositional_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P9_consists_of', Y, X],O1,_) \ fact(['a1:P9i_forms_part_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P9i_forms_part_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P9i_forms_part_of', Y, X],O1,_) \ fact(['a1:P9_consists_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P9_consists_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P51_has_former_or_current_owner', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P68i_use_foreseen_by', X, _],O1,_) \ fact(['a1:E57_Material', X],add,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:IndividualEvent', X],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P138i_has_representation', Y, X],O1,_) \ fact(['a1:P138_represents', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P138_represents', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P138_represents', Y, X],O1,_) \ fact(['a1:P138i_has_representation', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P138i_has_representation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P51_has_former_or_current_owner', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:Organization', X],O1,_), fact(['a3:Person', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:state', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, Y],O1,_) \ fact(['a6:childOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a6:childOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55i_currently_holds', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P19_was_intended_use_of', _, X1],O1,_) \ fact(['a1:E71_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E47_Spatial_Coordinates', X],O1,_) \ fact(['a1:E44_Place_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:workInfoHomepage', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:depicts', Y, X],O1,_) \ fact(['a3:depiction', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:depiction', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:depiction', Y, X],O1,_) \ fact(['a3:depicts', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:depicts', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['rdfs:Literal', X],O1,_) \ fact(['rdfs:Resource', X],add,U) <=> member(del,[O1]) | fact(['rdfs:Resource', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P52_has_current_owner', X, Y],O1,_) \ fact(['a1:P105_right_held_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P105_right_held_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:concurrentEvent', _, X1],O1,_) \ fact(['a2:Event', X1],add,U) <=> member(del,[O1]) | fact(['a2:Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P58_has_section_definition', _, X1],O1,_) \ fact(['a1:E46_Section_Definition', X1],add,U) <=> member(del,[O1]) | fact(['a1:E46_Section_Definition', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', X, _],O1,_) \ fact(['a1:E21_Person', X],add,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:surname', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P56i_is_found_on', _, X1],O1,_) \ fact(['a1:E19_Physical_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P144_joined_with', X, _],O1,_) \ fact(['a1:E85_Joining', X],add,U) <=> member(del,[O1]) | fact(['a1:E85_Joining', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P130i_features_are_also_found_on', X, _],O1,_) \ fact(['a1:E70_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:event', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P43_has_dimension', X, _],O1,_) \ fact(['a1:E70_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P56_bears_feature', Y, X],O1,_) \ fact(['a1:P56i_is_found_on', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P56i_is_found_on', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P56i_is_found_on', Y, X],O1,_) \ fact(['a1:P56_bears_feature', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P56_bears_feature', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P83_had_at_least_duration', X, X2],O1,_), fact(['a1:P83_had_at_least_duration', X, X1],O2,_), fact(['a1:E52_Time-Span', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a2:participant', X, _],O1,_) \ fact(['a2:Relationship', X],add,U) <=> member(del,[O1]) | fact(['a2:Relationship', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P140_assigned_attribute_to', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P4_has_time-span', _, X1],O1,_) \ fact(['a1:E52_Time-Span', X1],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13_destroyed', Y, X],O1,_) \ fact(['a1:P13i_was_destroyed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P13i_was_destroyed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', Y, X],O1,_) \ fact(['a1:P13_destroyed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P13_destroyed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P107i_is_current_or_former_member_of', _, X1],O1,_) \ fact(['a1:E74_Group', X1],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E12_Production', X],O1,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:employer', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E15_Identifier_Assignment', X],O1,_) \ fact(['a1:E13_Attribute_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P117_occurs_during', X, Y],O1,_), fact(['a1:P117_occurs_during', Y, Z],O2,_) \ fact(['a1:P117_occurs_during', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P117_occurs_during', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:E63_Beginning_of_Existence', X],O1,_) \ fact(['a1:E5_Event', X],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P117i_includes', Y, X],O1,_) \ fact(['a1:P117_occurs_during', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P117_occurs_during', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P117_occurs_during', Y, X],O1,_) \ fact(['a1:P117i_includes', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P117i_includes', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P10i_contains', X, _],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P120i_occurs_after', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P28_custody_surrendered_by', X, Y],O1,_) \ fact(['a1:P14_carried_out_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P84i_was_maximum_duration_of', _, X1],O1,_) \ fact(['a1:E52_Time-Span', X1],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P37i_was_assigned_by', _, X1],O1,_) \ fact(['a1:E15_Identifier_Assignment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', X, X2],O1,_), fact(['a1:P39_measured', X, X1],O2,_), fact(['a1:E16_Measurement', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P147_curated', _, X1],O1,_) \ fact(['a1:E78_Collection', X1],add,U) <=> member(del,[O1]) | fact(['a1:E78_Collection', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', _, X1],O1,_) \ fact(['a1:E68_Dissolution', X1],add,U) <=> member(del,[O1]) | fact(['a1:E68_Dissolution', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P65i_is_shown_by', Y, X],O1,_) \ fact(['a1:P65_shows_visual_item', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P65_shows_visual_item', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P65_shows_visual_item', Y, X],O1,_) \ fact(['a1:P65i_is_shown_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P65i_is_shown_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P56_bears_feature', X, _],O1,_) \ fact(['a1:E19_Physical_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E90_Symbolic_Object', X],O1,_) \ fact(['a1:E72_Legal_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P120_occurs_before', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E24_Physical_Man-Made_Thing', X],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E85_Joining', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P58_has_section_definition', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P146i_lost_member_by', _, X1],O1,_) \ fact(['a1:E86_Leaving', X1],add,U) <=> member(del,[O1]) | fact(['a1:E86_Leaving', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P8i_witnessed', _, X1],O1,_) \ fact(['a1:E4_Period', X1],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P37_assigned', X, _],O1,_) \ fact(['a1:E15_Identifier_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P118_overlaps_in_time_with', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E4_Period', X],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Event', X],O1,_) \ fact(['a7:Event', X],add,U) <=> member(del,[O1]) | fact(['a7:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:officiator', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P62i_is_depicted_by', _, X1],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P72_has_language', _, X1],O1,_) \ fact(['a1:E56_Language', X1],add,U) <=> member(del,[O1]) | fact(['a1:E56_Language', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P138_represents', X, Y],O1,_) \ fact(['a1:P67_refers_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P70i_is_documented_in', _, X1],O1,_) \ fact(['a1:E31_Document', X1],add,U) <=> member(del,[O1]) | fact(['a1:E31_Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P32_used_general_technique', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:aimChatID', X, Y],O1,_) \ fact(['a3:nick', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P105i_has_right_on', _, X1],O1,_) \ fact(['a1:E72_Legal_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:age', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P100_was_death_of', Y, X],O1,_) \ fact(['a1:P100i_died_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P100i_died_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P100i_died_in', Y, X],O1,_) \ fact(['a1:P100_was_death_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P100_was_death_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:skypeID', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:participant', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P11_had_participant', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:father', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P82_at_some_time_within', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P31i_was_modified_by', _, X1],O1,_) \ fact(['a1:E11_Modification', X1],add,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:gender', X, Y1],O1,_), fact(['a3:gender', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:relatedPlaces', X, Y],O1,_), fact(['a1:relatedPlaces', Y, Z],O2,_) \ fact(['a1:relatedPlaces', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:relatedPlaces', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P141_assigned', X, _],O1,_) \ fact(['a1:E13_Attribute_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:Document', X],O1,_), fact(['a3:Organization', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P72_has_language', X, _],O1,_) \ fact(['a1:E33_Linguistic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P105i_has_right_on', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P97_from_father', X, _],O1,_) \ fact(['a1:E67_Birth', X],add,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P110i_was_augmented_by', X, _],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P136_was_based_on', Y, X],O1,_) \ fact(['a1:P136i_supported_type_creation', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P136i_supported_type_creation', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P136i_supported_type_creation', Y, X],O1,_) \ fact(['a1:P136_was_based_on', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P136_was_based_on', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P22i_acquired_title_through', Y1, X],O1,_), fact(['a1:P22i_acquired_title_through', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P100_was_death_of', X, Y],O1,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P45_consists_of', Y, X],O1,_) \ fact(['a1:P45i_is_incorporated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P45i_is_incorporated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P45i_is_incorporated_in', Y, X],O1,_) \ fact(['a1:P45_consists_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P45_consists_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:jabberID', _, X1],O1,_) \ fact(['rdfs:Literal', X1],add,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P78i_identifies', _, X1],O1,_) \ fact(['a1:E52_Time-Span', X1],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:primaryTopic', X, _],O1,_) \ fact(['a3:Document', X],add,U) <=> member(del,[O1]) | fact(['a3:Document', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P53_has_former_or_current_location', Y, X],O1,_) \ fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P53i_is_former_or_current_location_of', Y, X],O1,_) \ fact(['a1:P53_has_former_or_current_location', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P53_has_former_or_current_location', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P37_assigned', Y, X],O1,_) \ fact(['a1:P37i_was_assigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P37i_was_assigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P37i_was_assigned_by', Y, X],O1,_) \ fact(['a1:P37_assigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P37_assigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:lastName', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P84i_was_maximum_duration_of', X, _],O1,_) \ fact(['a1:E54_Dimension', X],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P32_used_general_technique', X, Y],O1,_) \ fact(['a1:P125_used_object_of_type', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P125_used_object_of_type', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P32_used_general_technique', Y, X],O1,_) \ fact(['a1:P32i_was_technique_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P32i_was_technique_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P32i_was_technique_of', Y, X],O1,_) \ fact(['a1:P32_used_general_technique', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P32_used_general_technique', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P59i_is_located_on_or_within', Y, X],O1,_) \ fact(['a1:P59_has_section', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P59_has_section', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P59_has_section', Y, X],O1,_) \ fact(['a1:P59i_is_located_on_or_within', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P59i_is_located_on_or_within', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:mbox', Y1, X],O1,_), fact(['a3:mbox', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a2:Marriage', X],O1,_) \ fact(['a2:GroupEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:GroupEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E79_Part_Addition', X],O1,_) \ fact(['a1:E11_Modification', X],add,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P35_has_identified', Y, X],O1,_) \ fact(['a1:P35i_was_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P35i_was_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P35i_was_identified_by', Y, X],O1,_) \ fact(['a1:P35_has_identified', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P35_has_identified', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:focus', X, _],O1,_) \ fact(['a8:Concept', X],add,U) <=> member(del,[O1]) | fact(['a8:Concept', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:img', _, X1],O1,_) \ fact(['a3:Image', X1],add,U) <=> member(del,[O1]) | fact(['a3:Image', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:Organization', X],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:topic_interest', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:eventInterval', _, X1],O1,_) \ fact(['a2:Interval', X1],add,U) <=> member(del,[O1]) | fact(['a2:Interval', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P116i_is_started_by', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', X, Y],O1,_) \ fact(['a1:P31i_was_modified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:birth', _, X1],O1,_) \ fact(['a2:Birth', X1],add,U) <=> member(del,[O1]) | fact(['a2:Birth', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P132_overlaps_with', Y, X],O1,_) \ fact(['a1:P132_overlaps_with', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P132_overlaps_with', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E71_Man-Made_Thing', X],O1,_) \ fact(['a1:P_E71_Man-Made_Thing', X, X],add,U) <=> member(del,[O1]) | fact(['a1:P_E71_Man-Made_Thing', X, X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E66_Formation', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P40_observed_dimension', X, _],O1,_) \ fact(['a1:E16_Measurement', X],add,U) <=> member(del,[O1]) | fact(['a1:E16_Measurement', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyPrecedingEvent', _, X1],O1,_) \ fact(['a2:Event', X1],add,U) <=> member(del,[O1]) | fact(['a2:Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P70_documents', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P131_is_identified_by', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P102i_is_title_of', _, X1],O1,_) \ fact(['a1:E71_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P11i_participated_in', X, Y],O1,_) \ fact(['a1:P12i_was_present_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P29_custody_received_by', X, _],O1,_) \ fact(['a1:E10_Transfer_of_Custody', X],add,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:event', Y, X],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:agent', Y, X],O1,_) \ fact(['a2:event', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:event', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P109_has_current_or_former_curator', X, _],O1,_) \ fact(['a1:E78_Collection', X],add,U) <=> member(del,[O1]) | fact(['a1:E78_Collection', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P136_was_based_on', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P30_transferred_custody_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyFollowingEvent', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P124i_was_transformed_by', X, _],O1,_) \ fact(['a1:E77_Persistent_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P132_overlaps_with', X, _],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P110_augmented', Y, X],O1,_) \ fact(['a1:P110i_was_augmented_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P110i_was_augmented_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P110i_was_augmented_by', Y, X],O1,_) \ fact(['a1:P110_augmented', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P110_augmented', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P142i_was_used_in', X, _],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E21_Person', X],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P44_has_condition', _, X1],O1,_) \ fact(['a1:E3_Condition_State', X1],add,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P78_is_identified_by', Y, X],O1,_) \ fact(['a1:P78i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P78i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P78i_identifies', Y, X],O1,_) \ fact(['a1:P78_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P78_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P112_diminished', _, X1],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P8i_witnessed', X, _],O1,_) \ fact(['a1:E19_Physical_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P5i_forms_part_of', Y, X],O1,_) \ fact(['a1:P5_consists_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P5_consists_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P5_consists_of', Y, X],O1,_) \ fact(['a1:P5i_forms_part_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P5i_forms_part_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P116_starts', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39i_was_measured_by', _, X1],O1,_) \ fact(['a1:E16_Measurement', X1],add,U) <=> member(del,[O1]) | fact(['a1:E16_Measurement', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:precedingEvent', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,_), fact(['a1:referToSame', X1, X2],O2,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,_) \ fact(['a1:relatedManMadeThings', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedManMadeThings', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:P5i_forms_part_of', X, X2],O1,_), fact(['a1:P5i_forms_part_of', X, X1],O2,_), fact(['a1:E3_Condition_State', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P10i_contains', _, X1],O1,_) \ fact(['a1:E4_Period', X1],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P125i_was_type_of_object_used_in', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P138_represents', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P10_falls_within', X, _],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P56_bears_feature', _, X1],O1,_) \ fact(['a1:E26_Physical_Feature', X1],add,U) <=> member(del,[O1]) | fact(['a1:E26_Physical_Feature', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', X, Y],O1,_) \ fact(['a1:P11i_participated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E44_Place_Appellation', X],O1,_), fact(['a1:E49_Time_Appellation', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P71_lists', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyPrecedingEvent', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:child', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Event', X],O1,_) \ fact(['a9:Event', X],add,U) <=> member(del,[O1]) | fact(['a9:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P91i_is_unit_of', X, _],O1,_) \ fact(['a1:E58_Measurement_Unit', X],add,U) <=> member(del,[O1]) | fact(['a1:E58_Measurement_Unit', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E50_Date', X],O1,_) \ fact(['a1:E49_Time_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E49_Time_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P23_transferred_title_from', X, Y],O1,_) \ fact(['a1:P14_carried_out_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P110_augmented', _, X1],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', Y, X],O1,_) \ fact(['a1:P55i_currently_holds', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P55i_currently_holds', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55i_currently_holds', Y, X],O1,_) \ fact(['a1:P55_has_current_location', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P55_has_current_location', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E31_Document', X0, X1],O1,_), fact(['a1:referredBySame', X1, X2],O2,_), fact(['a1:P_E31_Document', X2, X3],O3,_) \ fact(['a1:relatedDocuments', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedDocuments', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:relatedManMadeThings', Y, X],O1,_) \ fact(['a1:relatedManMadeThings', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:relatedManMadeThings', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P74i_is_current_or_former_residence_of', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P103i_was_intention_of', _, X1],O1,_) \ fact(['a1:E71_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P84_had_at_most_duration', X, X2],O1,_), fact(['a1:P84_had_at_most_duration', X, X1],O2,_), fact(['a1:E52_Time-Span', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P88_consists_of', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', _, X1],O1,_) \ fact(['a1:E83_Type_Creation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E83_Type_Creation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P119i_is_met_in_time_by', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', X, _],O1,_) \ fact(['a1:E16_Measurement', X],add,U) <=> member(del,[O1]) | fact(['a1:E16_Measurement', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P97i_was_father_for', X, _],O1,_) \ fact(['a1:E21_Person', X],add,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P42i_was_assigned_by', _, X1],O1,_) \ fact(['a1:E17_Type_Assignment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E17_Type_Assignment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', X, Y],O1,_) \ fact(['a1:P12i_was_present_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P106_is_composed_of', X, _],O1,_) \ fact(['a1:E90_Symbolic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P43_has_dimension', _, X1],O1,_) \ fact(['a1:E54_Dimension', X1],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P81_ongoing_throughout', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:family_name', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P140_assigned_attribute_to', X, _],O1,_) \ fact(['a1:E13_Attribute_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P70i_is_documented_in', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P7_took_place_at', X, _],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P45i_is_incorporated_in', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E10_Transfer_of_Custody', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73_has_translation', _, X1],O1,_) \ fact(['a1:E33_Linguistic_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', X, X2],O1,_), fact(['a1:P95i_was_formed_by', X, X1],O2,_), fact(['a1:E74_Group', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P134_continued', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P138i_has_representation', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P109_has_current_or_former_curator', Y, X],O1,_) \ fact(['a1:P109i_is_current_or_former_curator_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P109i_is_current_or_former_curator_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P109i_is_current_or_former_curator_of', Y, X],O1,_) \ fact(['a1:P109_has_current_or_former_curator', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P109_has_current_or_former_curator', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P11_had_participant', X, Y],O1,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P71_lists', X, Y],O1,_) \ fact(['a1:P67_refers_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P44_has_condition', Y, X],O1,_) \ fact(['a1:P44i_is_condition_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P44i_is_condition_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P44i_is_condition_of', Y, X],O1,_) \ fact(['a1:P44_has_condition', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P44_has_condition', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:openid', Y1, X],O1,_), fact(['a3:openid', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P132_overlaps_with', _, X1],O1,_) \ fact(['a1:E4_Period', X1],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P111i_was_added_by', _, X1],O1,_) \ fact(['a1:E79_Part_Addition', X1],add,U) <=> member(del,[O1]) | fact(['a1:E79_Part_Addition', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P40i_was_observed_in', _, X1],O1,_) \ fact(['a1:E16_Measurement', X1],add,U) <=> member(del,[O1]) | fact(['a1:E16_Measurement', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P102_has_title', _, X1],O1,_) \ fact(['a1:E35_Title', X1],add,U) <=> member(del,[O1]) | fact(['a1:E35_Title', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', Y, X],O1,_) \ fact(['a1:P99_dissolved', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P99_dissolved', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', Y, X],O1,_) \ fact(['a1:P99i_was_dissolved_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P99i_was_dissolved_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P119_meets_in_time_with', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P144_joined_with', X, Y],O1,_) \ fact(['a1:P11_had_participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:parent', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', X, Y],O1,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:initiatingEvent', _, X1],O1,_) \ fact(['a2:Event', X1],add,U) <=> member(del,[O1]) | fact(['a2:Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P104i_applies_to', _, X1],O1,_) \ fact(['a1:E72_Legal_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P71i_is_listed_in', _, X1],O1,_) \ fact(['a1:E32_Authority_Document', X1],add,U) <=> member(del,[O1]) | fact(['a1:E32_Authority_Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P35i_was_identified_by', X, _],O1,_) \ fact(['a1:E3_Condition_State', X],add,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E57_Material', X],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E53_Place', X0, X1],O1,_), fact(['a1:referredBySame', X1, X2],O2,_), fact(['a1:P_E53_Place', X2, X3],O3,_) \ fact(['a1:relatedPlaces', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedPlaces', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:P34i_was_assessed_by', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P121_overlaps_with', Y, X],O1,_) \ fact(['a1:P121_overlaps_with', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P121_overlaps_with', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13_destroyed', X, _],O1,_) \ fact(['a1:E6_Destruction', X],add,U) <=> member(del,[O1]) | fact(['a1:E6_Destruction', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P84_had_at_most_duration', _, X1],O1,_) \ fact(['a1:E54_Dimension', X1],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P45_consists_of', _, X1],O1,_) \ fact(['a1:E57_Material', X1],add,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P100i_died_in', X, Y],O1,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P123_resulted_in', _, X1],O1,_) \ fact(['a1:E77_Persistent_Item', X1],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E51_Contact_Point', X],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, X2],O1,_), fact(['a2:father', X, X1],O2,_), fact(['a3:Person', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, X4],O1,_), fact(['a2:mother', X, X3],O2,_), fact(['a3:Person', X],O3,_) \ fact(['owl:sameAs', X3, X4],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X3, X4],del,U), applied_rules(1,del).
phase(1), fact(['a1:P9i_forms_part_of', X, X2],O1,_), fact(['a1:P9i_forms_part_of', X, X1],O2,_), fact(['a1:E4_Period', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', X, Y],O1,_) \ fact(['a1:P11_had_participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P15i_influenced', Y, X],O1,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P15_was_influenced_by', Y, X],O1,_) \ fact(['a1:P15i_influenced', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X, _],O1,_) \ fact(['a1:E89_Propositional_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:parent', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P14i_performed', Y, X],O1,_) \ fact(['a1:P14_carried_out_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P14_carried_out_by', Y, X],O1,_) \ fact(['a1:P14i_performed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', X, _],O1,_) \ fact(['a1:E19_Physical_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95_has_formed', Y, X],O1,_) \ fact(['a1:P95i_was_formed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P95i_was_formed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', Y, X],O1,_) \ fact(['a1:P95_has_formed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P95_has_formed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', X, _],O1,_) \ fact(['a1:E74_Group', X],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P42i_was_assigned_by', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P94_has_created', _, X1],O1,_) \ fact(['a1:E28_Conceptual_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P131_is_identified_by', _, X1],O1,_) \ fact(['a1:E82_Actor_Appellation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E82_Actor_Appellation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:based_near', _, X1],O1,_) \ fact(['a10:SpatialThing', X1],add,U) <=> member(del,[O1]) | fact(['a10:SpatialThing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', Y, X],O1,_) \ fact(['a1:P108i_was_produced_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P108i_was_produced_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', Y, X],O1,_) \ fact(['a1:P108_has_produced', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P108_has_produced', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P112i_was_diminished_by', X, Y],O1,_) \ fact(['a1:P31i_was_modified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E46_Section_Definition', X],O1,_) \ fact(['a1:E44_Place_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P58i_defines_section', Y, X],O1,_) \ fact(['a1:P58_has_section_definition', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P58_has_section_definition', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P58_has_section_definition', Y, X],O1,_) \ fact(['a1:P58i_defines_section', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P58i_defines_section', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:age', X, Y1],O1,_), fact(['a3:age', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P23i_surrendered_title_through', _, X1],O1,_) \ fact(['a1:E8_Acquisition', X1],add,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P78_is_identified_by', X, Y],O1,_) \ fact(['a1:P1_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', X, Y],O1,_) \ fact(['a1:P7i_witnessed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P7i_witnessed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:currentProject', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P119i_is_met_in_time_by', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:aimChatID', Y1, X],O1,_), fact(['a3:aimChatID', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', Y, X],O1,_) \ fact(['a1:P27_moved_from', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P27_moved_from', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', Y, X],O1,_) \ fact(['a1:P27i_was_origin_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P27i_was_origin_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P37_assigned', _, X1],O1,_) \ fact(['a1:E42_Identifier', X1],add,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P116i_is_started_by', Y, X],O1,_) \ fact(['a1:P116_starts', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P116_starts', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P116_starts', Y, X],O1,_) \ fact(['a1:P116i_is_started_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P116i_is_started_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:sha1', X, _],O1,_) \ fact(['a3:Document', X],add,U) <=> member(del,[O1]) | fact(['a3:Document', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:agent', _, X1],O1,_) \ fact(['a3:Agent', X1],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P12_occurred_in_the_presence_of', X, _],O1,_) \ fact(['a1:E5_Event', X],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P117i_includes', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P29i_received_custody_through', X, Y],O1,_) \ fact(['a1:P14i_performed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P102_has_title', X, _],O1,_) \ fact(['a1:E71_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P118i_is_overlapped_in_time_by', Y, X],O1,_) \ fact(['a1:P118_overlaps_in_time_with', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P118_overlaps_in_time_with', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P118_overlaps_in_time_with', Y, X],O1,_) \ fact(['a1:P118i_is_overlapped_in_time_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P118i_is_overlapped_in_time_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P89_falls_within', X, Y],O1,_), fact(['a1:P89_falls_within', Y, Z],O2,_) \ fact(['a1:P89_falls_within', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P89_falls_within', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P138i_has_representation', X, Y],O1,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, Y1],O1,_), fact(['a2:father', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a3:status', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P137_exemplifies', X, Y],O1,_) \ fact(['a1:P2_has_type', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P2_has_type', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:event', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:followingEvent', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E49_Time_Appellation', X],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:witness', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P48i_is_preferred_identifier_of', X, Y],O1,_) \ fact(['a1:P1i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P26i_was_destination_of', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:openid', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:organization', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P14i_performed', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P48i_is_preferred_identifier_of', X, _],O1,_) \ fact(['a1:E42_Identifier', X],add,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:plan', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P34i_was_assessed_by', X, Y],O1,_) \ fact(['a1:P140i_was_attributed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P131_is_identified_by', Y, X],O1,_) \ fact(['a1:P131i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P131i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P131i_identifies', Y, X],O1,_) \ fact(['a1:P131_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P131_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P148i_is_component_of', _, X1],O1,_) \ fact(['a1:E89_Propositional_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P1_is_identified_by', _, X1],O1,_) \ fact(['a1:E41_Appellation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P129_is_about', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P115i_is_finished_by', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P42_assigned', Y, X],O1,_) \ fact(['a1:P42i_was_assigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P42i_was_assigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P42i_was_assigned_by', Y, X],O1,_) \ fact(['a1:P42_assigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P42_assigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:employer', _, X1],O1,_) \ fact(['a3:Agent', X1],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P31_has_modified', X, _],O1,_) \ fact(['a1:E11_Modification', X],add,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P87_is_identified_by', Y, X],O1,_) \ fact(['a1:P87i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P87i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P87i_identifies', Y, X],O1,_) \ fact(['a1:P87_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P87_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:spectator', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E28_Conceptual_Object', X],O1,_) \ fact(['a1:E71_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', X, _],O1,_) \ fact(['a1:E68_Dissolution', X],add,U) <=> member(del,[O1]) | fact(['a1:E68_Dissolution', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:birth', X, Y],O1,_) \ fact(['a2:event', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:event', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', X, X2],O1,_), fact(['a1:P135i_was_created_by', X, X1],O2,_), fact(['a1:E55_Type', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:E9_Move', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P128i_is_carried_by', _, X1],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P71i_is_listed_in', X, Y],O1,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P5_consists_of', _, X1],O1,_) \ fact(['a1:E3_Condition_State', X1],add,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P78i_identifies', X, _],O1,_) \ fact(['a1:E49_Time_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E49_Time_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P65i_is_shown_by', X, Y],O1,_) \ fact(['a1:P128i_is_carried_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P128i_is_carried_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E8_Acquisition', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:followingEvent', _, X1],O1,_) \ fact(['a2:Event', X1],add,U) <=> member(del,[O1]) | fact(['a2:Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:icqChatID', _, X1],O1,_) \ fact(['rdfs:Literal', X1],add,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a5:PhysicalMedium', X],O1,_) \ fact(['a5:MediaType', X],add,U) <=> member(del,[O1]) | fact(['a5:MediaType', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P70i_is_documented_in', Y, X],O1,_) \ fact(['a1:P70_documents', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P70_documents', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P70_documents', Y, X],O1,_) \ fact(['a1:P70i_is_documented_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P70i_is_documented_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E75_Conceptual_Object_Appellation', X],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P83i_was_minimum_duration_of', X, _],O1,_) \ fact(['a1:E54_Dimension', X],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:Group', X],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P126_employed', _, X1],O1,_) \ fact(['a1:E57_Material', X1],add,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P40i_was_observed_in', X, _],O1,_) \ fact(['a1:E54_Dimension', X],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:agent', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P71_lists', X, _],O1,_) \ fact(['a1:E32_Authority_Document', X],add,U) <=> member(del,[O1]) | fact(['a1:E32_Authority_Document', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P32i_was_technique_of', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E20_Biological_Object', X],O1,_) \ fact(['a1:E19_Physical_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P87i_identifies', X, _],O1,_) \ fact(['a1:E44_Place_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P130i_features_are_also_found_on', _, X1],O1,_) \ fact(['a1:E70_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P119i_is_met_in_time_by', Y, X],O1,_) \ fact(['a1:P119_meets_in_time_with', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P119_meets_in_time_with', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P119_meets_in_time_with', Y, X],O1,_) \ fact(['a1:P119i_is_met_in_time_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P119i_is_met_in_time_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:interest', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P146i_lost_member_by', X, Y],O1,_) \ fact(['a1:P11i_participated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P30i_custody_transferred_through', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P104_is_subject_to', _, X1],O1,_) \ fact(['a1:E30_Right', X1],add,U) <=> member(del,[O1]) | fact(['a1:E30_Right', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P110_augmented', X, _],O1,_) \ fact(['a1:E79_Part_Addition', X],add,U) <=> member(del,[O1]) | fact(['a1:E79_Part_Addition', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:based_near', X, _],O1,_) \ fact(['a10:SpatialThing', X],add,U) <=> member(del,[O1]) | fact(['a10:SpatialThing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', _, X1],O1,_) \ fact(['a1:E70_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E72_Legal_Object', X],O1,_) \ fact(['a1:E70_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67i_is_referred_to_by', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P112_diminished', X, _],O1,_) \ fact(['a1:E80_Part_Removal', X],add,U) <=> member(del,[O1]) | fact(['a1:E80_Part_Removal', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:NameChange', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E37_Mark', X],O1,_) \ fact(['a1:E36_Visual_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E73_Information_Object', X0, X1],O1,_), fact(['a1:P67_refers_to', X1, X2],O2,_), fact(['a1:P_E73_Information_Object', X2, X3],O3,_) \ fact(['a1:relatedInformationObjects', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedInformationObjects', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a3:depicts', X, _],O1,_) \ fact(['a3:Image', X],add,U) <=> member(del,[O1]) | fact(['a3:Image', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:isPrimaryTopicOf', X, Y],O1,_) \ fact(['a3:page', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P146i_lost_member_by', X, _],O1,_) \ fact(['a1:E74_Group', X],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P59i_is_located_on_or_within', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X1, X0],O1,_), fact(['a1:P67_refers_to', X1, X2],O2,_) \ fact(['a1:referredBySame', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:referredBySame', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P28i_surrendered_custody_through', _, X1],O1,_) \ fact(['a1:E10_Transfer_of_Custody', X1],add,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P87i_identifies', X, Y],O1,_) \ fact(['a1:P1i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P68i_use_foreseen_by', _, X1],O1,_) \ fact(['a1:E29_Design_or_Procedure', X1],add,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P17i_motivated', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P22_transferred_title_to', X, Y1],O1,_), fact(['a1:P22_transferred_title_to', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P86i_contains', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P25i_moved_by', X, Y],O1,_) \ fact(['a1:P12i_was_present_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P40_observed_dimension', X, Y],O1,_) \ fact(['a1:P141_assigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P46_is_composed_of', Y, X],O1,_) \ fact(['a1:P46i_forms_part_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P46i_forms_part_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P46i_forms_part_of', Y, X],O1,_) \ fact(['a1:P46_is_composed_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P46_is_composed_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P48_has_preferred_identifier', X, Y],O1,_) \ fact(['a1:P1_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P91_has_unit', _, X1],O1,_) \ fact(['a1:E58_Measurement_Unit', X1],add,U) <=> member(del,[O1]) | fact(['a1:E58_Measurement_Unit', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P127_has_broader_term', X, Y],O1,_), fact(['a1:P127_has_broader_term', Y, Z],O2,_) \ fact(['a1:P127_has_broader_term', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P127_has_broader_term', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a2:event', _, X1],O1,_) \ fact(['a2:Event', X1],add,U) <=> member(del,[O1]) | fact(['a2:Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E3_Condition_State', X],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:accountServiceHomepage', X, _],O1,_) \ fact(['a3:OnlineAccount', X],add,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P70i_is_documented_in', X, Y],O1,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:holdsAccount', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X0, X1],O1,_), fact(['a1:P_E31_Document', X1, X2],O2,_) \ fact(['a1:refersToDocument', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:refersToDocument', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P146_separated_from', _, X1],O1,_) \ fact(['a1:E74_Group', X1],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P45i_is_incorporated_in', X, _],O1,_) \ fact(['a1:E57_Material', X],add,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P88i_forms_part_of', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P24i_changed_ownership_through', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:jabberID', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:participant', _, X1],O1,_) \ fact(['a3:Agent', X1],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P4_has_time-span', X, X2],O1,_), fact(['a1:P4_has_time-span', X, X1],O2,_), fact(['a1:E2_Temporal_Entity', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', X, X2],O1,_), fact(['a1:P55_has_current_location', X, X1],O2,_), fact(['a1:E19_Physical_Object', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P120i_occurs_after', X, Y],O1,_), fact(['a1:P120i_occurs_after', Y, Z],O2,_) \ fact(['a1:P120i_occurs_after', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P120i_occurs_after', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:E13_Attribute_Assignment', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:knows', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:weblog', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:PositionChange', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P134_continued', Y, X],O1,_) \ fact(['a1:P134i_was_continued_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P134i_was_continued_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P134i_was_continued_by', Y, X],O1,_) \ fact(['a1:P134_continued', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P134_continued', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P29_custody_received_by', X, Y],O1,_) \ fact(['a1:P14_carried_out_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P43i_is_dimension_of', X, _],O1,_) \ fact(['a1:E54_Dimension', X],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P137_exemplifies', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P65i_is_shown_by', X, _],O1,_) \ fact(['a1:E36_Visual_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P91i_is_unit_of', Y, X],O1,_) \ fact(['a1:P91_has_unit', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P91_has_unit', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P91_has_unit', Y, X],O1,_) \ fact(['a1:P91i_is_unit_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P91i_is_unit_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55_has_current_location', X, Y],O1,_) \ fact(['a1:P53_has_former_or_current_location', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P53_has_former_or_current_location', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P145i_left_by', Y, X],O1,_) \ fact(['a1:P145_separated', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P145_separated', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P145_separated', Y, X],O1,_) \ fact(['a1:P145i_left_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P145i_left_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95_has_formed', X, _],O1,_) \ fact(['a1:E66_Formation', X],add,U) <=> member(del,[O1]) | fact(['a1:E66_Formation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P38i_was_deassigned_by', X, _],O1,_) \ fact(['a1:E42_Identifier', X],add,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyPrecedingEvent', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:isPrimaryTopicOf', Y, X],O1,_) \ fact(['a3:primaryTopic', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:primaryTopic', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:primaryTopic', Y, X],O1,_) \ fact(['a3:isPrimaryTopicOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:isPrimaryTopicOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P38_deassigned', X, _],O1,_) \ fact(['a1:E15_Identifier_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P17_was_motivated_by', X, Y],O1,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P4i_is_time-span_of', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E31_Document', X0, X1],O1,_), fact(['a1:referToSame', X1, X2],O2,_), fact(['a1:P_E31_Document', X2, X3],O3,_) \ fact(['a1:relatedDocuments', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedDocuments', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a2:Performance', X],O1,_) \ fact(['a2:GroupEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:GroupEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:PersonalProfileDocument', X],O1,_) \ fact(['a3:Document', X],add,U) <=> member(del,[O1]) | fact(['a3:Document', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P17_was_motivated_by', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P19_was_intended_use_of', Y, X],O1,_) \ fact(['a1:P19i_was_made_for', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P19i_was_made_for', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P19i_was_made_for', Y, X],O1,_) \ fact(['a1:P19_was_intended_use_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P19_was_intended_use_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P29i_received_custody_through', _, X1],O1,_) \ fact(['a1:E10_Transfer_of_Custody', X1],add,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P30_transferred_custody_of', X, _],O1,_) \ fact(['a1:E10_Transfer_of_Custody', X],add,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:skypeID', X, Y],O1,_) \ fact(['a3:nick', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P101_had_as_general_use', Y, X],O1,_) \ fact(['a1:P101i_was_use_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P101i_was_use_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P101i_was_use_of', Y, X],O1,_) \ fact(['a1:P101_had_as_general_use', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P101_had_as_general_use', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P131_is_identified_by', X, Y],O1,_) \ fact(['a1:P1_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P46i_forms_part_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P76_has_contact_point', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:death', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:followingEvent', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P58i_defines_section', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', X, _],O1,_) \ fact(['a1:E70_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', X, Y],O1,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:relatedDocuments', Y, X],O1,_) \ fact(['a1:relatedDocuments', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:relatedDocuments', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P75_possesses', _, X1],O1,_) \ fact(['a1:E30_Right', X1],add,U) <=> member(del,[O1]) | fact(['a1:E30_Right', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E5_Event', X],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P131i_identifies', X, _],O1,_) \ fact(['a1:E82_Actor_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E82_Actor_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P35_has_identified', X, _],O1,_) \ fact(['a1:E14_Condition_Assessment', X],add,U) <=> member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P143_joined', X, X2],O1,_), fact(['a1:P143_joined', X, X1],O2,_), fact(['a1:E85_Joining', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P83_had_at_least_duration', Y, X],O1,_) \ fact(['a1:P83i_was_minimum_duration_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P83i_was_minimum_duration_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P83i_was_minimum_duration_of', Y, X],O1,_) \ fact(['a1:P83_had_at_least_duration', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P83_had_at_least_duration', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P113i_was_removed_by', Y, X],O1,_) \ fact(['a1:P113_removed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P113_removed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P113_removed', Y, X],O1,_) \ fact(['a1:P113i_was_removed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P113i_was_removed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', X, Y],O1,_) \ fact(['a1:P7_took_place_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P7_took_place_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E73_Information_Object', X0, X1],O1,_), fact(['a1:referToSame', X1, X2],O2,_), fact(['a1:P_E73_Information_Object', X2, X3],O3,_) \ fact(['a1:relatedInformationObjects', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedInformationObjects', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', X, Y],O1,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E31_Document', X],O1,_) \ fact(['a1:E73_Information_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E40_Legal_Body', X],O1,_) \ fact(['a1:E74_Group', X],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P106_is_composed_of', X, Y],O1,_), fact(['a1:P106_is_composed_of', Y, Z],O2,_) \ fact(['a1:P106_is_composed_of', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P106_is_composed_of', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P62i_is_depicted_by', Y, X],O1,_) \ fact(['a1:P62_depicts', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P62_depicts', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P62_depicts', Y, X],O1,_) \ fact(['a1:P62i_is_depicted_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P62i_is_depicted_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:birth', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E39_Actor', X],O1,_) \ fact(['a1:E77_Persistent_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E64_End_of_Existence', X],O1,_) \ fact(['a1:E5_Event', X],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P74_has_current_or_former_residence', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P110i_was_augmented_by', X, Y],O1,_) \ fact(['a1:P31i_was_modified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P52i_is_current_owner_of', X, Y],O1,_) \ fact(['a1:P105i_has_right_on', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P105i_has_right_on', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P101_had_as_general_use', X, _],O1,_) \ fact(['a1:E70_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13_destroyed', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P142_used_constituent', X, _],O1,_) \ fact(['a1:E15_Identifier_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E45_Address', X],O1,_) \ fact(['a1:E51_Contact_Point', X],add,U) <=> member(del,[O1]) | fact(['a1:E51_Contact_Point', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P43i_is_dimension_of', Y, X],O1,_) \ fact(['a1:P43_has_dimension', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P43_has_dimension', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P43_has_dimension', Y, X],O1,_) \ fact(['a1:P43i_is_dimension_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P43i_is_dimension_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P21_had_general_purpose', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:relationship', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a5:AgentClass', X],O1,_) \ fact(['rdfs:Class', X],add,U) <=> member(del,[O1]) | fact(['rdfs:Class', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P31i_was_modified_by', Y, X],O1,_) \ fact(['a1:P31_has_modified', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P31_has_modified', Y, X],O1,_) \ fact(['a1:P31i_was_modified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P31i_was_modified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:partner', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', Y, X],O1,_) \ fact(['a1:P98_brought_into_life', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P98_brought_into_life', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98_brought_into_life', Y, X],O1,_) \ fact(['a1:P98i_was_born', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P98i_was_born', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyFollowingEvent', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P134_continued', X, Y],O1,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P35_has_identified', _, X1],O1,_) \ fact(['a1:E3_Condition_State', X1],add,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P51i_is_former_or_current_owner_of', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, Y],O1,_) \ fact(['a6:childOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a6:childOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P115_finishes', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:thumbnail', _, X1],O1,_) \ fact(['a3:Image', X1],add,U) <=> member(del,[O1]) | fact(['a3:Image', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P2_has_type', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P5i_forms_part_of', _, X1],O1,_) \ fact(['a1:E3_Condition_State', X1],add,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P22i_acquired_title_through', Y, X],O1,_) \ fact(['a1:P22_transferred_title_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P22_transferred_title_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P22_transferred_title_to', Y, X],O1,_) \ fact(['a1:P22i_acquired_title_through', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P22i_acquired_title_through', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P25_moved', _, X1],O1,_) \ fact(['a1:E19_Physical_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P127_has_broader_term', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P69_is_associated_with', Y, X],O1,_) \ fact(['a1:P69_is_associated_with', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P69_is_associated_with', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P139_has_alternative_form', _, X1],O1,_) \ fact(['a1:E41_Appellation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P26_moved_to', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P123_resulted_in', X, _],O1,_) \ fact(['a1:E81_Transformation', X],add,U) <=> member(del,[O1]) | fact(['a1:E81_Transformation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P92_brought_into_existence', _, X1],O1,_) \ fact(['a1:E77_Persistent_Item', X1],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],del,U), applied_rules(1,del).
phase(1), fact(['a5:FileFormat', X],O1,_) \ fact(['a5:MediaType', X],add,U) <=> member(del,[O1]) | fact(['a5:MediaType', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P50_has_current_keeper', X, Y],O1,_) \ fact(['a1:P49_has_former_or_current_keeper', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:firstName', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P2_has_type', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E25_Man-Made_Feature', X],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E73_Information_Object', X],O1,_) \ fact(['a1:E89_Propositional_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P96i_gave_birth', X, Y],O1,_) \ fact(['a1:P11i_participated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P28_custody_surrendered_by', X, _],O1,_) \ fact(['a1:E10_Transfer_of_Custody', X],add,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55i_currently_holds', X, Y],O1,_) \ fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P87_is_identified_by', X, Y],O1,_) \ fact(['a1:P1_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P37_assigned', X, Y],O1,_) \ fact(['a1:P141_assigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:workInfoHomepage', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E22_Man-Made_Object', X],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P109i_is_current_or_former_curator_of', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P15i_influenced', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', X, X2],O1,_), fact(['a1:P73i_is_translation_of', X, X1],O2,_), fact(['a1:E33_Linguistic_Object', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95i_was_formed_by', _, X1],O1,_) \ fact(['a1:E66_Formation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E66_Formation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P129_is_about', X, Y],O1,_) \ fact(['a1:P67_refers_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E81_Transformation', X],O1,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E31_Document', X0, X1],O1,_), fact(['a1:refersToDocument', X1, X2],O2,_), fact(['a1:refersToDocument', X2, X3],O3,_) \ fact(['a1:relatedDocuments', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedDocuments', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:P33i_was_used_by', Y, X],O1,_) \ fact(['a1:P33_used_specific_technique', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P33_used_specific_technique', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P33_used_specific_technique', Y, X],O1,_) \ fact(['a1:P33i_was_used_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P33i_was_used_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P111_added', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P129i_is_subject_of', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P9i_forms_part_of', X, _],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P14_carried_out_by', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P126i_was_employed_in', _, X1],O1,_) \ fact(['a1:E11_Modification', X1],add,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,_), fact(['a1:referredBySame', X1, X2],O2,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,_) \ fact(['a1:relatedManMadeThings', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedManMadeThings', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:P58i_defines_section', X, _],O1,_) \ fact(['a1:E46_Section_Definition', X],add,U) <=> member(del,[O1]) | fact(['a1:E46_Section_Definition', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P14i_performed', X, Y],O1,_) \ fact(['a1:P11i_participated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P139_has_alternative_form', X, _],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P75_possesses', Y, X],O1,_) \ fact(['a1:P75i_is_possessed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P75i_is_possessed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P75i_is_possessed_by', Y, X],O1,_) \ fact(['a1:P75_possesses', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P75_possesses', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:position', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P145i_left_by', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P10_falls_within', _, X1],O1,_) \ fact(['a1:E4_Period', X1],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E45_Address', X],O1,_) \ fact(['a1:E44_Place_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyFollowingEvent', X, Y],O1,_) \ fact(['a2:followingEvent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:followingEvent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', _, X1],O1,_) \ fact(['a1:E33_Linguistic_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Employment', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a5:Location', X],O1,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],add,U) <=> member(del,[O1]) | fact(['a5:LocationPeriodOrJurisdiction', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P33i_was_used_by', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:topic', X, _],O1,_) \ fact(['a3:Document', X],add,U) <=> member(del,[O1]) | fact(['a3:Document', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P12_occurred_in_the_presence_of', Y, X],O1,_) \ fact(['a1:P12i_was_present_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P12i_was_present_at', Y, X],O1,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P117_occurs_during', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P76i_provides_access_to', X, _],O1,_) \ fact(['a1:E51_Contact_Point', X],add,U) <=> member(del,[O1]) | fact(['a1:E51_Contact_Point', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P70_documents', X, _],O1,_) \ fact(['a1:E31_Document', X],add,U) <=> member(del,[O1]) | fact(['a1:E31_Document', X],del,U), applied_rules(1,del).
phase(1), fact(['a5:MediaType', X],O1,_) \ fact(['a5:MediaTypeOrExtent', X],add,U) <=> member(del,[O1]) | fact(['a5:MediaTypeOrExtent', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:maker', _, X1],O1,_) \ fact(['a3:Agent', X1],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:primaryTopic', X, Y1],O1,_), fact(['a3:primaryTopic', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a3:mbox_sha1sum', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', _, X1],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P35i_was_identified_by', _, X1],O1,_) \ fact(['a1:E14_Condition_Assessment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P76_has_contact_point', _, X1],O1,_) \ fact(['a1:E51_Contact_Point', X1],add,U) <=> member(del,[O1]) | fact(['a1:E51_Contact_Point', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E84_Information_Carrier', X],O1,_) \ fact(['a1:E22_Man-Made_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E22_Man-Made_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P48_has_preferred_identifier', Y, X],O1,_) \ fact(['a1:P48i_is_preferred_identifier_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P48i_is_preferred_identifier_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P48i_is_preferred_identifier_of', Y, X],O1,_) \ fact(['a1:P48_has_preferred_identifier', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P48_has_preferred_identifier', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:BasMitzvah', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P124i_was_transformed_by', Y, X],O1,_) \ fact(['a1:P124_transformed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P124_transformed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P124_transformed', Y, X],O1,_) \ fact(['a1:P124i_was_transformed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P124i_was_transformed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P92_brought_into_existence', X, Y],O1,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13_destroyed', X, Y],O1,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P8_took_place_on_or_within', Y, X],O1,_) \ fact(['a1:P8i_witnessed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P8i_witnessed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P8i_witnessed', Y, X],O1,_) \ fact(['a1:P8_took_place_on_or_within', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P8_took_place_on_or_within', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P76i_provides_access_to', Y, X],O1,_) \ fact(['a1:P76_has_contact_point', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P76_has_contact_point', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P76_has_contact_point', Y, X],O1,_) \ fact(['a1:P76i_provides_access_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P76i_provides_access_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P106i_forms_part_of', _, X1],O1,_) \ fact(['a1:E90_Symbolic_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P56_bears_feature', X, Y],O1,_) \ fact(['a1:P46_is_composed_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P46_is_composed_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P145i_left_by', X, Y],O1,_) \ fact(['a1:P11i_participated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:mbox', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P53_has_former_or_current_location', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', X, _],O1,_) \ fact(['a1:E74_Group', X],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P25_moved', X, Y],O1,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyFollowingEvent', _, X1],O1,_) \ fact(['a2:Event', X1],add,U) <=> member(del,[O1]) | fact(['a2:Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P96_by_mother', _, X1],O1,_) \ fact(['a1:E21_Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:msnChatID', X, Y],O1,_) \ fact(['a3:nick', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P146i_lost_member_by', Y, X],O1,_) \ fact(['a1:P146_separated_from', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P146_separated_from', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P146_separated_from', Y, X],O1,_) \ fact(['a1:P146i_lost_member_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P146i_lost_member_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P40_observed_dimension', _, X1],O1,_) \ fact(['a1:E54_Dimension', X1],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:mother', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P33_used_specific_technique', _, X1],O1,_) \ fact(['a1:E29_Design_or_Procedure', X1],add,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41i_was_classified_by', X, Y],O1,_) \ fact(['a1:P140i_was_attributed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:schoolHomepage', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P52_has_current_owner', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P7_took_place_at', Y, X],O1,_) \ fact(['a1:P7i_witnessed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P7i_witnessed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P7i_witnessed', Y, X],O1,_) \ fact(['a1:P7_took_place_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P7_took_place_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95_has_formed', _, X1],O1,_) \ fact(['a1:E74_Group', X1],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:Person', X],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P127i_has_narrower_term', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E6_Destruction', X],O1,_) \ fact(['a1:E64_End_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P53i_is_former_or_current_location_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P134_continued', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:account', _, X1],O1,_) \ fact(['a3:OnlineAccount', X1],add,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P127_has_broader_term', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P93_took_out_of_existence', _, X1],O1,_) \ fact(['a1:E77_Persistent_Item', X1],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P137_exemplifies', Y, X],O1,_) \ fact(['a1:P137i_is_exemplified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P137i_is_exemplified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P137i_is_exemplified_by', Y, X],O1,_) \ fact(['a1:P137_exemplifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P137_exemplifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P22_transferred_title_to', X, _],O1,_) \ fact(['a1:E8_Acquisition', X],add,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:accountName', X, _],O1,_) \ fact(['a3:OnlineAccount', X],add,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P30i_custody_transferred_through', _, X1],O1,_) \ fact(['a1:E10_Transfer_of_Custody', X1],add,U) <=> member(del,[O1]) | fact(['a1:E10_Transfer_of_Custody', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P86_falls_within', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', X, Y],O1,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P20_had_specific_purpose', Y, X],O1,_) \ fact(['a1:P20i_was_purpose_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P20i_was_purpose_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P20i_was_purpose_of', Y, X],O1,_) \ fact(['a1:P20_had_specific_purpose', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P20_had_specific_purpose', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P89i_contains', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P5i_forms_part_of', X, _],O1,_) \ fact(['a1:E3_Condition_State', X],add,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P49i_is_former_or_current_keeper_of', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P128i_is_carried_by', X, _],O1,_) \ fact(['a1:E73_Information_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Imprisonment', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:tipjar', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P92i_was_brought_into_existence_by', X, Y],O1,_) \ fact(['a1:P12i_was_present_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', X, Y],O1,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:organization', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:concurrentEvent', Y, X],O1,_) \ fact(['a2:concurrentEvent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:concurrentEvent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:yahooChatID', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P42_assigned', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P91_has_unit', X, _],O1,_) \ fact(['a1:E54_Dimension', X],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Retirement', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:tipjar', X, Y],O1,_) \ fact(['a3:page', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P62_depicts', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:interval', _, X1],O1,_) \ fact(['a2:Interval', X1],add,U) <=> member(del,[O1]) | fact(['a2:Interval', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:olb', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P117i_includes', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P88i_forms_part_of', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', X, Y],O1,_) \ fact(['a1:P130i_features_are_also_found_on', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135_created_type', X, _],O1,_) \ fact(['a1:E83_Type_Creation', X],add,U) <=> member(del,[O1]) | fact(['a1:E83_Type_Creation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P59i_is_located_on_or_within', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Dismissal', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P96i_gave_birth', _, X1],O1,_) \ fact(['a1:E67_Birth', X1],add,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E27_Site', X],O1,_) \ fact(['a1:E26_Physical_Feature', X],add,U) <=> member(del,[O1]) | fact(['a1:E26_Physical_Feature', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:principal', X, X2],O1,_), fact(['a2:principal', X, X1],O2,_), fact(['a2:IndividualEvent', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a3:msnChatID', _, X1],O1,_) \ fact(['rdfs:Literal', X1],add,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:homepage', Y1, X],O1,_), fact(['a3:homepage', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P1i_identifies', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P10_falls_within', X, Y],O1,_), fact(['a1:P10_falls_within', Y, Z],O2,_) \ fact(['a1:P10_falls_within', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P10_falls_within', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P96_by_mother', X, _],O1,_) \ fact(['a1:E67_Birth', X],add,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Enrolment', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P75_possesses', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P93i_was_taken_out_of_existence_by', _, X1],O1,_) \ fact(['a1:E64_End_of_Existence', X1],add,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P100_was_death_of', _, X1],O1,_) \ fact(['a1:E21_Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P126i_was_employed_in', X, _],O1,_) \ fact(['a1:E57_Material', X],add,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P9i_forms_part_of', _, X1],O1,_) \ fact(['a1:E4_Period', X1],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:Person', X],O1,_) \ fact(['a10:SpatialThing', X],add,U) <=> member(del,[O1]) | fact(['a10:SpatialThing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', X, Y],O1,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P92i_was_brought_into_existence_by', X, _],O1,_) \ fact(['a1:E77_Persistent_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P54i_is_current_permanent_location_of', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P51i_is_former_or_current_owner_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P115i_is_finished_by', X, Y],O1,_), fact(['a1:P115i_is_finished_by', Y, Z],O2,_) \ fact(['a1:P115i_is_finished_by', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P115i_is_finished_by', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P137i_is_exemplified_by', X, Y],O1,_) \ fact(['a1:P2i_is_type_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P2i_is_type_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:concludingEvent', _, X1],O1,_) \ fact(['a2:Event', X1],add,U) <=> member(del,[O1]) | fact(['a2:Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:thumbnail', X, _],O1,_) \ fact(['a3:Image', X],add,U) <=> member(del,[O1]) | fact(['a3:Image', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:parent', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P44i_is_condition_of', X, _],O1,_) \ fact(['a1:E3_Condition_State', X],add,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P144i_gained_member_by', X, Y],O1,_) \ fact(['a1:P11i_participated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P118i_is_overlapped_in_time_by', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P129i_is_subject_of', _, X1],O1,_) \ fact(['a1:E89_Propositional_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', _, X1],O1,_) \ fact(['a1:E74_Group', X1],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P20_had_specific_purpose', _, X1],O1,_) \ fact(['a1:E5_Event', X1],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', _, X1],O1,_) \ fact(['a1:E67_Birth', X1],add,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P32i_was_technique_of', X, Y],O1,_) \ fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', X, Y],O1,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P65_shows_visual_item', X, _],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P129i_is_subject_of', X, Y],O1,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P134i_was_continued_by', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:msnChatID', Y1, X],O1,_), fact(['a3:msnChatID', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P87_is_identified_by', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:Person', X],O1,_), fact(['a3:Project', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E33_Linguistic_Object', X],O1,_) \ fact(['a1:E73_Information_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:geekcode', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:officiator', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P114_is_equal_in_time_to', Y, X],O1,_) \ fact(['a1:P114_is_equal_in_time_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P114_is_equal_in_time_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:partner', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:spectator', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P28i_surrendered_custody_through', X, Y],O1,_) \ fact(['a1:P14i_performed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P136i_supported_type_creation', X, Y],O1,_) \ fact(['a1:P15i_influenced', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P72i_is_language_of', X, _],O1,_) \ fact(['a1:E56_Language', X],add,U) <=> member(del,[O1]) | fact(['a1:E56_Language', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P96_by_mother', X, Y],O1,_) \ fact(['a1:P11_had_participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P116_starts', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:img', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P100i_died_in', X, _],O1,_) \ fact(['a1:E21_Person', X],add,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P96i_gave_birth', X, _],O1,_) \ fact(['a1:E21_Person', X],add,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', X, Y],O1,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:familyName', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P148_has_component', X, Y],O1,_), fact(['a1:P148_has_component', Y, Z],O2,_) \ fact(['a1:P148_has_component', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P148_has_component', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P55i_currently_holds', _, X1],O1,_) \ fact(['a1:E19_Physical_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Event', X],O1,_) \ fact(['a11:Event', X],add,U) <=> member(del,[O1]) | fact(['a11:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P97i_was_father_for', Y, X],O1,_) \ fact(['a1:P97_from_father', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P97_from_father', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P97_from_father', Y, X],O1,_) \ fact(['a1:P97i_was_father_for', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P97i_was_father_for', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P26_moved_to', X, _],O1,_) \ fact(['a1:E9_Move', X],add,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E52_Time-Span', X],O1,_), fact(['a1:E53_Place', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P89_falls_within', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E56_Language', X],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:spectator', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P40i_was_observed_in', Y, X],O1,_) \ fact(['a1:P40_observed_dimension', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P40_observed_dimension', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P40_observed_dimension', Y, X],O1,_) \ fact(['a1:P40i_was_observed_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P40i_was_observed_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E71_Man-Made_Thing', X0, X1],O1,_), fact(['a1:P67_refers_to', X1, X2],O2,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],O3,_) \ fact(['a1:relatedManMadeThings', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedManMadeThings', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a2:Adoption', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P42i_was_assigned_by', X, Y],O1,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P95_has_formed', X, Y],O1,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P31i_was_modified_by', X, Y],O1,_) \ fact(['a1:P12i_was_present_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P56i_is_found_on', X, Y],O1,_) \ fact(['a1:P46i_forms_part_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P46i_forms_part_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P117_occurs_during', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99_dissolved', X, Y],O1,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:msnChatID', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P89i_contains', X, Y],O1,_), fact(['a1:P89i_contains', Y, Z],O2,_) \ fact(['a1:P89i_contains', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P89i_contains', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E31_Document', X0, X1],O1,_), fact(['a1:P67_refers_to', X1, X2],O2,_), fact(['a1:P_E31_Document', X2, X3],O3,_) \ fact(['a1:relatedDocuments', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedDocuments', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:P137i_is_exemplified_by', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P130_shows_features_of', Y, X],O1,_) \ fact(['a1:P130i_features_are_also_found_on', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P130i_features_are_also_found_on', Y, X],O1,_) \ fact(['a1:P130_shows_features_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P130_shows_features_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P52i_is_current_owner_of', X, Y],O1,_) \ fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P46i_forms_part_of', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P19i_was_made_for', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E17_Type_Assignment', X],O1,_) \ fact(['a1:E13_Attribute_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E32_Authority_Document', X],O1,_) \ fact(['a1:E31_Document', X],add,U) <=> member(del,[O1]) | fact(['a1:E31_Document', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', Y, X],O1,_) \ fact(['a1:P135_created_type', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P135_created_type', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135_created_type', Y, X],O1,_) \ fact(['a1:P135i_was_created_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P135i_was_created_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P120_occurs_before', Y, X],O1,_) \ fact(['a1:P120i_occurs_after', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P120i_occurs_after', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P120i_occurs_after', Y, X],O1,_) \ fact(['a1:P120_occurs_before', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P120_occurs_before', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P107i_is_current_or_former_member_of', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:gender', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P19i_was_made_for', X, _],O1,_) \ fact(['a1:E71_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P86_falls_within', X, Y],O1,_), fact(['a1:P86_falls_within', Y, Z],O2,_) \ fact(['a1:P86_falls_within', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P86_falls_within', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P120_occurs_before', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E19_Physical_Object', X],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P7i_witnessed', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P75i_is_possessed_by', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['rdfs:ContainerMembershipProperty', X],O1,_) \ fact(['rdf:Property', X],add,U) <=> member(del,[O1]) | fact(['rdf:Property', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', _, X1],O1,_) \ fact(['a1:E9_Move', X1],add,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P92i_was_brought_into_existence_by', _, X1],O1,_) \ fact(['a1:E63_Beginning_of_Existence', X1],add,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P113i_was_removed_by', _, X1],O1,_) \ fact(['a1:E80_Part_Removal', X1],add,U) <=> member(del,[O1]) | fact(['a1:E80_Part_Removal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P103_was_intended_for', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:child', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:homepage', X, Y],O1,_) \ fact(['a3:page', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:partner', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39i_was_measured_by', X, Y],O1,_) \ fact(['a1:P140i_was_attributed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E48_Place_Name', X],O1,_) \ fact(['a1:P_E53_Place', X, X],add,U) <=> member(del,[O1]) | fact(['a1:P_E53_Place', X, X],del,U), applied_rules(1,del).
phase(1), fact(['a3:schoolHomepage', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P34_concerned', X, _],O1,_) \ fact(['a1:E14_Condition_Assessment', X],add,U) <=> member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Redundancy', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P28_custody_surrendered_by', Y, X],O1,_) \ fact(['a1:P28i_surrendered_custody_through', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P28i_surrendered_custody_through', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P28i_surrendered_custody_through', Y, X],O1,_) \ fact(['a1:P28_custody_surrendered_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P28_custody_surrendered_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', X, Y],O1,_), fact(['a1:P27_moved_from', Y, Z],O2,_) \ fact(['a1:P27_moved_from', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P27_moved_from', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:E80_Part_Removal', X],O1,_) \ fact(['a1:E11_Modification', X],add,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P102i_is_title_of', X, _],O1,_) \ fact(['a1:E35_Title', X],add,U) <=> member(del,[O1]) | fact(['a1:E35_Title', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P116i_is_started_by', X, Y],O1,_), fact(['a1:P116i_is_started_by', Y, Z],O2,_) \ fact(['a1:P116i_is_started_by', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P116i_is_started_by', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:E44_Place_Appellation', X],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P54_has_current_permanent_location', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P38i_was_deassigned_by', Y, X],O1,_) \ fact(['a1:P38_deassigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P38_deassigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P38_deassigned', Y, X],O1,_) \ fact(['a1:P38i_was_deassigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P38i_was_deassigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P97i_was_father_for', _, X1],O1,_) \ fact(['a1:E67_Birth', X1],add,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P4_has_time-span', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Formation', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:agent', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P137_exemplifies', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P137i_is_exemplified_by', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P80_end_is_qualified_by', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:knows', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Disbanding', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P148i_is_component_of', X, Y],O1,_), fact(['a1:P148i_is_component_of', Y, Z],O2,_) \ fact(['a1:P148i_is_component_of', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P148i_is_component_of', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a3:yahooChatID', X, Y],O1,_) \ fact(['a3:nick', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:death', X, Y],O1,_) \ fact(['a2:event', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:event', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P89_falls_within', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P115_finishes', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:death', _, X1],O1,_) \ fact(['a2:Death', X1],add,U) <=> member(del,[O1]) | fact(['a2:Death', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P35i_was_identified_by', X, Y],O1,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P111_added', X, _],O1,_) \ fact(['a1:E79_Part_Addition', X],add,U) <=> member(del,[O1]) | fact(['a1:E79_Part_Addition', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P37i_was_assigned_by', X, _],O1,_) \ fact(['a1:E42_Identifier', X],add,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P42_assigned', X, _],O1,_) \ fact(['a1:E17_Type_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E17_Type_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E73_Information_Object', X],O1,_) \ fact(['a1:E90_Symbolic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P110_augmented', X, Y],O1,_) \ fact(['a1:P31_has_modified', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P78i_identifies', X, Y],O1,_) \ fact(['a1:P1i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P91i_is_unit_of', _, X1],O1,_) \ fact(['a1:E54_Dimension', X1],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P146_separated_from', X, _],O1,_) \ fact(['a1:E86_Leaving', X],add,U) <=> member(del,[O1]) | fact(['a1:E86_Leaving', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:position', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P86i_contains', _, X1],O1,_) \ fact(['a1:E52_Time-Span', X1],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:mbox_sha1sum', Y1, X],O1,_), fact(['a3:mbox_sha1sum', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:E74_Group', X],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P37i_was_assigned_by', X, Y],O1,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:yahooChatID', _, X1],O1,_) \ fact(['rdfs:Literal', X1],add,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P127i_has_narrower_term', X, Y],O1,_), fact(['a1:P127i_has_narrower_term', Y, Z],O2,_) \ fact(['a1:P127i_has_narrower_term', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P127i_has_narrower_term', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a3:member', _, X1],O1,_) \ fact(['a3:Agent', X1],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P21i_was_purpose_of', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E29_Design_or_Procedure', X],O1,_) \ fact(['a1:E73_Information_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Execution', X],O1,_) \ fact(['a2:Death', X],add,U) <=> member(del,[O1]) | fact(['a2:Death', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P71_lists', Y, X],O1,_) \ fact(['a1:P71i_is_listed_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P71i_is_listed_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P71i_is_listed_in', Y, X],O1,_) \ fact(['a1:P71_lists', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P71_lists', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P84_had_at_most_duration', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P101i_was_use_of', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P142_used_constituent', Y, X],O1,_) \ fact(['a1:P142i_was_used_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P142i_was_used_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P142i_was_used_in', Y, X],O1,_) \ fact(['a1:P142_used_constituent', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P142_used_constituent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:position', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P147i_was_curated_by', _, X1],O1,_) \ fact(['a1:E87_Curation_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E87_Curation_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P49_has_former_or_current_keeper', Y, X],O1,_) \ fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P49i_is_former_or_current_keeper_of', Y, X],O1,_) \ fact(['a1:P49_has_former_or_current_keeper', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P38i_was_deassigned_by', X, Y],O1,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P145i_left_by', _, X1],O1,_) \ fact(['a1:E86_Leaving', X1],add,U) <=> member(del,[O1]) | fact(['a1:E86_Leaving', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P91_has_unit', X, X2],O1,_), fact(['a1:P91_has_unit', X, X1],O2,_), fact(['a1:E54_Dimension', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a2:relationship', _, X1],O1,_) \ fact(['a2:Relationship', X1],add,U) <=> member(del,[O1]) | fact(['a2:Relationship', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73i_is_translation_of', X, _],O1,_) \ fact(['a1:E33_Linguistic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P75i_is_possessed_by', X, _],O1,_) \ fact(['a1:E30_Right', X],add,U) <=> member(del,[O1]) | fact(['a1:E30_Right', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:principal', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:OnlineEcommerceAccount', X],O1,_) \ fact(['a3:OnlineAccount', X],add,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P2i_is_type_of', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E31_Document', X],O1,_) \ fact(['a1:P_E31_Document', X, X],add,U) <=> member(del,[O1]) | fact(['a1:P_E31_Document', X, X],del,U), applied_rules(1,del).
phase(1), fact(['a2:principal', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P144i_gained_member_by', X, _],O1,_) \ fact(['a1:E74_Group', X],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P74i_is_current_or_former_residence_of', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:holdsAccount', _, X1],O1,_) \ fact(['a3:OnlineAccount', X1],add,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P90_has_value', X, _],O1,_) \ fact(['a1:E54_Dimension', X],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:weblog', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41i_was_classified_by', _, X1],O1,_) \ fact(['a1:E17_Type_Assignment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E17_Type_Assignment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P123_resulted_in', X, Y],O1,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P93_took_out_of_existence', X, _],O1,_) \ fact(['a1:E64_End_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:concurrentEvent', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P49i_is_former_or_current_keeper_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['rdfs:Datatype', X],O1,_) \ fact(['rdfs:Class', X],add,U) <=> member(del,[O1]) | fact(['rdfs:Class', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P111i_was_added_by', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:father', X, _],O1,_), fact(['a2:mother', X, _],O2,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1,O2]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P125i_was_type_of_object_used_in', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P145_separated', X, Y],O1,_) \ fact(['a1:P11_had_participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P57_has_number_of_parts', X, _],O1,_) \ fact(['a1:E19_Physical_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Investiture', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P147_curated', X, _],O1,_) \ fact(['a1:E87_Curation_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E87_Curation_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P138i_has_representation', _, X1],O1,_) \ fact(['a1:E36_Visual_Item', X1],add,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67i_is_referred_to_by', Y, X],O1,_) \ fact(['a1:P67_refers_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67_refers_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', Y, X],O1,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P67i_is_referred_to_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P50_has_current_keeper', Y, X],O1,_) \ fact(['a1:P50i_is_current_keeper_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P50i_is_current_keeper_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P50i_is_current_keeper_of', Y, X],O1,_) \ fact(['a1:P50_has_current_keeper', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P50_has_current_keeper', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P138_represents', X, _],O1,_) \ fact(['a1:E36_Visual_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73_has_translation', X, Y],O1,_) \ fact(['a1:P130_shows_features_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P130_shows_features_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:concurrentEvent', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a5:PeriodOfTime', X],O1,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],add,U) <=> member(del,[O1]) | fact(['a5:LocationPeriodOrJurisdiction', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P143i_was_joined_by', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P121_overlaps_with', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P34i_was_assessed_by', Y, X],O1,_) \ fact(['a1:P34_concerned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P34_concerned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P34_concerned', Y, X],O1,_) \ fact(['a1:P34i_was_assessed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P34i_was_assessed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108i_was_produced_by', _, X1],O1,_) \ fact(['a1:E12_Production', X1],add,U) <=> member(del,[O1]) | fact(['a1:E12_Production', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P140i_was_attributed_by', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P117i_includes', X, Y],O1,_), fact(['a1:P117i_includes', Y, Z],O2,_) \ fact(['a1:P117i_includes', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P117i_includes', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P102i_is_title_of', X, Y],O1,_) \ fact(['a1:P1i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X0, X1],O1,_), fact(['a1:P67_refers_to', X2, X1],O2,_) \ fact(['a1:referToSame', X0, X2],add,U) <=> member(del,[O1,O2]) | fact(['a1:referToSame', X0, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:E71_Man-Made_Thing', X],O1,_) \ fact(['a1:E70_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P141_assigned', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P74_has_current_or_former_residence', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P84i_was_maximum_duration_of', Y, X],O1,_) \ fact(['a1:P84_had_at_most_duration', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P84_had_at_most_duration', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P84_had_at_most_duration', Y, X],O1,_) \ fact(['a1:P84i_was_maximum_duration_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P84i_was_maximum_duration_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:weblog', X, Y],O1,_) \ fact(['a3:page', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E77_Persistent_Item', X],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P104i_applies_to', Y, X],O1,_) \ fact(['a1:P104_is_subject_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P104_is_subject_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P104_is_subject_to', Y, X],O1,_) \ fact(['a1:P104i_applies_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P104i_applies_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E87_Curation_Activity', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:isPrimaryTopicOf', Y1, X],O1,_), fact(['a3:isPrimaryTopicOf', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a2:Relationship', X],O1,_) \ fact(['a6:Relationship', X],add,U) <=> member(del,[O1]) | fact(['a6:Relationship', X],del,U), applied_rules(1,del).
phase(1), fact(['a6:Relationship', X],O1,_) \ fact(['a2:Relationship', X],add,U) <=> member(del,[O1]) | fact(['a2:Relationship', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:logo', Y1, X],O1,_), fact(['a3:logo', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P92_brought_into_existence', X, _],O1,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E48_Place_Name', X],O1,_) \ fact(['a1:E44_Place_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P143i_was_joined_by', X, Y],O1,_) \ fact(['a1:P11i_participated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E2_Temporal_Entity', X],O1,_), fact(['a1:E77_Persistent_Item', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P54i_is_current_permanent_location_of', _, X1],O1,_) \ fact(['a1:E19_Physical_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P145_separated', X, X2],O1,_), fact(['a1:P145_separated', X, X1],O2,_), fact(['a1:E86_Leaving', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P99i_was_dissolved_by', X, Y],O1,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:Inauguration', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P125_used_object_of_type', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P25i_moved_by', _, X1],O1,_) \ fact(['a1:E9_Move', X1],add,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P72i_is_language_of', Y, X],O1,_) \ fact(['a1:P72_has_language', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P72_has_language', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P72_has_language', Y, X],O1,_) \ fact(['a1:P72i_is_language_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P72i_is_language_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P101i_was_use_of', _, X1],O1,_) \ fact(['a1:E70_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P123i_resulted_from', X, _],O1,_) \ fact(['a1:E77_Persistent_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E66_Formation', X],O1,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P1i_identifies', X, _],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a5:SizeOrDuration', X],O1,_) \ fact(['a5:MediaTypeOrExtent', X],add,U) <=> member(del,[O1]) | fact(['a5:MediaTypeOrExtent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P92_brought_into_existence', Y, X],O1,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P92i_was_brought_into_existence_by', Y, X],O1,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:icqChatID', Y1, X],O1,_), fact(['a3:icqChatID', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a3:OnlineChatAccount', X],O1,_) \ fact(['a3:OnlineAccount', X],add,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P97_from_father', _, X1],O1,_) \ fact(['a1:E21_Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P65i_is_shown_by', _, X1],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P86i_contains', X, Y],O1,_), fact(['a1:P86i_contains', Y, Z],O2,_) \ fact(['a1:P86i_contains', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P86i_contains', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a2:Coronation', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P148i_is_component_of', X, _],O1,_) \ fact(['a1:E89_Propositional_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P34i_was_assessed_by', _, X1],O1,_) \ fact(['a1:E14_Condition_Assessment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E14_Condition_Assessment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P49_has_former_or_current_keeper', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P43i_is_dimension_of', _, X1],O1,_) \ fact(['a1:E70_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P143i_was_joined_by', _, X1],O1,_) \ fact(['a1:E85_Joining', X1],add,U) <=> member(del,[O1]) | fact(['a1:E85_Joining', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P21_had_general_purpose', Y, X],O1,_) \ fact(['a1:P21i_was_purpose_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P21i_was_purpose_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P21i_was_purpose_of', Y, X],O1,_) \ fact(['a1:P21_had_general_purpose', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P21_had_general_purpose', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P87i_identifies', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Funeral', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P11i_participated_in', Y, X],O1,_) \ fact(['a1:P11_had_participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P11_had_participant', Y, X],O1,_) \ fact(['a1:P11i_participated_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11i_participated_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P111_added', Y, X],O1,_) \ fact(['a1:P111i_was_added_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P111i_was_added_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P111i_was_added_by', Y, X],O1,_) \ fact(['a1:P111_added', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P111_added', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E73_Information_Object', X],O1,_) \ fact(['a1:P_E73_Information_Object', X, X],add,U) <=> member(del,[O1]) | fact(['a1:P_E73_Information_Object', X, X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P113_removed', X, _],O1,_) \ fact(['a1:E80_Part_Removal', X],add,U) <=> member(del,[O1]) | fact(['a1:E80_Part_Removal', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P142i_was_used_in', X, Y],O1,_) \ fact(['a1:P16i_was_used_for', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:page', Y, X],O1,_) \ fact(['a3:topic', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:topic', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:topic', Y, X],O1,_) \ fact(['a3:page', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:page', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135i_was_created_by', X, Y],O1,_) \ fact(['a1:P94i_was_created_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P94i_was_created_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P101_had_as_general_use', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:homepage', X, Y],O1,_) \ fact(['a3:isPrimaryTopicOf', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:isPrimaryTopicOf', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P127i_has_narrower_term', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P25i_moved_by', Y, X],O1,_) \ fact(['a1:P25_moved', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P25_moved', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P25_moved', Y, X],O1,_) \ fact(['a1:P25i_moved_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P25i_moved_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P3_has_note', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P38_deassigned', X, Y],O1,_) \ fact(['a1:P141_assigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E42_Identifier', X],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P148_has_component', X, _],O1,_) \ fact(['a1:E89_Propositional_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P122_borders_with', Y, X],O1,_) \ fact(['a1:P122_borders_with', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P122_borders_with', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P59i_is_located_on_or_within', X, X2],O1,_), fact(['a1:P59i_is_located_on_or_within', X, X1],O2,_), fact(['a1:E53_Place', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P26i_was_destination_of', _, X1],O1,_) \ fact(['a1:E9_Move', X1],add,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:accountServiceHomepage', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P68_foresees_use_of', Y, X],O1,_) \ fact(['a1:P68i_use_foreseen_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P68i_use_foreseen_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P68i_use_foreseen_by', Y, X],O1,_) \ fact(['a1:P68_foresees_use_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P68_foresees_use_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:eventInterval', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P128_carries', _, X1],O1,_) \ fact(['a1:E73_Information_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E65_Creation', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:mbox_sha1sum', _, X1],O1,_) \ fact(['rdfs:Literal', X1],add,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:interval', X, _],O1,_) \ fact(['a2:Relationship', X],add,U) <=> member(del,[O1]) | fact(['a2:Relationship', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P67_refers_to', X, Y],O1,_), fact(['a1:P67_refers_to', Y, Z],O2,_) \ fact(['a1:P67_refers_to', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P67_refers_to', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:E12_Production', X],O1,_) \ fact(['a1:E11_Modification', X],add,U) <=> member(del,[O1]) | fact(['a1:E11_Modification', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P12i_was_present_at', X, _],O1,_) \ fact(['a1:E77_Persistent_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P48_has_preferred_identifier', X, X2],O1,_), fact(['a1:P48_has_preferred_identifier', X, X1],O2,_), fact(['a1:E1_CRM_Entity', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P148_has_component', _, X1],O1,_) \ fact(['a1:E89_Propositional_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P12_occurred_in_the_presence_of', _, X1],O1,_) \ fact(['a1:E77_Persistent_Item', X1],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P31i_was_modified_by', X, _],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P94i_was_created_by', X, _],O1,_) \ fact(['a1:E28_Conceptual_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P107_has_current_or_former_member', X, _],O1,_) \ fact(['a1:E74_Group', X],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P103i_was_intention_of', X, _],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P12i_was_present_at', _, X1],O1,_) \ fact(['a1:E5_Event', X1],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P42_assigned', X, Y],O1,_) \ fact(['a1:P141_assigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P41_classified', X, _],O1,_) \ fact(['a1:E17_Type_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E17_Type_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P62i_is_depicted_by', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P4i_is_time-span_of', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P106i_forms_part_of', X, _],O1,_) \ fact(['a1:E90_Symbolic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E26_Physical_Feature', X],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:immediatelyPrecedingEvent', X, Y],O1,_) \ fact(['a2:precedingEvent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:precedingEvent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:Resignation', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:BarMitzvah', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E2_Temporal_Entity', X],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P123i_resulted_from', X, Y],O1,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E54_Dimension', X],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P131i_identifies', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Baptism', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P122_borders_with', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P94_has_created', X, Y],O1,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P115_finishes', X, Y],O1,_), fact(['a1:P115_finishes', Y, Z],O2,_) \ fact(['a1:P115_finishes', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P115_finishes', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a3:openid', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P1i_identifies', Y, X],O1,_) \ fact(['a1:P1_is_identified_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1_is_identified_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P1_is_identified_by', Y, X],O1,_) \ fact(['a1:P1i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P52_has_current_owner', X, Y],O1,_) \ fact(['a1:P51_has_former_or_current_owner', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P102i_is_title_of', Y, X],O1,_) \ fact(['a1:P102_has_title', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P102_has_title', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P102_has_title', Y, X],O1,_) \ fact(['a1:P102i_is_title_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P102i_is_title_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P59_has_section', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P79_beginning_is_qualified_by', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:jabberID', Y1, X],O1,_), fact(['a3:jabberID', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P140_assigned_attribute_to', Y, X],O1,_) \ fact(['a1:P140i_was_attributed_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P140i_was_attributed_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P140i_was_attributed_by', Y, X],O1,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98_brought_into_life', _, X1],O1,_) \ fact(['a1:E21_Person', X1],add,U) <=> member(del,[O1]) | fact(['a1:E21_Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P8_took_place_on_or_within', X, _],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P8_took_place_on_or_within', _, X1],O1,_) \ fact(['a1:E19_Physical_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E22_Man-Made_Object', X],O1,_) \ fact(['a1:E19_Physical_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P114_is_equal_in_time_to', X, Y],O1,_), fact(['a1:P114_is_equal_in_time_to', Y, Z],O2,_) \ fact(['a1:P114_is_equal_in_time_to', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P114_is_equal_in_time_to', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E73_Information_Object', X0, X1],O1,_), fact(['a1:referredBySame', X1, X2],O2,_), fact(['a1:P_E73_Information_Object', X2, X3],O3,_) \ fact(['a1:relatedInformationObjects', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedInformationObjects', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a2:Burial', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P140i_was_attributed_by', _, X1],O1,_) \ fact(['a1:E13_Attribute_Assignment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E53_Place', X],O1,_) \ fact(['a1:P_E53_Place', X, X],add,U) <=> member(del,[O1]) | fact(['a1:P_E53_Place', X, X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P23_transferred_title_from', Y, X],O1,_) \ fact(['a1:P23i_surrendered_title_through', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P23i_surrendered_title_through', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P23i_surrendered_title_through', Y, X],O1,_) \ fact(['a1:P23_transferred_title_from', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P23_transferred_title_from', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27i_was_origin_of', X, Y],O1,_), fact(['a1:P27i_was_origin_of', Y, Z],O2,_) \ fact(['a1:P27i_was_origin_of', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P27i_was_origin_of', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P33i_was_used_by', X, _],O1,_) \ fact(['a1:E29_Design_or_Procedure', X],add,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P74i_is_current_or_former_residence_of', Y, X],O1,_) \ fact(['a1:P74_has_current_or_former_residence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P74_has_current_or_former_residence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P74_has_current_or_former_residence', Y, X],O1,_) \ fact(['a1:P74i_is_current_or_former_residence_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P74i_is_current_or_former_residence_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E90_Symbolic_Object', X],O1,_) \ fact(['a1:E28_Conceptual_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P107_has_current_or_former_member', Y, X],O1,_) \ fact(['a1:P107i_is_current_or_former_member_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P107i_is_current_or_former_member_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P107i_is_current_or_former_member_of', Y, X],O1,_) \ fact(['a1:P107_has_current_or_former_member', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P107_has_current_or_former_member', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P131i_identifies', X, Y],O1,_) \ fact(['a1:P1i_identifies', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P1i_identifies', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:keywords', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P87_is_identified_by', _, X1],O1,_) \ fact(['a1:E44_Place_Appellation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E44_Place_Appellation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P15i_influenced', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P109_has_current_or_former_curator', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P141i_was_assigned_by', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E16_Measurement', X],O1,_) \ fact(['a1:E13_Attribute_Assignment', X],add,U) <=> member(del,[O1]) | fact(['a1:E13_Attribute_Assignment', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P124_transformed', _, X1],O1,_) \ fact(['a1:E77_Persistent_Item', X1],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P120i_occurs_after', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E53_Place', X0, X1],O1,_), fact(['a1:P67_refers_to', X1, X2],O2,_), fact(['a1:P_E53_Place', X2, X3],O3,_) \ fact(['a1:relatedPlaces', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedPlaces', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a5:Agent', X],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:Agent', X],O1,_) \ fact(['a5:Agent', X],add,U) <=> member(del,[O1]) | fact(['a5:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P62_depicts', X, _],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P65_shows_visual_item', _, X1],O1,_) \ fact(['a1:E36_Visual_Item', X1],add,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:initiatingEvent', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P11i_participated_in', _, X1],O1,_) \ fact(['a1:E5_Event', X1],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', X, Y],O1,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P136i_supported_type_creation', _, X1],O1,_) \ fact(['a1:E83_Type_Creation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E83_Type_Creation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E55_Type', X],O1,_) \ fact(['a1:E28_Conceptual_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:officiator', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:relatedPlaces', Y, X],O1,_) \ fact(['a1:relatedPlaces', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:relatedPlaces', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P147_curated', Y, X],O1,_) \ fact(['a1:P147i_was_curated_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P147i_was_curated_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P147i_was_curated_by', Y, X],O1,_) \ fact(['a1:P147_curated', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P147_curated', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P53_has_former_or_current_location', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Birth', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:keywords', X, Y],O1,_) \ fact(['a12:subject', X, Y],add,U) <=> member(del,[O1]) | fact(['a12:subject', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P5_consists_of', X, _],O1,_) \ fact(['a1:E3_Condition_State', X],add,U) <=> member(del,[O1]) | fact(['a1:E3_Condition_State', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:icqChatID', X, Y],O1,_) \ fact(['a3:nick', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:nick', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P118i_is_overlapped_in_time_by', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P48_has_preferred_identifier', _, X1],O1,_) \ fact(['a1:E42_Identifier', X1],add,U) <=> member(del,[O1]) | fact(['a1:E42_Identifier', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P44i_is_condition_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P69_is_associated_with', X, _],O1,_) \ fact(['a1:E29_Design_or_Procedure', X],add,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E11_Modification', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P93i_was_taken_out_of_existence_by', Y, X],O1,_) \ fact(['a1:P93_took_out_of_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93_took_out_of_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P93_took_out_of_existence', Y, X],O1,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P109i_is_current_or_former_curator_of', _, X1],O1,_) \ fact(['a1:E78_Collection', X1],add,U) <=> member(del,[O1]) | fact(['a1:E78_Collection', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P76i_provides_access_to', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P94i_was_created_by', X, Y],O1,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E86_Leaving', X],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:Document', X],O1,_), fact(['a3:Project', X],O2,_) \ fact(['owl:Nothing', X],add,U) <=> member(del,[O1,O2]) | fact(['owl:Nothing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P20i_was_purpose_of', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Event', X],O1,_) \ fact(['a13:Event', X],add,U) <=> member(del,[O1]) | fact(['a13:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:birthday', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P143_joined', X, _],O1,_) \ fact(['a1:E85_Joining', X],add,U) <=> member(del,[O1]) | fact(['a1:E85_Joining', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P115_finishes', Y, X],O1,_) \ fact(['a1:P115i_is_finished_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P115i_is_finished_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P115i_is_finished_by', Y, X],O1,_) \ fact(['a1:P115_finishes', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P115_finishes', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P25i_moved_by', X, _],O1,_) \ fact(['a1:E19_Physical_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:witness', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E38_Image', X],O1,_) \ fact(['a1:E36_Visual_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E36_Visual_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P73_has_translation', X, _],O1,_) \ fact(['a1:E33_Linguistic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P26i_was_destination_of', X, Y],O1,_) \ fact(['a1:P7i_witnessed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P7i_witnessed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:weblog', Y1, X],O1,_), fact(['a3:weblog', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P17i_motivated', X, Y],O1,_) \ fact(['a1:P15i_influenced', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P142_used_constituent', _, X1],O1,_) \ fact(['a1:E41_Appellation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P125i_was_type_of_object_used_in', Y, X],O1,_) \ fact(['a1:P125_used_object_of_type', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P125_used_object_of_type', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P125_used_object_of_type', Y, X],O1,_) \ fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:workplaceHomepage', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P134i_was_continued_by', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E89_Propositional_Object', X],O1,_) \ fact(['a1:E28_Conceptual_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E28_Conceptual_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:skypeID', _, X1],O1,_) \ fact(['rdfs:Literal', X1],add,U) <=> member(del,[O1]) | fact(['rdfs:Literal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:isPrimaryTopicOf', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P88_consists_of', Y, X],O1,_) \ fact(['a1:P88i_forms_part_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P88i_forms_part_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P88i_forms_part_of', Y, X],O1,_) \ fact(['a1:P88_consists_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P88_consists_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:relationship', Y, X],O1,_) \ fact(['a2:participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:participant', Y, X],O1,_) \ fact(['a2:relationship', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:relationship', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P21i_was_purpose_of', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P17_was_motivated_by', _, X1],O1,_) \ fact(['a1:E1_CRM_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P34_concerned', X, Y],O1,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P140_assigned_attribute_to', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P25_moved', X, _],O1,_) \ fact(['a1:E9_Move', X],add,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Accession', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:interest', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E58_Measurement_Unit', X],O1,_) \ fact(['a1:E55_Type', X],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P105i_has_right_on', Y, X],O1,_) \ fact(['a1:P105_right_held_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P105_right_held_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P105_right_held_by', Y, X],O1,_) \ fact(['a1:P105i_has_right_on', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P105i_has_right_on', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:Assassination', X],O1,_) \ fact(['a2:Murder', X],add,U) <=> member(del,[O1]) | fact(['a2:Murder', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P108_has_produced', X, _],O1,_) \ fact(['a1:E12_Production', X],add,U) <=> member(del,[O1]) | fact(['a1:E12_Production', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E35_Title', X],O1,_) \ fact(['a1:E33_Linguistic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:witness', X, Y],O1,_) \ fact(['a2:spectator', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:spectator', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E83_Type_Creation', X],O1,_) \ fact(['a1:E65_Creation', X],add,U) <=> member(del,[O1]) | fact(['a1:E65_Creation', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:mother', X, Y1],O1,_), fact(['a2:mother', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P32i_was_technique_of', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P65_shows_visual_item', X, Y],O1,_) \ fact(['a1:P128_carries', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P128_carries', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P69_is_associated_with', _, X1],O1,_) \ fact(['a1:E29_Design_or_Procedure', X1],add,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P135_created_type', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P22_transferred_title_to', X, Y],O1,_) \ fact(['a1:P14_carried_out_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14_carried_out_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P49_has_former_or_current_keeper', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P104i_applies_to', X, _],O1,_) \ fact(['a1:E30_Right', X],add,U) <=> member(del,[O1]) | fact(['a1:E30_Right', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P86i_contains', Y, X],O1,_) \ fact(['a1:P86_falls_within', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P86_falls_within', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P86_falls_within', Y, X],O1,_) \ fact(['a1:P86i_contains', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P86i_contains', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P11_had_participant', X, _],O1,_) \ fact(['a1:E5_Event', X],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P2i_is_type_of', Y, X],O1,_) \ fact(['a1:P2_has_type', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P2_has_type', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P2_has_type', Y, X],O1,_) \ fact(['a1:P2i_is_type_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P2i_is_type_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:workplaceHomepage', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E52_Time-Span', X],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', _, X1],O1,_) \ fact(['a1:E6_Destruction', X1],add,U) <=> member(del,[O1]) | fact(['a1:E6_Destruction', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P129_is_about', X, _],O1,_) \ fact(['a1:E89_Propositional_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P103i_was_intention_of', Y, X],O1,_) \ fact(['a1:P103_was_intended_for', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P103_was_intended_for', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P103_was_intended_for', Y, X],O1,_) \ fact(['a1:P103i_was_intention_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P103i_was_intention_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:birthday', X, Y1],O1,_), fact(['a3:birthday', X, Y2],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:E34_Inscription', X],O1,_) \ fact(['a1:E33_Linguistic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E33_Linguistic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P21_had_general_purpose', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E69_Death', X],O1,_) \ fact(['a1:E64_End_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E18_Physical_Thing', X],O1,_) \ fact(['a1:E72_Legal_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P_E53_Place', X0, X1],O1,_), fact(['a1:referToSame', X1, X2],O2,_), fact(['a1:P_E53_Place', X2, X3],O3,_) \ fact(['a1:relatedPlaces', X0, X3],add,U) <=> member(del,[O1,O2,O3]) | fact(['a1:relatedPlaces', X0, X3],del,U), applied_rules(1,del).
phase(1), fact(['a1:P143_joined', X, Y],O1,_) \ fact(['a1:P11_had_participant', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P11_had_participant', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P35_has_identified', X, Y],O1,_) \ fact(['a1:P141_assigned', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141_assigned', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:employer', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P145_separated', X, _],O1,_) \ fact(['a1:E86_Leaving', X],add,U) <=> member(del,[O1]) | fact(['a1:E86_Leaving', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98i_was_born', X, X2],O1,_), fact(['a1:P98i_was_born', X, X1],O2,_), fact(['a1:E21_Person', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P114_is_equal_in_time_to', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P20i_was_purpose_of', X, _],O1,_) \ fact(['a1:E5_Event', X],add,U) <=> member(del,[O1]) | fact(['a1:E5_Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P38i_was_deassigned_by', _, X1],O1,_) \ fact(['a1:E15_Identifier_Assignment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P83_had_at_least_duration', _, X1],O1,_) \ fact(['a1:E54_Dimension', X1],add,U) <=> member(del,[O1]) | fact(['a1:E54_Dimension', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:page', _, X1],O1,_) \ fact(['a3:Document', X1],add,U) <=> member(del,[O1]) | fact(['a3:Document', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:precedingEvent', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P134i_was_continued_by', X, Y],O1,_) \ fact(['a1:P15i_influenced', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15i_influenced', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E67_Birth', X],O1,_) \ fact(['a1:E63_Beginning_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E63_Beginning_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P133_is_separated_from', _, X1],O1,_) \ fact(['a1:E4_Period', X1],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:pastProject', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:concludingEvent', X, Y],O1,_) \ fact(['owl:differentFrom', X, Y],add,U) <=> member(del,[O1]) | fact(['owl:differentFrom', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P19_was_intended_use_of', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E35_Title', X],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98_brought_into_life', X, _],O1,_) \ fact(['a1:E67_Birth', X],add,U) <=> member(del,[O1]) | fact(['a1:E67_Birth', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P68_foresees_use_of', _, X1],O1,_) \ fact(['a1:E57_Material', X1],add,U) <=> member(del,[O1]) | fact(['a1:E57_Material', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P33_used_specific_technique', X, Y],O1,_) \ fact(['a1:P16_used_specific_object', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:precedingEvent', _, X1],O1,_) \ fact(['a2:Event', X1],add,U) <=> member(del,[O1]) | fact(['a2:Event', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P17i_motivated', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E68_Dissolution', X],O1,_) \ fact(['a1:E64_End_of_Existence', X],add,U) <=> member(del,[O1]) | fact(['a1:E64_End_of_Existence', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],O1,_) \ fact(['a1:P12i_was_present_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P12i_was_present_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P52i_is_current_owner_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P120_occurs_before', X, Y],O1,_), fact(['a1:P120_occurs_before', Y, Z],O2,_) \ fact(['a1:P120_occurs_before', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P120_occurs_before', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P89i_contains', Y, X],O1,_) \ fact(['a1:P89_falls_within', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P89_falls_within', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P89_falls_within', Y, X],O1,_) \ fact(['a1:P89i_contains', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P89i_contains', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P121_overlaps_with', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P88_consists_of', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P129_is_about', Y, X],O1,_) \ fact(['a1:P129i_is_subject_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P129i_is_subject_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P129i_is_subject_of', Y, X],O1,_) \ fact(['a1:P129_is_about', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P129_is_about', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:state', X, Y],O1,_) \ fact(['a2:agent', X, Y],add,U) <=> member(del,[O1]) | fact(['a2:agent', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P50i_is_current_keeper_of', X, Y],O1,_) \ fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:precedingEvent', X, Y],O1,_), fact(['a2:precedingEvent', Y, Z],O2,_) \ fact(['a2:precedingEvent', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a2:precedingEvent', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a3:member', X, _],O1,_) \ fact(['a3:Group', X],add,U) <=> member(del,[O1]) | fact(['a3:Group', X],del,U), applied_rules(1,del).
phase(1), fact(['rdfs:Class', X],O1,_) \ fact(['rdfs:Resource', X],add,U) <=> member(del,[O1]) | fact(['rdfs:Resource', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P4i_is_time-span_of', Y, X],O1,_) \ fact(['a1:P4_has_time-span', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P4_has_time-span', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P4_has_time-span', Y, X],O1,_) \ fact(['a1:P4i_is_time-span_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P4i_is_time-span_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P105_right_held_by', X, _],O1,_) \ fact(['a1:E72_Legal_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E72_Legal_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:aimChatID', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P122_borders_with', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:OnlineGamingAccount', X],O1,_) \ fact(['a3:OnlineAccount', X],add,U) <=> member(del,[O1]) | fact(['a3:OnlineAccount', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P26_moved_to', X, Y],O1,_) \ fact(['a1:P7_took_place_at', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P7_took_place_at', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P31_has_modified', _, X1],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P83_had_at_least_duration', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:GroupEvent', X],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P86_falls_within', _, X1],O1,_) \ fact(['a1:E52_Time-Span', X1],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:yahooChatID', Y1, X],O1,_), fact(['a3:yahooChatID', Y2, X],O2,_) \ fact(['owl:sameAs', Y1, Y2],add,U) <=> member(del,[O1,O2]) | fact(['owl:sameAs', Y1, Y2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P106i_forms_part_of', Y, X],O1,_) \ fact(['a1:P106_is_composed_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P106_is_composed_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P106_is_composed_of', Y, X],O1,_) \ fact(['a1:P106i_forms_part_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P106i_forms_part_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P40i_was_observed_in', X, Y],O1,_) \ fact(['a1:P141i_was_assigned_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P141i_was_assigned_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P133_is_separated_from', Y, X],O1,_) \ fact(['a1:P133_is_separated_from', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P133_is_separated_from', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P130_shows_features_of', X, _],O1,_) \ fact(['a1:E70_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E70_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Interval', X],O1,_) \ fact(['a14:ProperInterval', X],add,U) <=> member(del,[O1]) | fact(['a14:ProperInterval', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P52i_is_current_owner_of', Y, X],O1,_) \ fact(['a1:P52_has_current_owner', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P52_has_current_owner', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P52_has_current_owner', Y, X],O1,_) \ fact(['a1:P52i_is_current_owner_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P52i_is_current_owner_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P100i_died_in', _, X1],O1,_) \ fact(['a1:E69_Death', X1],add,U) <=> member(del,[O1]) | fact(['a1:E69_Death', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:maker', Y, X],O1,_) \ fact(['a3:made', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:made', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a3:made', Y, X],O1,_) \ fact(['a3:maker', X, Y],add,U) <=> member(del,[O1]) | fact(['a3:maker', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P124_transformed', X, _],O1,_) \ fact(['a1:E81_Transformation', X],add,U) <=> member(del,[O1]) | fact(['a1:E81_Transformation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E82_Actor_Appellation', X],O1,_) \ fact(['a1:E41_Appellation', X],add,U) <=> member(del,[O1]) | fact(['a1:E41_Appellation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P32_used_general_technique', _, X1],O1,_) \ fact(['a1:E55_Type', X1],add,U) <=> member(del,[O1]) | fact(['a1:E55_Type', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P123i_resulted_from', Y, X],O1,_) \ fact(['a1:P123_resulted_in', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P123_resulted_in', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P123_resulted_in', Y, X],O1,_) \ fact(['a1:P123i_resulted_from', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P123i_resulted_from', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P10i_contains', X, Y],O1,_), fact(['a1:P10i_contains', Y, Z],O2,_) \ fact(['a1:P10i_contains', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P10i_contains', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P51i_is_former_or_current_owner_of', Y, X],O1,_) \ fact(['a1:P51_has_former_or_current_owner', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P51_has_former_or_current_owner', Y, X],O1,_) \ fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P142i_was_used_in', _, X1],O1,_) \ fact(['a1:E15_Identifier_Assignment', X1],add,U) <=> member(del,[O1]) | fact(['a1:E15_Identifier_Assignment', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Death', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P98_brought_into_life', X, Y],O1,_) \ fact(['a1:P92_brought_into_existence', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P92_brought_into_existence', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P93i_was_taken_out_of_existence_by', X, _],O1,_) \ fact(['a1:E77_Persistent_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39_measured', Y, X],O1,_) \ fact(['a1:P39i_was_measured_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P39i_was_measured_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P39i_was_measured_by', Y, X],O1,_) \ fact(['a1:P39_measured', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P39_measured', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P116i_is_started_by', _, X1],O1,_) \ fact(['a1:E2_Temporal_Entity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E41_Appellation', X],O1,_) \ fact(['a1:E90_Symbolic_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P106i_forms_part_of', X, Y],O1,_), fact(['a1:P106i_forms_part_of', Y, Z],O2,_) \ fact(['a1:P106i_forms_part_of', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P106i_forms_part_of', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:P50_has_current_keeper', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P9_consists_of', X, _],O1,_) \ fact(['a1:E4_Period', X],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P144_joined_with', _, X1],O1,_) \ fact(['a1:E74_Group', X1],add,U) <=> member(del,[O1]) | fact(['a1:E74_Group', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:publications', X, _],O1,_) \ fact(['a3:Person', X],add,U) <=> member(del,[O1]) | fact(['a3:Person', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P46_is_composed_of', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P59_has_section', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:E36_Visual_Item', X],O1,_) \ fact(['a1:E73_Information_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E73_Information_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P112i_was_diminished_by', _, X1],O1,_) \ fact(['a1:E80_Part_Removal', X1],add,U) <=> member(del,[O1]) | fact(['a1:E80_Part_Removal', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P11i_participated_in', X, _],O1,_) \ fact(['a1:E39_Actor', X],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P78_is_identified_by', X, _],O1,_) \ fact(['a1:E52_Time-Span', X],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P34_concerned', _, X1],O1,_) \ fact(['a1:E18_Physical_Thing', X1],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P112i_was_diminished_by', X, _],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P136i_supported_type_creation', X, _],O1,_) \ fact(['a1:E1_CRM_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E1_CRM_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P144i_gained_member_by', Y, X],O1,_) \ fact(['a1:P144_joined_with', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P144_joined_with', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P144_joined_with', Y, X],O1,_) \ fact(['a1:P144i_gained_member_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P144i_gained_member_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:Cremation', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P119_meets_in_time_with', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Marriage', X],O1,_) \ fact(['a7:WeddingEvent_Generic', X],add,U) <=> member(del,[O1]) | fact(['a7:WeddingEvent_Generic', X],del,U), applied_rules(1,del).
phase(1), fact(['a7:WeddingEvent_Generic', X],O1,_) \ fact(['a2:Marriage', X],add,U) <=> member(del,[O1]) | fact(['a2:Marriage', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', _, X1],O1,_) \ fact(['a1:E7_Activity', X1],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:Image', X],O1,_) \ fact(['a3:Document', X],add,U) <=> member(del,[O1]) | fact(['a3:Document', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P143_joined', Y, X],O1,_) \ fact(['a1:P143i_was_joined_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P143i_was_joined_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P143i_was_joined_by', Y, X],O1,_) \ fact(['a1:P143_joined', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P143_joined', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P24i_changed_ownership_through', _, X1],O1,_) \ fact(['a1:E8_Acquisition', X1],add,U) <=> member(del,[O1]) | fact(['a1:E8_Acquisition', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P115i_is_finished_by', X, _],O1,_) \ fact(['a1:E2_Temporal_Entity', X],add,U) <=> member(del,[O1]) | fact(['a1:E2_Temporal_Entity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P103_was_intended_for', X, _],O1,_) \ fact(['a1:E71_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E71_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P53i_is_former_or_current_location_of', X, _],O1,_) \ fact(['a1:E53_Place', X],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P128_carries', X, _],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a5:LicenseDocument', X],O1,_) \ fact(['a5:RightsStatement', X],add,U) <=> member(del,[O1]) | fact(['a5:RightsStatement', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P68_foresees_use_of', X, _],O1,_) \ fact(['a1:E29_Design_or_Procedure', X],add,U) <=> member(del,[O1]) | fact(['a1:E29_Design_or_Procedure', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P89i_contains', _, X1],O1,_) \ fact(['a1:E53_Place', X1],add,U) <=> member(del,[O1]) | fact(['a1:E53_Place', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P20_had_specific_purpose', X, _],O1,_) \ fact(['a1:E7_Activity', X],add,U) <=> member(del,[O1]) | fact(['a1:E7_Activity', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P46_is_composed_of', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P7i_witnessed', _, X1],O1,_) \ fact(['a1:E4_Period', X1],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:Naturalization', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P23i_surrendered_title_through', X, Y],O1,_) \ fact(['a1:P14i_performed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:E30_Right', X],O1,_) \ fact(['a1:E89_Propositional_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E89_Propositional_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P9_consists_of', _, X1],O1,_) \ fact(['a1:E4_Period', X1],add,U) <=> member(del,[O1]) | fact(['a1:E4_Period', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P106_is_composed_of', _, X1],O1,_) \ fact(['a1:E90_Symbolic_Object', X1],add,U) <=> member(del,[O1]) | fact(['a1:E90_Symbolic_Object', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:tipjar', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a3:account', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E70_Thing', X],O1,_) \ fact(['a1:E77_Persistent_Item', X],add,U) <=> member(del,[O1]) | fact(['a1:E77_Persistent_Item', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P22i_acquired_title_through', X, Y],O1,_) \ fact(['a1:P14i_performed', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P14i_performed', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P27_moved_from', X, _],O1,_) \ fact(['a1:E9_Move', X],add,U) <=> member(del,[O1]) | fact(['a1:E9_Move', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P105_right_held_by', _, X1],O1,_) \ fact(['a1:E39_Actor', X1],add,U) <=> member(del,[O1]) | fact(['a1:E39_Actor', X1],del,U), applied_rules(1,del).
phase(1), fact(['a3:icqChatID', X, _],O1,_) \ fact(['a3:Agent', X],add,U) <=> member(del,[O1]) | fact(['a3:Agent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:E78_Collection', X],O1,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P13i_was_destroyed_by', X, X2],O1,_), fact(['a1:P13i_was_destroyed_by', X, X1],O2,_), fact(['a1:E18_Physical_Thing', X],O3,_) \ fact(['owl:sameAs', X1, X2],add,U) <=> member(del,[O1,O2,O3]) | fact(['owl:sameAs', X1, X2],del,U), applied_rules(1,del).
phase(1), fact(['a1:P136_was_based_on', X, Y],O1,_) \ fact(['a1:P15_was_influenced_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P15_was_influenced_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16i_was_used_for', Y, X],O1,_) \ fact(['a1:P16_used_specific_object', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P16_used_specific_object', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P16_used_specific_object', Y, X],O1,_) \ fact(['a1:P16i_was_used_for', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P88_consists_of', X, Y],O1,_), fact(['a1:P88_consists_of', Y, Z],O2,_) \ fact(['a1:P88_consists_of', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P88_consists_of', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a15:Performance', X],O1,_) \ fact(['a2:Performance', X],add,U) <=> member(del,[O1]) | fact(['a2:Performance', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:Performance', X],O1,_) \ fact(['a15:Performance', X],add,U) <=> member(del,[O1]) | fact(['a15:Performance', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P54_has_current_permanent_location', X, _],O1,_) \ fact(['a1:E19_Physical_Object', X],add,U) <=> member(del,[O1]) | fact(['a1:E19_Physical_Object', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P88i_forms_part_of', X, Y],O1,_), fact(['a1:P88i_forms_part_of', Y, Z],O2,_) \ fact(['a1:P88i_forms_part_of', X, Z],add,U) <=> member(del,[O1,O2]) | fact(['a1:P88i_forms_part_of', X, Z],del,U), applied_rules(1,del).
phase(1), fact(['a1:E25_Man-Made_Feature', X],O1,_) \ fact(['a1:E26_Physical_Feature', X],add,U) <=> member(del,[O1]) | fact(['a1:E26_Physical_Feature', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P94_has_created', X, _],O1,_) \ fact(['a1:E65_Creation', X],add,U) <=> member(del,[O1]) | fact(['a1:E65_Creation', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P128_carries', Y, X],O1,_) \ fact(['a1:P128i_is_carried_by', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P128i_is_carried_by', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P128i_is_carried_by', Y, X],O1,_) \ fact(['a1:P128_carries', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P128_carries', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a2:Emigration', X],O1,_) \ fact(['a2:IndividualEvent', X],add,U) <=> member(del,[O1]) | fact(['a2:IndividualEvent', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P112_diminished', X, Y],O1,_) \ fact(['a1:P31_has_modified', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P31_has_modified', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P33i_was_used_by', X, Y],O1,_) \ fact(['a1:P16i_was_used_for', X, Y],add,U) <=> member(del,[O1]) | fact(['a1:P16i_was_used_for', X, Y],del,U), applied_rules(1,del).
phase(1), fact(['a1:P83i_was_minimum_duration_of', _, X1],O1,_) \ fact(['a1:E52_Time-Span', X1],add,U) <=> member(del,[O1]) | fact(['a1:E52_Time-Span', X1],del,U), applied_rules(1,del).
phase(1), fact(['a2:organization', X, _],O1,_) \ fact(['a2:Event', X],add,U) <=> member(del,[O1]) | fact(['a2:Event', X],del,U), applied_rules(1,del).
phase(1), fact(['a1:P113i_was_removed_by', X, _],O1,_) \ fact(['a1:E18_Physical_Thing', X],add,U) <=> member(del,[O1]) | fact(['a1:E18_Physical_Thing', X],del,U), applied_rules(1,del).
phase(1), fact(['a2:child', _, X1],O1,_) \ fact(['a3:Person', X1],add,U) <=> member(del,[O1]) | fact(['a3:Person', X1],del,U), applied_rules(1,del).
phase(1), fact(['a1:P78_is_identified_by', _, X1],O1,_) \ fact(['a1:E49_Time_Appellation', X1],add,U) <=> member(del,[O1]) | fact(['a1:E49_Time_Appellation', X1],del,U), applied_rules(1,del).
phase(1) <=> phase(2).

% -- re-add deleted facts that still have some alternative derivation --
phase(2), fact(['a1:P22i_acquired_title_through', _, X1],add,_) \ fact(['a1:E8_Acquisition', X1],del,U) <=> true | fact(['a1:E8_Acquisition', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P24_transferred_title_of', X, _],add,_) \ fact(['a1:E8_Acquisition', X],del,U) <=> true | fact(['a1:E8_Acquisition', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P110i_was_augmented_by', _, X1],add,_) \ fact(['a1:E79_Part_Addition', X1],del,U) <=> true | fact(['a1:E79_Part_Addition', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41_classified', X, X2],add,_), fact(['a1:P41_classified', X, X1],add,_), fact(['a1:E17_Type_Assignment', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P33_used_specific_technique', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P116_starts', X, Y],add,_), fact(['a1:P116_starts', Y, Z],add,_) \ fact(['a1:P116_starts', X, Z],del,U) <=> true | fact(['a1:P116_starts', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P124i_was_transformed_by', _, X1],add,_) \ fact(['a1:E81_Transformation', X1],del,U) <=> true | fact(['a1:E81_Transformation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P104_is_subject_to', X, _],add,_) \ fact(['a1:E72_Legal_Object', X],del,U) <=> true | fact(['a1:E72_Legal_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P114_is_equal_in_time_to', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P127_has_broader_term', Y, X],add,_) \ fact(['a1:P127i_has_narrower_term', X, Y],del,U) <=> true | fact(['a1:P127i_has_narrower_term', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P127i_has_narrower_term', Y, X],add,_) \ fact(['a1:P127_has_broader_term', X, Y],del,U) <=> true | fact(['a1:P127_has_broader_term', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:followingEvent', X, Y],add,_), fact(['a2:followingEvent', Y, Z],add,_) \ fact(['a2:followingEvent', X, Z],del,U) <=> true | fact(['a2:followingEvent', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:E34_Inscription', X],add,_) \ fact(['a1:E37_Mark', X],del,U) <=> true | fact(['a1:E37_Mark', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P94i_was_created_by', _, X1],add,_) \ fact(['a1:E65_Creation', X1],del,U) <=> true | fact(['a1:E65_Creation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:aimChatID', _, X1],add,_) \ fact(['rdfs:Literal', X1],del,U) <=> true | fact(['rdfs:Literal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E7_Activity', X],add,_) \ fact(['a1:E5_Event', X],del,U) <=> true | fact(['a1:E5_Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:depiction', _, X1],add,_) \ fact(['a3:Image', X1],del,U) <=> true | fact(['a3:Image', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P23_transferred_title_from', X, _],add,_) \ fact(['a1:E8_Acquisition', X],del,U) <=> true | fact(['a1:E8_Acquisition', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Murder', X],add,_) \ fact(['a2:Death', X],del,U) <=> true | fact(['a2:Death', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E14_Condition_Assessment', X],add,_) \ fact(['a1:E13_Attribute_Assignment', X],del,U) <=> true | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108_has_produced', X, Y],add,_) \ fact(['a1:P31_has_modified', X, Y],del,U) <=> true | fact(['a1:P31_has_modified', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16i_was_used_for', X, Y],add,_) \ fact(['a1:P15i_influenced', X, Y],del,U) <=> true | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P123i_resulted_from', _, X1],add,_) \ fact(['a1:E81_Transformation', X1],del,U) <=> true | fact(['a1:E81_Transformation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:homepage', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P96_by_mother', Y, X],add,_) \ fact(['a1:P96i_gave_birth', X, Y],del,U) <=> true | fact(['a1:P96i_gave_birth', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P96i_gave_birth', Y, X],add,_) \ fact(['a1:P96_by_mother', X, Y],del,U) <=> true | fact(['a1:P96_by_mother', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P100_was_death_of', X, _],add,_) \ fact(['a1:E69_Death', X],del,U) <=> true | fact(['a1:E69_Death', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41i_was_classified_by', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P71i_is_listed_in', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41i_was_classified_by', Y, X],add,_) \ fact(['a1:P41_classified', X, Y],del,U) <=> true | fact(['a1:P41_classified', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41_classified', Y, X],add,_) \ fact(['a1:P41i_was_classified_by', X, Y],del,U) <=> true | fact(['a1:P41i_was_classified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P14_carried_out_by', X, Y],add,_) \ fact(['a1:P11_had_participant', X, Y],del,U) <=> true | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P93_took_out_of_existence', X, Y],add,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U) <=> true | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P54_has_current_permanent_location', X, X2],add,_), fact(['a1:P54_has_current_permanent_location', X, X1],add,_), fact(['a1:E19_Physical_Object', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P146_separated_from', X, Y],add,_) \ fact(['a1:P11_had_participant', X, Y],del,U) <=> true | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P17_was_motivated_by', Y, X],add,_) \ fact(['a1:P17i_motivated', X, Y],del,U) <=> true | fact(['a1:P17i_motivated', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P17i_motivated', Y, X],add,_) \ fact(['a1:P17_was_motivated_by', X, Y],del,U) <=> true | fact(['a1:P17_was_motivated_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39i_was_measured_by', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P113_removed', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73_has_translation', Y, X],add,_) \ fact(['a1:P73i_is_translation_of', X, Y],del,U) <=> true | fact(['a1:P73i_is_translation_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73i_is_translation_of', Y, X],add,_) \ fact(['a1:P73_has_translation', X, Y],del,U) <=> true | fact(['a1:P73_has_translation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P2i_is_type_of', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P141i_was_assigned_by', _, X1],add,_) \ fact(['a1:E13_Attribute_Assignment', X1],del,U) <=> true | fact(['a1:E13_Attribute_Assignment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P102_has_title', X, Y],add,_) \ fact(['a1:P1_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P38_deassigned', _, X1],add,_) \ fact(['a1:E42_Identifier', X1],del,U) <=> true | fact(['a1:E42_Identifier', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P54_has_current_permanent_location', Y, X],add,_) \ fact(['a1:P54i_is_current_permanent_location_of', X, Y],del,U) <=> true | fact(['a1:P54i_is_current_permanent_location_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P54i_is_current_permanent_location_of', Y, X],add,_) \ fact(['a1:P54_has_current_permanent_location', X, Y],del,U) <=> true | fact(['a1:P54_has_current_permanent_location', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E21_Person', X],add,_) \ fact(['a1:E20_Biological_Object', X],del,U) <=> true | fact(['a1:E20_Biological_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['rdfs:Container', X],add,_) \ fact(['rdfs:Resource', X],del,U) <=> true | fact(['rdfs:Resource', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:publications', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:relatedInformationObjects', Y, X],add,_) \ fact(['a1:relatedInformationObjects', X, Y],del,U) <=> true | fact(['a1:relatedInformationObjects', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P126_employed', X, _],add,_) \ fact(['a1:E11_Modification', X],del,U) <=> true | fact(['a1:E11_Modification', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:death', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:Divorce', X],add,_) \ fact(['a2:GroupEvent', X],del,U) <=> true | fact(['a2:GroupEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108i_was_produced_by', X, _],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P136_was_based_on', X, _],add,_) \ fact(['a1:E83_Type_Creation', X],del,U) <=> true | fact(['a1:E83_Type_Creation', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Graduation', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P29i_received_custody_through', Y, X],add,_) \ fact(['a1:P29_custody_received_by', X, Y],del,U) <=> true | fact(['a1:P29_custody_received_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P29_custody_received_by', Y, X],add,_) \ fact(['a1:P29i_received_custody_through', X, Y],del,U) <=> true | fact(['a1:P29i_received_custody_through', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P10_falls_within', Y, X],add,_) \ fact(['a1:P10i_contains', X, Y],del,U) <=> true | fact(['a1:P10i_contains', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P10i_contains', Y, X],add,_) \ fact(['a1:P10_falls_within', X, Y],del,U) <=> true | fact(['a1:P10_falls_within', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55_has_current_location', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P142_used_constituent', X, Y],add,_) \ fact(['a1:P16_used_specific_object', X, Y],del,U) <=> true | fact(['a1:P16_used_specific_object', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P147i_was_curated_by', X, _],add,_) \ fact(['a1:E78_Collection', X],del,U) <=> true | fact(['a1:E78_Collection', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E53_Place', X],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P72i_is_language_of', _, X1],add,_) \ fact(['a1:E33_Linguistic_Object', X1],del,U) <=> true | fact(['a1:E33_Linguistic_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P70_documents', X, Y],add,_) \ fact(['a1:P67_refers_to', X, Y],del,U) <=> true | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P124_transformed', X, Y],add,_) \ fact(['a1:P93_took_out_of_existence', X, Y],del,U) <=> true | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:Person', X],add,_) \ fact(['a4:Person', X],del,U) <=> true | fact(['a4:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E24_Physical_Man-Made_Thing', X],add,_) \ fact(['a1:E71_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P148i_is_component_of', Y, X],add,_) \ fact(['a1:P148_has_component', X, Y],del,U) <=> true | fact(['a1:P148_has_component', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P148_has_component', Y, X],add,_) \ fact(['a1:P148i_is_component_of', X, Y],del,U) <=> true | fact(['a1:P148i_is_component_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P15_was_influenced_by', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P107_has_current_or_former_member', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:made', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P30_transferred_custody_of', Y, X],add,_) \ fact(['a1:P30i_custody_transferred_through', X, Y],del,U) <=> true | fact(['a1:P30i_custody_transferred_through', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P30i_custody_transferred_through', Y, X],add,_) \ fact(['a1:P30_transferred_custody_of', X, Y],del,U) <=> true | fact(['a1:P30_transferred_custody_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P125_used_object_of_type', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:birth', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E65_Creation', X],add,_) \ fact(['a1:E63_Beginning_of_Existence', X],del,U) <=> true | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E81_Transformation', X],add,_) \ fact(['a1:E64_End_of_Existence', X],del,U) <=> true | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P24i_changed_ownership_through', Y, X],add,_) \ fact(['a1:P24_transferred_title_of', X, Y],del,U) <=> true | fact(['a1:P24_transferred_title_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P24_transferred_title_of', Y, X],add,_) \ fact(['a1:P24i_changed_ownership_through', X, Y],del,U) <=> true | fact(['a1:P24i_changed_ownership_through', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:Annulment', X],add,_) \ fact(['a2:GroupEvent', X],del,U) <=> true | fact(['a2:GroupEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Promotion', X],add,_) \ fact(['a2:PositionChange', X],del,U) <=> true | fact(['a2:PositionChange', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P31_has_modified', X, Y],add,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U) <=> true | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:Ordination', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P130_shows_features_of', _, X1],add,_) \ fact(['a1:E70_Thing', X1],del,U) <=> true | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P118_overlaps_in_time_with', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P144i_gained_member_by', _, X1],add,_) \ fact(['a1:E85_Joining', X1],del,U) <=> true | fact(['a1:E85_Joining', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P124i_was_transformed_by', X, Y],add,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U) <=> true | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P15_was_influenced_by', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E79_Part_Addition', X],add,_), fact(['a1:E80_Part_Removal', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135_created_type', X, Y],add,_) \ fact(['a1:P94_has_created', X, Y],del,U) <=> true | fact(['a1:P94_has_created', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P7_took_place_at', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a5:Jurisdiction', X],add,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],del,U) <=> true | fact(['a5:LocationPeriodOrJurisdiction', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P56i_is_found_on', X, _],add,_) \ fact(['a1:E26_Physical_Feature', X],del,U) <=> true | fact(['a1:E26_Physical_Feature', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P1_is_identified_by', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P126i_was_employed_in', Y, X],add,_) \ fact(['a1:P126_employed', X, Y],del,U) <=> true | fact(['a1:P126_employed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P126_employed', Y, X],add,_) \ fact(['a1:P126i_was_employed_in', X, Y],del,U) <=> true | fact(['a1:P126i_was_employed_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:principal', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:myersBriggs', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Demotion', X],add,_) \ fact(['a2:PositionChange', X],del,U) <=> true | fact(['a2:PositionChange', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:relationship', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P112_diminished', Y, X],add,_) \ fact(['a1:P112i_was_diminished_by', X, Y],del,U) <=> true | fact(['a1:P112i_was_diminished_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P112i_was_diminished_by', Y, X],add,_) \ fact(['a1:P112_diminished', X, Y],del,U) <=> true | fact(['a1:P112_diminished', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:openid', X, Y],add,_) \ fact(['a3:isPrimaryTopicOf', X, Y],del,U) <=> true | fact(['a3:isPrimaryTopicOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P141_assigned', Y, X],add,_) \ fact(['a1:P141i_was_assigned_by', X, Y],del,U) <=> true | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P141i_was_assigned_by', Y, X],add,_) \ fact(['a1:P141_assigned', X, Y],del,U) <=> true | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P44_has_condition', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P45_consists_of', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P50i_is_current_keeper_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P26_moved_to', Y, X],add,_) \ fact(['a1:P26i_was_destination_of', X, Y],del,U) <=> true | fact(['a1:P26i_was_destination_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P26i_was_destination_of', Y, X],add,_) \ fact(['a1:P26_moved_to', X, Y],del,U) <=> true | fact(['a1:P26_moved_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:img', X, Y],add,_) \ fact(['a3:depiction', X, Y],del,U) <=> true | fact(['a3:depiction', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P24_transferred_title_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P133_is_separated_from', X, _],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P94_has_created', Y, X],add,_) \ fact(['a1:P94i_was_created_by', X, Y],del,U) <=> true | fact(['a1:P94i_was_created_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P94i_was_created_by', Y, X],add,_) \ fact(['a1:P94_has_created', X, Y],del,U) <=> true | fact(['a1:P94_has_created', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67i_is_referred_to_by', _, X1],add,_) \ fact(['a1:E89_Propositional_Object', X1],del,U) <=> true | fact(['a1:E89_Propositional_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P9_consists_of', Y, X],add,_) \ fact(['a1:P9i_forms_part_of', X, Y],del,U) <=> true | fact(['a1:P9i_forms_part_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P9i_forms_part_of', Y, X],add,_) \ fact(['a1:P9_consists_of', X, Y],del,U) <=> true | fact(['a1:P9_consists_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P51_has_former_or_current_owner', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P68i_use_foreseen_by', X, _],add,_) \ fact(['a1:E57_Material', X],del,U) <=> true | fact(['a1:E57_Material', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:IndividualEvent', X],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P138i_has_representation', Y, X],add,_) \ fact(['a1:P138_represents', X, Y],del,U) <=> true | fact(['a1:P138_represents', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P138_represents', Y, X],add,_) \ fact(['a1:P138i_has_representation', X, Y],del,U) <=> true | fact(['a1:P138i_has_representation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P51_has_former_or_current_owner', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:Organization', X],add,_), fact(['a3:Person', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:state', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:father', X, Y],add,_) \ fact(['a6:childOf', X, Y],del,U) <=> true | fact(['a6:childOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55i_currently_holds', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P19_was_intended_use_of', _, X1],add,_) \ fact(['a1:E71_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E71_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E47_Spatial_Coordinates', X],add,_) \ fact(['a1:E44_Place_Appellation', X],del,U) <=> true | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:workInfoHomepage', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:depicts', Y, X],add,_) \ fact(['a3:depiction', X, Y],del,U) <=> true | fact(['a3:depiction', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:depiction', Y, X],add,_) \ fact(['a3:depicts', X, Y],del,U) <=> true | fact(['a3:depicts', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['rdfs:Literal', X],add,_) \ fact(['rdfs:Resource', X],del,U) <=> true | fact(['rdfs:Resource', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P52_has_current_owner', X, Y],add,_) \ fact(['a1:P105_right_held_by', X, Y],del,U) <=> true | fact(['a1:P105_right_held_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:concurrentEvent', _, X1],add,_) \ fact(['a2:Event', X1],del,U) <=> true | fact(['a2:Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P58_has_section_definition', _, X1],add,_) \ fact(['a1:E46_Section_Definition', X1],del,U) <=> true | fact(['a1:E46_Section_Definition', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98i_was_born', X, _],add,_) \ fact(['a1:E21_Person', X],del,U) <=> true | fact(['a1:E21_Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:surname', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P56i_is_found_on', _, X1],add,_) \ fact(['a1:E19_Physical_Object', X1],del,U) <=> true | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P144_joined_with', X, _],add,_) \ fact(['a1:E85_Joining', X],del,U) <=> true | fact(['a1:E85_Joining', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P130i_features_are_also_found_on', X, _],add,_) \ fact(['a1:E70_Thing', X],del,U) <=> true | fact(['a1:E70_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:event', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P43_has_dimension', X, _],add,_) \ fact(['a1:E70_Thing', X],del,U) <=> true | fact(['a1:E70_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P56_bears_feature', Y, X],add,_) \ fact(['a1:P56i_is_found_on', X, Y],del,U) <=> true | fact(['a1:P56i_is_found_on', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P56i_is_found_on', Y, X],add,_) \ fact(['a1:P56_bears_feature', X, Y],del,U) <=> true | fact(['a1:P56_bears_feature', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P83_had_at_least_duration', X, X2],add,_), fact(['a1:P83_had_at_least_duration', X, X1],add,_), fact(['a1:E52_Time-Span', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a2:participant', X, _],add,_) \ fact(['a2:Relationship', X],del,U) <=> true | fact(['a2:Relationship', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P140_assigned_attribute_to', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P4_has_time-span', _, X1],add,_) \ fact(['a1:E52_Time-Span', X1],del,U) <=> true | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13_destroyed', Y, X],add,_) \ fact(['a1:P13i_was_destroyed_by', X, Y],del,U) <=> true | fact(['a1:P13i_was_destroyed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13i_was_destroyed_by', Y, X],add,_) \ fact(['a1:P13_destroyed', X, Y],del,U) <=> true | fact(['a1:P13_destroyed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P107i_is_current_or_former_member_of', _, X1],add,_) \ fact(['a1:E74_Group', X1],del,U) <=> true | fact(['a1:E74_Group', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E12_Production', X],add,_) \ fact(['a1:E63_Beginning_of_Existence', X],del,U) <=> true | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:employer', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E15_Identifier_Assignment', X],add,_) \ fact(['a1:E13_Attribute_Assignment', X],del,U) <=> true | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P117_occurs_during', X, Y],add,_), fact(['a1:P117_occurs_during', Y, Z],add,_) \ fact(['a1:P117_occurs_during', X, Z],del,U) <=> true | fact(['a1:P117_occurs_during', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:E63_Beginning_of_Existence', X],add,_) \ fact(['a1:E5_Event', X],del,U) <=> true | fact(['a1:E5_Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P117i_includes', Y, X],add,_) \ fact(['a1:P117_occurs_during', X, Y],del,U) <=> true | fact(['a1:P117_occurs_during', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P117_occurs_during', Y, X],add,_) \ fact(['a1:P117i_includes', X, Y],del,U) <=> true | fact(['a1:P117i_includes', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P10i_contains', X, _],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P120i_occurs_after', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P28_custody_surrendered_by', X, Y],add,_) \ fact(['a1:P14_carried_out_by', X, Y],del,U) <=> true | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P84i_was_maximum_duration_of', _, X1],add,_) \ fact(['a1:E52_Time-Span', X1],del,U) <=> true | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P37i_was_assigned_by', _, X1],add,_) \ fact(['a1:E15_Identifier_Assignment', X1],del,U) <=> true | fact(['a1:E15_Identifier_Assignment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39_measured', X, X2],add,_), fact(['a1:P39_measured', X, X1],add,_), fact(['a1:E16_Measurement', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P147_curated', _, X1],add,_) \ fact(['a1:E78_Collection', X1],del,U) <=> true | fact(['a1:E78_Collection', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99i_was_dissolved_by', _, X1],add,_) \ fact(['a1:E68_Dissolution', X1],del,U) <=> true | fact(['a1:E68_Dissolution', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P65i_is_shown_by', Y, X],add,_) \ fact(['a1:P65_shows_visual_item', X, Y],del,U) <=> true | fact(['a1:P65_shows_visual_item', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P65_shows_visual_item', Y, X],add,_) \ fact(['a1:P65i_is_shown_by', X, Y],del,U) <=> true | fact(['a1:P65i_is_shown_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P56_bears_feature', X, _],add,_) \ fact(['a1:E19_Physical_Object', X],del,U) <=> true | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E90_Symbolic_Object', X],add,_) \ fact(['a1:E72_Legal_Object', X],del,U) <=> true | fact(['a1:E72_Legal_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P120_occurs_before', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E24_Physical_Man-Made_Thing', X],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E85_Joining', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P58_has_section_definition', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P146i_lost_member_by', _, X1],add,_) \ fact(['a1:E86_Leaving', X1],del,U) <=> true | fact(['a1:E86_Leaving', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P8i_witnessed', _, X1],add,_) \ fact(['a1:E4_Period', X1],del,U) <=> true | fact(['a1:E4_Period', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P37_assigned', X, _],add,_) \ fact(['a1:E15_Identifier_Assignment', X],del,U) <=> true | fact(['a1:E15_Identifier_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P118_overlaps_in_time_with', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E4_Period', X],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Event', X],add,_) \ fact(['a7:Event', X],del,U) <=> true | fact(['a7:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:officiator', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P62i_is_depicted_by', _, X1],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P72_has_language', _, X1],add,_) \ fact(['a1:E56_Language', X1],del,U) <=> true | fact(['a1:E56_Language', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P138_represents', X, Y],add,_) \ fact(['a1:P67_refers_to', X, Y],del,U) <=> true | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P70i_is_documented_in', _, X1],add,_) \ fact(['a1:E31_Document', X1],del,U) <=> true | fact(['a1:E31_Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P32_used_general_technique', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:aimChatID', X, Y],add,_) \ fact(['a3:nick', X, Y],del,U) <=> true | fact(['a3:nick', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P105i_has_right_on', _, X1],add,_) \ fact(['a1:E72_Legal_Object', X1],del,U) <=> true | fact(['a1:E72_Legal_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:age', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P100_was_death_of', Y, X],add,_) \ fact(['a1:P100i_died_in', X, Y],del,U) <=> true | fact(['a1:P100i_died_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P100i_died_in', Y, X],add,_) \ fact(['a1:P100_was_death_of', X, Y],del,U) <=> true | fact(['a1:P100_was_death_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:skypeID', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:participant', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P11_had_participant', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:father', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P82_at_some_time_within', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P31i_was_modified_by', _, X1],add,_) \ fact(['a1:E11_Modification', X1],del,U) <=> true | fact(['a1:E11_Modification', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:gender', X, Y1],add,_), fact(['a3:gender', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:relatedPlaces', X, Y],add,_), fact(['a1:relatedPlaces', Y, Z],add,_) \ fact(['a1:relatedPlaces', X, Z],del,U) <=> true | fact(['a1:relatedPlaces', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P141_assigned', X, _],add,_) \ fact(['a1:E13_Attribute_Assignment', X],del,U) <=> true | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:Document', X],add,_), fact(['a3:Organization', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P72_has_language', X, _],add,_) \ fact(['a1:E33_Linguistic_Object', X],del,U) <=> true | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P105i_has_right_on', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P97_from_father', X, _],add,_) \ fact(['a1:E67_Birth', X],del,U) <=> true | fact(['a1:E67_Birth', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P110i_was_augmented_by', X, _],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P136_was_based_on', Y, X],add,_) \ fact(['a1:P136i_supported_type_creation', X, Y],del,U) <=> true | fact(['a1:P136i_supported_type_creation', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P136i_supported_type_creation', Y, X],add,_) \ fact(['a1:P136_was_based_on', X, Y],del,U) <=> true | fact(['a1:P136_was_based_on', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P22i_acquired_title_through', Y1, X],add,_), fact(['a1:P22i_acquired_title_through', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P100_was_death_of', X, Y],add,_) \ fact(['a1:P93_took_out_of_existence', X, Y],del,U) <=> true | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P45_consists_of', Y, X],add,_) \ fact(['a1:P45i_is_incorporated_in', X, Y],del,U) <=> true | fact(['a1:P45i_is_incorporated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P45i_is_incorporated_in', Y, X],add,_) \ fact(['a1:P45_consists_of', X, Y],del,U) <=> true | fact(['a1:P45_consists_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:jabberID', _, X1],add,_) \ fact(['rdfs:Literal', X1],del,U) <=> true | fact(['rdfs:Literal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P78i_identifies', _, X1],add,_) \ fact(['a1:E52_Time-Span', X1],del,U) <=> true | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:primaryTopic', X, _],add,_) \ fact(['a3:Document', X],del,U) <=> true | fact(['a3:Document', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P53_has_former_or_current_location', Y, X],add,_) \ fact(['a1:P53i_is_former_or_current_location_of', X, Y],del,U) <=> true | fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P53i_is_former_or_current_location_of', Y, X],add,_) \ fact(['a1:P53_has_former_or_current_location', X, Y],del,U) <=> true | fact(['a1:P53_has_former_or_current_location', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P37_assigned', Y, X],add,_) \ fact(['a1:P37i_was_assigned_by', X, Y],del,U) <=> true | fact(['a1:P37i_was_assigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P37i_was_assigned_by', Y, X],add,_) \ fact(['a1:P37_assigned', X, Y],del,U) <=> true | fact(['a1:P37_assigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:lastName', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P84i_was_maximum_duration_of', X, _],add,_) \ fact(['a1:E54_Dimension', X],del,U) <=> true | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P32_used_general_technique', X, Y],add,_) \ fact(['a1:P125_used_object_of_type', X, Y],del,U) <=> true | fact(['a1:P125_used_object_of_type', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P32_used_general_technique', Y, X],add,_) \ fact(['a1:P32i_was_technique_of', X, Y],del,U) <=> true | fact(['a1:P32i_was_technique_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P32i_was_technique_of', Y, X],add,_) \ fact(['a1:P32_used_general_technique', X, Y],del,U) <=> true | fact(['a1:P32_used_general_technique', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P59i_is_located_on_or_within', Y, X],add,_) \ fact(['a1:P59_has_section', X, Y],del,U) <=> true | fact(['a1:P59_has_section', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P59_has_section', Y, X],add,_) \ fact(['a1:P59i_is_located_on_or_within', X, Y],del,U) <=> true | fact(['a1:P59i_is_located_on_or_within', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:mbox', Y1, X],add,_), fact(['a3:mbox', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a2:Marriage', X],add,_) \ fact(['a2:GroupEvent', X],del,U) <=> true | fact(['a2:GroupEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E79_Part_Addition', X],add,_) \ fact(['a1:E11_Modification', X],del,U) <=> true | fact(['a1:E11_Modification', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P35_has_identified', Y, X],add,_) \ fact(['a1:P35i_was_identified_by', X, Y],del,U) <=> true | fact(['a1:P35i_was_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P35i_was_identified_by', Y, X],add,_) \ fact(['a1:P35_has_identified', X, Y],del,U) <=> true | fact(['a1:P35_has_identified', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:focus', X, _],add,_) \ fact(['a8:Concept', X],del,U) <=> true | fact(['a8:Concept', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:img', _, X1],add,_) \ fact(['a3:Image', X1],del,U) <=> true | fact(['a3:Image', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:Organization', X],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:topic_interest', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:eventInterval', _, X1],add,_) \ fact(['a2:Interval', X1],del,U) <=> true | fact(['a2:Interval', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P116i_is_started_by', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108i_was_produced_by', X, Y],add,_) \ fact(['a1:P31i_was_modified_by', X, Y],del,U) <=> true | fact(['a1:P31i_was_modified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:birth', _, X1],add,_) \ fact(['a2:Birth', X1],del,U) <=> true | fact(['a2:Birth', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P132_overlaps_with', Y, X],add,_) \ fact(['a1:P132_overlaps_with', X, Y],del,U) <=> true | fact(['a1:P132_overlaps_with', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E71_Man-Made_Thing', X],add,_) \ fact(['a1:P_E71_Man-Made_Thing', X, X],del,U) <=> true | fact(['a1:P_E71_Man-Made_Thing', X, X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E66_Formation', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P40_observed_dimension', X, _],add,_) \ fact(['a1:E16_Measurement', X],del,U) <=> true | fact(['a1:E16_Measurement', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:immediatelyPrecedingEvent', _, X1],add,_) \ fact(['a2:Event', X1],del,U) <=> true | fact(['a2:Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P70_documents', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P131_is_identified_by', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P102i_is_title_of', _, X1],add,_) \ fact(['a1:E71_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E71_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P11i_participated_in', X, Y],add,_) \ fact(['a1:P12i_was_present_at', X, Y],del,U) <=> true | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P29_custody_received_by', X, _],add,_) \ fact(['a1:E10_Transfer_of_Custody', X],del,U) <=> true | fact(['a1:E10_Transfer_of_Custody', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:event', Y, X],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:agent', Y, X],add,_) \ fact(['a2:event', X, Y],del,U) <=> true | fact(['a2:event', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P109_has_current_or_former_curator', X, _],add,_) \ fact(['a1:E78_Collection', X],del,U) <=> true | fact(['a1:E78_Collection', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P136_was_based_on', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P30_transferred_custody_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:immediatelyFollowingEvent', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P124i_was_transformed_by', X, _],add,_) \ fact(['a1:E77_Persistent_Item', X],del,U) <=> true | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P132_overlaps_with', X, _],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P110_augmented', Y, X],add,_) \ fact(['a1:P110i_was_augmented_by', X, Y],del,U) <=> true | fact(['a1:P110i_was_augmented_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P110i_was_augmented_by', Y, X],add,_) \ fact(['a1:P110_augmented', X, Y],del,U) <=> true | fact(['a1:P110_augmented', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P142i_was_used_in', X, _],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E21_Person', X],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P44_has_condition', _, X1],add,_) \ fact(['a1:E3_Condition_State', X1],del,U) <=> true | fact(['a1:E3_Condition_State', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P78_is_identified_by', Y, X],add,_) \ fact(['a1:P78i_identifies', X, Y],del,U) <=> true | fact(['a1:P78i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P78i_identifies', Y, X],add,_) \ fact(['a1:P78_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P78_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P112_diminished', _, X1],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P8i_witnessed', X, _],add,_) \ fact(['a1:E19_Physical_Object', X],del,U) <=> true | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P5i_forms_part_of', Y, X],add,_) \ fact(['a1:P5_consists_of', X, Y],del,U) <=> true | fact(['a1:P5_consists_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P5_consists_of', Y, X],add,_) \ fact(['a1:P5i_forms_part_of', X, Y],del,U) <=> true | fact(['a1:P5i_forms_part_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P116_starts', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39i_was_measured_by', _, X1],add,_) \ fact(['a1:E16_Measurement', X1],del,U) <=> true | fact(['a1:E16_Measurement', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:precedingEvent', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,_), fact(['a1:referToSame', X1, X2],add,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,_) \ fact(['a1:relatedManMadeThings', X0, X3],del,U) <=> true | fact(['a1:relatedManMadeThings', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:P5i_forms_part_of', X, X2],add,_), fact(['a1:P5i_forms_part_of', X, X1],add,_), fact(['a1:E3_Condition_State', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P10i_contains', _, X1],add,_) \ fact(['a1:E4_Period', X1],del,U) <=> true | fact(['a1:E4_Period', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P125i_was_type_of_object_used_in', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P138_represents', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P10_falls_within', X, _],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P56_bears_feature', _, X1],add,_) \ fact(['a1:E26_Physical_Feature', X1],del,U) <=> true | fact(['a1:E26_Physical_Feature', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99i_was_dissolved_by', X, Y],add,_) \ fact(['a1:P11i_participated_in', X, Y],del,U) <=> true | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E44_Place_Appellation', X],add,_), fact(['a1:E49_Time_Appellation', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P71_lists', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:immediatelyPrecedingEvent', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:child', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Event', X],add,_) \ fact(['a9:Event', X],del,U) <=> true | fact(['a9:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P91i_is_unit_of', X, _],add,_) \ fact(['a1:E58_Measurement_Unit', X],del,U) <=> true | fact(['a1:E58_Measurement_Unit', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E50_Date', X],add,_) \ fact(['a1:E49_Time_Appellation', X],del,U) <=> true | fact(['a1:E49_Time_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P23_transferred_title_from', X, Y],add,_) \ fact(['a1:P14_carried_out_by', X, Y],del,U) <=> true | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P110_augmented', _, X1],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55_has_current_location', Y, X],add,_) \ fact(['a1:P55i_currently_holds', X, Y],del,U) <=> true | fact(['a1:P55i_currently_holds', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55i_currently_holds', Y, X],add,_) \ fact(['a1:P55_has_current_location', X, Y],del,U) <=> true | fact(['a1:P55_has_current_location', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E31_Document', X0, X1],add,_), fact(['a1:referredBySame', X1, X2],add,_), fact(['a1:P_E31_Document', X2, X3],add,_) \ fact(['a1:relatedDocuments', X0, X3],del,U) <=> true | fact(['a1:relatedDocuments', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:relatedManMadeThings', Y, X],add,_) \ fact(['a1:relatedManMadeThings', X, Y],del,U) <=> true | fact(['a1:relatedManMadeThings', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P74i_is_current_or_former_residence_of', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P103i_was_intention_of', _, X1],add,_) \ fact(['a1:E71_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E71_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P84_had_at_most_duration', X, X2],add,_), fact(['a1:P84_had_at_most_duration', X, X1],add,_), fact(['a1:E52_Time-Span', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P88_consists_of', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135i_was_created_by', _, X1],add,_) \ fact(['a1:E83_Type_Creation', X1],del,U) <=> true | fact(['a1:E83_Type_Creation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P119i_is_met_in_time_by', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39_measured', X, _],add,_) \ fact(['a1:E16_Measurement', X],del,U) <=> true | fact(['a1:E16_Measurement', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P97i_was_father_for', X, _],add,_) \ fact(['a1:E21_Person', X],del,U) <=> true | fact(['a1:E21_Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P42i_was_assigned_by', _, X1],add,_) \ fact(['a1:E17_Type_Assignment', X1],del,U) <=> true | fact(['a1:E17_Type_Assignment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16i_was_used_for', X, Y],add,_) \ fact(['a1:P12i_was_present_at', X, Y],del,U) <=> true | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P106_is_composed_of', X, _],add,_) \ fact(['a1:E90_Symbolic_Object', X],del,U) <=> true | fact(['a1:E90_Symbolic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P43_has_dimension', _, X1],add,_) \ fact(['a1:E54_Dimension', X1],del,U) <=> true | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P81_ongoing_throughout', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:family_name', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P140_assigned_attribute_to', X, _],add,_) \ fact(['a1:E13_Attribute_Assignment', X],del,U) <=> true | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P70i_is_documented_in', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P7_took_place_at', X, _],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P45i_is_incorporated_in', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E10_Transfer_of_Custody', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73_has_translation', _, X1],add,_) \ fact(['a1:E33_Linguistic_Object', X1],del,U) <=> true | fact(['a1:E33_Linguistic_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95i_was_formed_by', X, X2],add,_), fact(['a1:P95i_was_formed_by', X, X1],add,_), fact(['a1:E74_Group', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P134_continued', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P138i_has_representation', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P109_has_current_or_former_curator', Y, X],add,_) \ fact(['a1:P109i_is_current_or_former_curator_of', X, Y],del,U) <=> true | fact(['a1:P109i_is_current_or_former_curator_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P109i_is_current_or_former_curator_of', Y, X],add,_) \ fact(['a1:P109_has_current_or_former_curator', X, Y],del,U) <=> true | fact(['a1:P109_has_current_or_former_curator', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P11_had_participant', X, Y],add,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U) <=> true | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P71_lists', X, Y],add,_) \ fact(['a1:P67_refers_to', X, Y],del,U) <=> true | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P44_has_condition', Y, X],add,_) \ fact(['a1:P44i_is_condition_of', X, Y],del,U) <=> true | fact(['a1:P44i_is_condition_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P44i_is_condition_of', Y, X],add,_) \ fact(['a1:P44_has_condition', X, Y],del,U) <=> true | fact(['a1:P44_has_condition', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:openid', Y1, X],add,_), fact(['a3:openid', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P132_overlaps_with', _, X1],add,_) \ fact(['a1:E4_Period', X1],del,U) <=> true | fact(['a1:E4_Period', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P111i_was_added_by', _, X1],add,_) \ fact(['a1:E79_Part_Addition', X1],del,U) <=> true | fact(['a1:E79_Part_Addition', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P40i_was_observed_in', _, X1],add,_) \ fact(['a1:E16_Measurement', X1],del,U) <=> true | fact(['a1:E16_Measurement', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P102_has_title', _, X1],add,_) \ fact(['a1:E35_Title', X1],del,U) <=> true | fact(['a1:E35_Title', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99i_was_dissolved_by', Y, X],add,_) \ fact(['a1:P99_dissolved', X, Y],del,U) <=> true | fact(['a1:P99_dissolved', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99_dissolved', Y, X],add,_) \ fact(['a1:P99i_was_dissolved_by', X, Y],del,U) <=> true | fact(['a1:P99i_was_dissolved_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P119_meets_in_time_with', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P144_joined_with', X, Y],add,_) \ fact(['a1:P11_had_participant', X, Y],del,U) <=> true | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:parent', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41_classified', X, Y],add,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],del,U) <=> true | fact(['a1:P140_assigned_attribute_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:initiatingEvent', _, X1],add,_) \ fact(['a2:Event', X1],del,U) <=> true | fact(['a2:Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P104i_applies_to', _, X1],add,_) \ fact(['a1:E72_Legal_Object', X1],del,U) <=> true | fact(['a1:E72_Legal_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P71i_is_listed_in', _, X1],add,_) \ fact(['a1:E32_Authority_Document', X1],del,U) <=> true | fact(['a1:E32_Authority_Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P35i_was_identified_by', X, _],add,_) \ fact(['a1:E3_Condition_State', X],del,U) <=> true | fact(['a1:E3_Condition_State', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E57_Material', X],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E53_Place', X0, X1],add,_), fact(['a1:referredBySame', X1, X2],add,_), fact(['a1:P_E53_Place', X2, X3],add,_) \ fact(['a1:relatedPlaces', X0, X3],del,U) <=> true | fact(['a1:relatedPlaces', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:P34i_was_assessed_by', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P121_overlaps_with', Y, X],add,_) \ fact(['a1:P121_overlaps_with', X, Y],del,U) <=> true | fact(['a1:P121_overlaps_with', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13_destroyed', X, _],add,_) \ fact(['a1:E6_Destruction', X],del,U) <=> true | fact(['a1:E6_Destruction', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P84_had_at_most_duration', _, X1],add,_) \ fact(['a1:E54_Dimension', X1],del,U) <=> true | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P45_consists_of', _, X1],add,_) \ fact(['a1:E57_Material', X1],del,U) <=> true | fact(['a1:E57_Material', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P100i_died_in', X, Y],add,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U) <=> true | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P123_resulted_in', _, X1],add,_) \ fact(['a1:E77_Persistent_Item', X1],del,U) <=> true | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E51_Contact_Point', X],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:father', X, X2],add,_), fact(['a2:father', X, X1],add,_), fact(['a3:Person', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a2:mother', X, X4],add,_), fact(['a2:mother', X, X3],add,_), fact(['a3:Person', X],add,_) \ fact(['owl:sameAs', X3, X4],del,U) <=> true | fact(['owl:sameAs', X3, X4],add,U), applied_rules(1,red).
phase(2), fact(['a1:P9i_forms_part_of', X, X2],add,_), fact(['a1:P9i_forms_part_of', X, X1],add,_), fact(['a1:E4_Period', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99_dissolved', X, Y],add,_) \ fact(['a1:P11_had_participant', X, Y],del,U) <=> true | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P15i_influenced', Y, X],add,_) \ fact(['a1:P15_was_influenced_by', X, Y],del,U) <=> true | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P15_was_influenced_by', Y, X],add,_) \ fact(['a1:P15i_influenced', X, Y],del,U) <=> true | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67_refers_to', X, _],add,_) \ fact(['a1:E89_Propositional_Object', X],del,U) <=> true | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:parent', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P14i_performed', Y, X],add,_) \ fact(['a1:P14_carried_out_by', X, Y],del,U) <=> true | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P14_carried_out_by', Y, X],add,_) \ fact(['a1:P14i_performed', X, Y],del,U) <=> true | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55_has_current_location', X, _],add,_) \ fact(['a1:E19_Physical_Object', X],del,U) <=> true | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95_has_formed', Y, X],add,_) \ fact(['a1:P95i_was_formed_by', X, Y],del,U) <=> true | fact(['a1:P95i_was_formed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95i_was_formed_by', Y, X],add,_) \ fact(['a1:P95_has_formed', X, Y],del,U) <=> true | fact(['a1:P95_has_formed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95i_was_formed_by', X, _],add,_) \ fact(['a1:E74_Group', X],del,U) <=> true | fact(['a1:E74_Group', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P42i_was_assigned_by', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P94_has_created', _, X1],add,_) \ fact(['a1:E28_Conceptual_Object', X1],del,U) <=> true | fact(['a1:E28_Conceptual_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P131_is_identified_by', _, X1],add,_) \ fact(['a1:E82_Actor_Appellation', X1],del,U) <=> true | fact(['a1:E82_Actor_Appellation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:based_near', _, X1],add,_) \ fact(['a10:SpatialThing', X1],del,U) <=> true | fact(['a10:SpatialThing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108_has_produced', Y, X],add,_) \ fact(['a1:P108i_was_produced_by', X, Y],del,U) <=> true | fact(['a1:P108i_was_produced_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108i_was_produced_by', Y, X],add,_) \ fact(['a1:P108_has_produced', X, Y],del,U) <=> true | fact(['a1:P108_has_produced', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P112i_was_diminished_by', X, Y],add,_) \ fact(['a1:P31i_was_modified_by', X, Y],del,U) <=> true | fact(['a1:P31i_was_modified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E46_Section_Definition', X],add,_) \ fact(['a1:E44_Place_Appellation', X],del,U) <=> true | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P58i_defines_section', Y, X],add,_) \ fact(['a1:P58_has_section_definition', X, Y],del,U) <=> true | fact(['a1:P58_has_section_definition', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P58_has_section_definition', Y, X],add,_) \ fact(['a1:P58i_defines_section', X, Y],del,U) <=> true | fact(['a1:P58i_defines_section', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:age', X, Y1],add,_), fact(['a3:age', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P23i_surrendered_title_through', _, X1],add,_) \ fact(['a1:E8_Acquisition', X1],del,U) <=> true | fact(['a1:E8_Acquisition', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P78_is_identified_by', X, Y],add,_) \ fact(['a1:P1_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27i_was_origin_of', X, Y],add,_) \ fact(['a1:P7i_witnessed', X, Y],del,U) <=> true | fact(['a1:P7i_witnessed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:currentProject', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P119i_is_met_in_time_by', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:aimChatID', Y1, X],add,_), fact(['a3:aimChatID', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27i_was_origin_of', Y, X],add,_) \ fact(['a1:P27_moved_from', X, Y],del,U) <=> true | fact(['a1:P27_moved_from', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27_moved_from', Y, X],add,_) \ fact(['a1:P27i_was_origin_of', X, Y],del,U) <=> true | fact(['a1:P27i_was_origin_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P37_assigned', _, X1],add,_) \ fact(['a1:E42_Identifier', X1],del,U) <=> true | fact(['a1:E42_Identifier', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P116i_is_started_by', Y, X],add,_) \ fact(['a1:P116_starts', X, Y],del,U) <=> true | fact(['a1:P116_starts', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P116_starts', Y, X],add,_) \ fact(['a1:P116i_is_started_by', X, Y],del,U) <=> true | fact(['a1:P116i_is_started_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:sha1', X, _],add,_) \ fact(['a3:Document', X],del,U) <=> true | fact(['a3:Document', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:agent', _, X1],add,_) \ fact(['a3:Agent', X1],del,U) <=> true | fact(['a3:Agent', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P12_occurred_in_the_presence_of', X, _],add,_) \ fact(['a1:E5_Event', X],del,U) <=> true | fact(['a1:E5_Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P117i_includes', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P29i_received_custody_through', X, Y],add,_) \ fact(['a1:P14i_performed', X, Y],del,U) <=> true | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P102_has_title', X, _],add,_) \ fact(['a1:E71_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P118i_is_overlapped_in_time_by', Y, X],add,_) \ fact(['a1:P118_overlaps_in_time_with', X, Y],del,U) <=> true | fact(['a1:P118_overlaps_in_time_with', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P118_overlaps_in_time_with', Y, X],add,_) \ fact(['a1:P118i_is_overlapped_in_time_by', X, Y],del,U) <=> true | fact(['a1:P118i_is_overlapped_in_time_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P89_falls_within', X, Y],add,_), fact(['a1:P89_falls_within', Y, Z],add,_) \ fact(['a1:P89_falls_within', X, Z],del,U) <=> true | fact(['a1:P89_falls_within', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P138i_has_representation', X, Y],add,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],del,U) <=> true | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:father', X, Y1],add,_), fact(['a2:father', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a3:status', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P137_exemplifies', X, Y],add,_) \ fact(['a1:P2_has_type', X, Y],del,U) <=> true | fact(['a1:P2_has_type', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:event', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:followingEvent', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E49_Time_Appellation', X],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:witness', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P48i_is_preferred_identifier_of', X, Y],add,_) \ fact(['a1:P1i_identifies', X, Y],del,U) <=> true | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P26i_was_destination_of', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:openid', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:organization', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P14i_performed', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P48i_is_preferred_identifier_of', X, _],add,_) \ fact(['a1:E42_Identifier', X],del,U) <=> true | fact(['a1:E42_Identifier', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:plan', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P34i_was_assessed_by', X, Y],add,_) \ fact(['a1:P140i_was_attributed_by', X, Y],del,U) <=> true | fact(['a1:P140i_was_attributed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P131_is_identified_by', Y, X],add,_) \ fact(['a1:P131i_identifies', X, Y],del,U) <=> true | fact(['a1:P131i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P131i_identifies', Y, X],add,_) \ fact(['a1:P131_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P131_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P148i_is_component_of', _, X1],add,_) \ fact(['a1:E89_Propositional_Object', X1],del,U) <=> true | fact(['a1:E89_Propositional_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P1_is_identified_by', _, X1],add,_) \ fact(['a1:E41_Appellation', X1],del,U) <=> true | fact(['a1:E41_Appellation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P129_is_about', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P115i_is_finished_by', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P42_assigned', Y, X],add,_) \ fact(['a1:P42i_was_assigned_by', X, Y],del,U) <=> true | fact(['a1:P42i_was_assigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P42i_was_assigned_by', Y, X],add,_) \ fact(['a1:P42_assigned', X, Y],del,U) <=> true | fact(['a1:P42_assigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:employer', _, X1],add,_) \ fact(['a3:Agent', X1],del,U) <=> true | fact(['a3:Agent', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P31_has_modified', X, _],add,_) \ fact(['a1:E11_Modification', X],del,U) <=> true | fact(['a1:E11_Modification', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P87_is_identified_by', Y, X],add,_) \ fact(['a1:P87i_identifies', X, Y],del,U) <=> true | fact(['a1:P87i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P87i_identifies', Y, X],add,_) \ fact(['a1:P87_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P87_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:spectator', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E28_Conceptual_Object', X],add,_) \ fact(['a1:E71_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99_dissolved', X, _],add,_) \ fact(['a1:E68_Dissolution', X],del,U) <=> true | fact(['a1:E68_Dissolution', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:birth', X, Y],add,_) \ fact(['a2:event', X, Y],del,U) <=> true | fact(['a2:event', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135i_was_created_by', X, X2],add,_), fact(['a1:P135i_was_created_by', X, X1],add,_), fact(['a1:E55_Type', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:E9_Move', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P128i_is_carried_by', _, X1],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P71i_is_listed_in', X, Y],add,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],del,U) <=> true | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P5_consists_of', _, X1],add,_) \ fact(['a1:E3_Condition_State', X1],del,U) <=> true | fact(['a1:E3_Condition_State', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P78i_identifies', X, _],add,_) \ fact(['a1:E49_Time_Appellation', X],del,U) <=> true | fact(['a1:E49_Time_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P65i_is_shown_by', X, Y],add,_) \ fact(['a1:P128i_is_carried_by', X, Y],del,U) <=> true | fact(['a1:P128i_is_carried_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E8_Acquisition', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:followingEvent', _, X1],add,_) \ fact(['a2:Event', X1],del,U) <=> true | fact(['a2:Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:icqChatID', _, X1],add,_) \ fact(['rdfs:Literal', X1],del,U) <=> true | fact(['rdfs:Literal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a5:PhysicalMedium', X],add,_) \ fact(['a5:MediaType', X],del,U) <=> true | fact(['a5:MediaType', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P70i_is_documented_in', Y, X],add,_) \ fact(['a1:P70_documents', X, Y],del,U) <=> true | fact(['a1:P70_documents', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P70_documents', Y, X],add,_) \ fact(['a1:P70i_is_documented_in', X, Y],del,U) <=> true | fact(['a1:P70i_is_documented_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E75_Conceptual_Object_Appellation', X],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P83i_was_minimum_duration_of', X, _],add,_) \ fact(['a1:E54_Dimension', X],del,U) <=> true | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:Group', X],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P126_employed', _, X1],add,_) \ fact(['a1:E57_Material', X1],del,U) <=> true | fact(['a1:E57_Material', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P40i_was_observed_in', X, _],add,_) \ fact(['a1:E54_Dimension', X],del,U) <=> true | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:agent', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P71_lists', X, _],add,_) \ fact(['a1:E32_Authority_Document', X],del,U) <=> true | fact(['a1:E32_Authority_Document', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P32i_was_technique_of', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E20_Biological_Object', X],add,_) \ fact(['a1:E19_Physical_Object', X],del,U) <=> true | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P87i_identifies', X, _],add,_) \ fact(['a1:E44_Place_Appellation', X],del,U) <=> true | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P130i_features_are_also_found_on', _, X1],add,_) \ fact(['a1:E70_Thing', X1],del,U) <=> true | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P119i_is_met_in_time_by', Y, X],add,_) \ fact(['a1:P119_meets_in_time_with', X, Y],del,U) <=> true | fact(['a1:P119_meets_in_time_with', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P119_meets_in_time_with', Y, X],add,_) \ fact(['a1:P119i_is_met_in_time_by', X, Y],del,U) <=> true | fact(['a1:P119i_is_met_in_time_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:interest', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P146i_lost_member_by', X, Y],add,_) \ fact(['a1:P11i_participated_in', X, Y],del,U) <=> true | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P30i_custody_transferred_through', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P104_is_subject_to', _, X1],add,_) \ fact(['a1:E30_Right', X1],del,U) <=> true | fact(['a1:E30_Right', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P110_augmented', X, _],add,_) \ fact(['a1:E79_Part_Addition', X],del,U) <=> true | fact(['a1:E79_Part_Addition', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:based_near', X, _],add,_) \ fact(['a10:SpatialThing', X],del,U) <=> true | fact(['a10:SpatialThing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16_used_specific_object', _, X1],add,_) \ fact(['a1:E70_Thing', X1],del,U) <=> true | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E72_Legal_Object', X],add,_) \ fact(['a1:E70_Thing', X],del,U) <=> true | fact(['a1:E70_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67i_is_referred_to_by', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P112_diminished', X, _],add,_) \ fact(['a1:E80_Part_Removal', X],del,U) <=> true | fact(['a1:E80_Part_Removal', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:NameChange', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E37_Mark', X],add,_) \ fact(['a1:E36_Visual_Item', X],del,U) <=> true | fact(['a1:E36_Visual_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E73_Information_Object', X0, X1],add,_), fact(['a1:P67_refers_to', X1, X2],add,_), fact(['a1:P_E73_Information_Object', X2, X3],add,_) \ fact(['a1:relatedInformationObjects', X0, X3],del,U) <=> true | fact(['a1:relatedInformationObjects', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a3:depicts', X, _],add,_) \ fact(['a3:Image', X],del,U) <=> true | fact(['a3:Image', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:isPrimaryTopicOf', X, Y],add,_) \ fact(['a3:page', X, Y],del,U) <=> true | fact(['a3:page', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P146i_lost_member_by', X, _],add,_) \ fact(['a1:E74_Group', X],del,U) <=> true | fact(['a1:E74_Group', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P59i_is_located_on_or_within', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67_refers_to', X1, X0],add,_), fact(['a1:P67_refers_to', X1, X2],add,_) \ fact(['a1:referredBySame', X0, X2],del,U) <=> true | fact(['a1:referredBySame', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P28i_surrendered_custody_through', _, X1],add,_) \ fact(['a1:E10_Transfer_of_Custody', X1],del,U) <=> true | fact(['a1:E10_Transfer_of_Custody', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P87i_identifies', X, Y],add,_) \ fact(['a1:P1i_identifies', X, Y],del,U) <=> true | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P68i_use_foreseen_by', _, X1],add,_) \ fact(['a1:E29_Design_or_Procedure', X1],del,U) <=> true | fact(['a1:E29_Design_or_Procedure', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P17i_motivated', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P22_transferred_title_to', X, Y1],add,_), fact(['a1:P22_transferred_title_to', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P86i_contains', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P25i_moved_by', X, Y],add,_) \ fact(['a1:P12i_was_present_at', X, Y],del,U) <=> true | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P40_observed_dimension', X, Y],add,_) \ fact(['a1:P141_assigned', X, Y],del,U) <=> true | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P46_is_composed_of', Y, X],add,_) \ fact(['a1:P46i_forms_part_of', X, Y],del,U) <=> true | fact(['a1:P46i_forms_part_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P46i_forms_part_of', Y, X],add,_) \ fact(['a1:P46_is_composed_of', X, Y],del,U) <=> true | fact(['a1:P46_is_composed_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P48_has_preferred_identifier', X, Y],add,_) \ fact(['a1:P1_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P91_has_unit', _, X1],add,_) \ fact(['a1:E58_Measurement_Unit', X1],del,U) <=> true | fact(['a1:E58_Measurement_Unit', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P127_has_broader_term', X, Y],add,_), fact(['a1:P127_has_broader_term', Y, Z],add,_) \ fact(['a1:P127_has_broader_term', X, Z],del,U) <=> true | fact(['a1:P127_has_broader_term', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a2:event', _, X1],add,_) \ fact(['a2:Event', X1],del,U) <=> true | fact(['a2:Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E3_Condition_State', X],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:accountServiceHomepage', X, _],add,_) \ fact(['a3:OnlineAccount', X],del,U) <=> true | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P70i_is_documented_in', X, Y],add,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],del,U) <=> true | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:holdsAccount', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67_refers_to', X0, X1],add,_), fact(['a1:P_E31_Document', X1, X2],add,_) \ fact(['a1:refersToDocument', X0, X2],del,U) <=> true | fact(['a1:refersToDocument', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P146_separated_from', _, X1],add,_) \ fact(['a1:E74_Group', X1],del,U) <=> true | fact(['a1:E74_Group', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P45i_is_incorporated_in', X, _],add,_) \ fact(['a1:E57_Material', X],del,U) <=> true | fact(['a1:E57_Material', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P88i_forms_part_of', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P24i_changed_ownership_through', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:jabberID', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:participant', _, X1],add,_) \ fact(['a3:Agent', X1],del,U) <=> true | fact(['a3:Agent', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P4_has_time-span', X, X2],add,_), fact(['a1:P4_has_time-span', X, X1],add,_), fact(['a1:E2_Temporal_Entity', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55_has_current_location', X, X2],add,_), fact(['a1:P55_has_current_location', X, X1],add,_), fact(['a1:E19_Physical_Object', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P120i_occurs_after', X, Y],add,_), fact(['a1:P120i_occurs_after', Y, Z],add,_) \ fact(['a1:P120i_occurs_after', X, Z],del,U) <=> true | fact(['a1:P120i_occurs_after', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:E13_Attribute_Assignment', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:knows', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:weblog', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:PositionChange', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P134_continued', Y, X],add,_) \ fact(['a1:P134i_was_continued_by', X, Y],del,U) <=> true | fact(['a1:P134i_was_continued_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P134i_was_continued_by', Y, X],add,_) \ fact(['a1:P134_continued', X, Y],del,U) <=> true | fact(['a1:P134_continued', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P29_custody_received_by', X, Y],add,_) \ fact(['a1:P14_carried_out_by', X, Y],del,U) <=> true | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P43i_is_dimension_of', X, _],add,_) \ fact(['a1:E54_Dimension', X],del,U) <=> true | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P137_exemplifies', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P65i_is_shown_by', X, _],add,_) \ fact(['a1:E36_Visual_Item', X],del,U) <=> true | fact(['a1:E36_Visual_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P91i_is_unit_of', Y, X],add,_) \ fact(['a1:P91_has_unit', X, Y],del,U) <=> true | fact(['a1:P91_has_unit', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P91_has_unit', Y, X],add,_) \ fact(['a1:P91i_is_unit_of', X, Y],del,U) <=> true | fact(['a1:P91i_is_unit_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55_has_current_location', X, Y],add,_) \ fact(['a1:P53_has_former_or_current_location', X, Y],del,U) <=> true | fact(['a1:P53_has_former_or_current_location', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13i_was_destroyed_by', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P145i_left_by', Y, X],add,_) \ fact(['a1:P145_separated', X, Y],del,U) <=> true | fact(['a1:P145_separated', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P145_separated', Y, X],add,_) \ fact(['a1:P145i_left_by', X, Y],del,U) <=> true | fact(['a1:P145i_left_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95_has_formed', X, _],add,_) \ fact(['a1:E66_Formation', X],del,U) <=> true | fact(['a1:E66_Formation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P38i_was_deassigned_by', X, _],add,_) \ fact(['a1:E42_Identifier', X],del,U) <=> true | fact(['a1:E42_Identifier', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:immediatelyPrecedingEvent', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:isPrimaryTopicOf', Y, X],add,_) \ fact(['a3:primaryTopic', X, Y],del,U) <=> true | fact(['a3:primaryTopic', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:primaryTopic', Y, X],add,_) \ fact(['a3:isPrimaryTopicOf', X, Y],del,U) <=> true | fact(['a3:isPrimaryTopicOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P38_deassigned', X, _],add,_) \ fact(['a1:E15_Identifier_Assignment', X],del,U) <=> true | fact(['a1:E15_Identifier_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P17_was_motivated_by', X, Y],add,_) \ fact(['a1:P15_was_influenced_by', X, Y],del,U) <=> true | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P4i_is_time-span_of', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E31_Document', X0, X1],add,_), fact(['a1:referToSame', X1, X2],add,_), fact(['a1:P_E31_Document', X2, X3],add,_) \ fact(['a1:relatedDocuments', X0, X3],del,U) <=> true | fact(['a1:relatedDocuments', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a2:Performance', X],add,_) \ fact(['a2:GroupEvent', X],del,U) <=> true | fact(['a2:GroupEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:PersonalProfileDocument', X],add,_) \ fact(['a3:Document', X],del,U) <=> true | fact(['a3:Document', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P17_was_motivated_by', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P19_was_intended_use_of', Y, X],add,_) \ fact(['a1:P19i_was_made_for', X, Y],del,U) <=> true | fact(['a1:P19i_was_made_for', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P19i_was_made_for', Y, X],add,_) \ fact(['a1:P19_was_intended_use_of', X, Y],del,U) <=> true | fact(['a1:P19_was_intended_use_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P29i_received_custody_through', _, X1],add,_) \ fact(['a1:E10_Transfer_of_Custody', X1],del,U) <=> true | fact(['a1:E10_Transfer_of_Custody', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P30_transferred_custody_of', X, _],add,_) \ fact(['a1:E10_Transfer_of_Custody', X],del,U) <=> true | fact(['a1:E10_Transfer_of_Custody', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:skypeID', X, Y],add,_) \ fact(['a3:nick', X, Y],del,U) <=> true | fact(['a3:nick', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P101_had_as_general_use', Y, X],add,_) \ fact(['a1:P101i_was_use_of', X, Y],del,U) <=> true | fact(['a1:P101i_was_use_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P101i_was_use_of', Y, X],add,_) \ fact(['a1:P101_had_as_general_use', X, Y],del,U) <=> true | fact(['a1:P101_had_as_general_use', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P131_is_identified_by', X, Y],add,_) \ fact(['a1:P1_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P46i_forms_part_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P76_has_contact_point', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:death', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:followingEvent', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P58i_defines_section', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16i_was_used_for', X, _],add,_) \ fact(['a1:E70_Thing', X],del,U) <=> true | fact(['a1:E70_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95i_was_formed_by', X, Y],add,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U) <=> true | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:relatedDocuments', Y, X],add,_) \ fact(['a1:relatedDocuments', X, Y],del,U) <=> true | fact(['a1:relatedDocuments', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P75_possesses', _, X1],add,_) \ fact(['a1:E30_Right', X1],del,U) <=> true | fact(['a1:E30_Right', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E5_Event', X],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P131i_identifies', X, _],add,_) \ fact(['a1:E82_Actor_Appellation', X],del,U) <=> true | fact(['a1:E82_Actor_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P35_has_identified', X, _],add,_) \ fact(['a1:E14_Condition_Assessment', X],del,U) <=> true | fact(['a1:E14_Condition_Assessment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P143_joined', X, X2],add,_), fact(['a1:P143_joined', X, X1],add,_), fact(['a1:E85_Joining', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135i_was_created_by', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P83_had_at_least_duration', Y, X],add,_) \ fact(['a1:P83i_was_minimum_duration_of', X, Y],del,U) <=> true | fact(['a1:P83i_was_minimum_duration_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P83i_was_minimum_duration_of', Y, X],add,_) \ fact(['a1:P83_had_at_least_duration', X, Y],del,U) <=> true | fact(['a1:P83_had_at_least_duration', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P113i_was_removed_by', Y, X],add,_) \ fact(['a1:P113_removed', X, Y],del,U) <=> true | fact(['a1:P113_removed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P113_removed', Y, X],add,_) \ fact(['a1:P113i_was_removed_by', X, Y],del,U) <=> true | fact(['a1:P113i_was_removed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27_moved_from', X, Y],add,_) \ fact(['a1:P7_took_place_at', X, Y],del,U) <=> true | fact(['a1:P7_took_place_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E73_Information_Object', X0, X1],add,_), fact(['a1:referToSame', X1, X2],add,_), fact(['a1:P_E73_Information_Object', X2, X3],add,_) \ fact(['a1:relatedInformationObjects', X0, X3],del,U) <=> true | fact(['a1:relatedInformationObjects', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108_has_produced', X, Y],add,_) \ fact(['a1:P92_brought_into_existence', X, Y],del,U) <=> true | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E31_Document', X],add,_) \ fact(['a1:E73_Information_Object', X],del,U) <=> true | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E40_Legal_Body', X],add,_) \ fact(['a1:E74_Group', X],del,U) <=> true | fact(['a1:E74_Group', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P106_is_composed_of', X, Y],add,_), fact(['a1:P106_is_composed_of', Y, Z],add,_) \ fact(['a1:P106_is_composed_of', X, Z],del,U) <=> true | fact(['a1:P106_is_composed_of', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P62i_is_depicted_by', Y, X],add,_) \ fact(['a1:P62_depicts', X, Y],del,U) <=> true | fact(['a1:P62_depicts', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P62_depicts', Y, X],add,_) \ fact(['a1:P62i_is_depicted_by', X, Y],del,U) <=> true | fact(['a1:P62i_is_depicted_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:birth', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E39_Actor', X],add,_) \ fact(['a1:E77_Persistent_Item', X],del,U) <=> true | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E64_End_of_Existence', X],add,_) \ fact(['a1:E5_Event', X],del,U) <=> true | fact(['a1:E5_Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P74_has_current_or_former_residence', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P110i_was_augmented_by', X, Y],add,_) \ fact(['a1:P31i_was_modified_by', X, Y],del,U) <=> true | fact(['a1:P31i_was_modified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P52i_is_current_owner_of', X, Y],add,_) \ fact(['a1:P105i_has_right_on', X, Y],del,U) <=> true | fact(['a1:P105i_has_right_on', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P101_had_as_general_use', X, _],add,_) \ fact(['a1:E70_Thing', X],del,U) <=> true | fact(['a1:E70_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13_destroyed', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P142_used_constituent', X, _],add,_) \ fact(['a1:E15_Identifier_Assignment', X],del,U) <=> true | fact(['a1:E15_Identifier_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E45_Address', X],add,_) \ fact(['a1:E51_Contact_Point', X],del,U) <=> true | fact(['a1:E51_Contact_Point', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P43i_is_dimension_of', Y, X],add,_) \ fact(['a1:P43_has_dimension', X, Y],del,U) <=> true | fact(['a1:P43_has_dimension', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P43_has_dimension', Y, X],add,_) \ fact(['a1:P43i_is_dimension_of', X, Y],del,U) <=> true | fact(['a1:P43i_is_dimension_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P21_had_general_purpose', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:relationship', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a5:AgentClass', X],add,_) \ fact(['rdfs:Class', X],del,U) <=> true | fact(['rdfs:Class', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P31i_was_modified_by', Y, X],add,_) \ fact(['a1:P31_has_modified', X, Y],del,U) <=> true | fact(['a1:P31_has_modified', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P31_has_modified', Y, X],add,_) \ fact(['a1:P31i_was_modified_by', X, Y],del,U) <=> true | fact(['a1:P31i_was_modified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:partner', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98i_was_born', Y, X],add,_) \ fact(['a1:P98_brought_into_life', X, Y],del,U) <=> true | fact(['a1:P98_brought_into_life', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98_brought_into_life', Y, X],add,_) \ fact(['a1:P98i_was_born', X, Y],del,U) <=> true | fact(['a1:P98i_was_born', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:immediatelyFollowingEvent', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P134_continued', X, Y],add,_) \ fact(['a1:P15_was_influenced_by', X, Y],del,U) <=> true | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P35_has_identified', _, X1],add,_) \ fact(['a1:E3_Condition_State', X1],del,U) <=> true | fact(['a1:E3_Condition_State', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P51i_is_former_or_current_owner_of', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:mother', X, Y],add,_) \ fact(['a6:childOf', X, Y],del,U) <=> true | fact(['a6:childOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P115_finishes', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:thumbnail', _, X1],add,_) \ fact(['a3:Image', X1],del,U) <=> true | fact(['a3:Image', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P2_has_type', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P5i_forms_part_of', _, X1],add,_) \ fact(['a1:E3_Condition_State', X1],del,U) <=> true | fact(['a1:E3_Condition_State', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P22i_acquired_title_through', Y, X],add,_) \ fact(['a1:P22_transferred_title_to', X, Y],del,U) <=> true | fact(['a1:P22_transferred_title_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P22_transferred_title_to', Y, X],add,_) \ fact(['a1:P22i_acquired_title_through', X, Y],del,U) <=> true | fact(['a1:P22i_acquired_title_through', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P25_moved', _, X1],add,_) \ fact(['a1:E19_Physical_Object', X1],del,U) <=> true | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P127_has_broader_term', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P69_is_associated_with', Y, X],add,_) \ fact(['a1:P69_is_associated_with', X, Y],del,U) <=> true | fact(['a1:P69_is_associated_with', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:father', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P139_has_alternative_form', _, X1],add,_) \ fact(['a1:E41_Appellation', X1],del,U) <=> true | fact(['a1:E41_Appellation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P26_moved_to', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P123_resulted_in', X, _],add,_) \ fact(['a1:E81_Transformation', X],del,U) <=> true | fact(['a1:E81_Transformation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P92_brought_into_existence', _, X1],add,_) \ fact(['a1:E77_Persistent_Item', X1],del,U) <=> true | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,red).
phase(2), fact(['a5:FileFormat', X],add,_) \ fact(['a5:MediaType', X],del,U) <=> true | fact(['a5:MediaType', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P50_has_current_keeper', X, Y],add,_) \ fact(['a1:P49_has_former_or_current_keeper', X, Y],del,U) <=> true | fact(['a1:P49_has_former_or_current_keeper', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:firstName', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P2_has_type', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E25_Man-Made_Feature', X],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E73_Information_Object', X],add,_) \ fact(['a1:E89_Propositional_Object', X],del,U) <=> true | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P96i_gave_birth', X, Y],add,_) \ fact(['a1:P11i_participated_in', X, Y],del,U) <=> true | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P28_custody_surrendered_by', X, _],add,_) \ fact(['a1:E10_Transfer_of_Custody', X],del,U) <=> true | fact(['a1:E10_Transfer_of_Custody', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55i_currently_holds', X, Y],add,_) \ fact(['a1:P53i_is_former_or_current_location_of', X, Y],del,U) <=> true | fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P87_is_identified_by', X, Y],add,_) \ fact(['a1:P1_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P37_assigned', X, Y],add,_) \ fact(['a1:P141_assigned', X, Y],del,U) <=> true | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:workInfoHomepage', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E22_Man-Made_Object', X],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P109i_is_current_or_former_curator_of', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P15i_influenced', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73i_is_translation_of', X, X2],add,_), fact(['a1:P73i_is_translation_of', X, X1],add,_), fact(['a1:E33_Linguistic_Object', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95i_was_formed_by', _, X1],add,_) \ fact(['a1:E66_Formation', X1],del,U) <=> true | fact(['a1:E66_Formation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P129_is_about', X, Y],add,_) \ fact(['a1:P67_refers_to', X, Y],del,U) <=> true | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E81_Transformation', X],add,_) \ fact(['a1:E63_Beginning_of_Existence', X],del,U) <=> true | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E31_Document', X0, X1],add,_), fact(['a1:refersToDocument', X1, X2],add,_), fact(['a1:refersToDocument', X2, X3],add,_) \ fact(['a1:relatedDocuments', X0, X3],del,U) <=> true | fact(['a1:relatedDocuments', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:P33i_was_used_by', Y, X],add,_) \ fact(['a1:P33_used_specific_technique', X, Y],del,U) <=> true | fact(['a1:P33_used_specific_technique', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P33_used_specific_technique', Y, X],add,_) \ fact(['a1:P33i_was_used_by', X, Y],del,U) <=> true | fact(['a1:P33i_was_used_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P111_added', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P129i_is_subject_of', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P9i_forms_part_of', X, _],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P14_carried_out_by', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P126i_was_employed_in', _, X1],add,_) \ fact(['a1:E11_Modification', X1],del,U) <=> true | fact(['a1:E11_Modification', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,_), fact(['a1:referredBySame', X1, X2],add,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,_) \ fact(['a1:relatedManMadeThings', X0, X3],del,U) <=> true | fact(['a1:relatedManMadeThings', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:P58i_defines_section', X, _],add,_) \ fact(['a1:E46_Section_Definition', X],del,U) <=> true | fact(['a1:E46_Section_Definition', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P14i_performed', X, Y],add,_) \ fact(['a1:P11i_participated_in', X, Y],del,U) <=> true | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P139_has_alternative_form', X, _],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P75_possesses', Y, X],add,_) \ fact(['a1:P75i_is_possessed_by', X, Y],del,U) <=> true | fact(['a1:P75i_is_possessed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P75i_is_possessed_by', Y, X],add,_) \ fact(['a1:P75_possesses', X, Y],del,U) <=> true | fact(['a1:P75_possesses', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:position', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P145i_left_by', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P10_falls_within', _, X1],add,_) \ fact(['a1:E4_Period', X1],del,U) <=> true | fact(['a1:E4_Period', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E45_Address', X],add,_) \ fact(['a1:E44_Place_Appellation', X],del,U) <=> true | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:immediatelyFollowingEvent', X, Y],add,_) \ fact(['a2:followingEvent', X, Y],del,U) <=> true | fact(['a2:followingEvent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73i_is_translation_of', _, X1],add,_) \ fact(['a1:E33_Linguistic_Object', X1],del,U) <=> true | fact(['a1:E33_Linguistic_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Employment', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a5:Location', X],add,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],del,U) <=> true | fact(['a5:LocationPeriodOrJurisdiction', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P33i_was_used_by', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:topic', X, _],add,_) \ fact(['a3:Document', X],del,U) <=> true | fact(['a3:Document', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P12_occurred_in_the_presence_of', Y, X],add,_) \ fact(['a1:P12i_was_present_at', X, Y],del,U) <=> true | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P12i_was_present_at', Y, X],add,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U) <=> true | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P117_occurs_during', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P76i_provides_access_to', X, _],add,_) \ fact(['a1:E51_Contact_Point', X],del,U) <=> true | fact(['a1:E51_Contact_Point', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P70_documents', X, _],add,_) \ fact(['a1:E31_Document', X],del,U) <=> true | fact(['a1:E31_Document', X],add,U), applied_rules(1,red).
phase(2), fact(['a5:MediaType', X],add,_) \ fact(['a5:MediaTypeOrExtent', X],del,U) <=> true | fact(['a5:MediaTypeOrExtent', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:maker', _, X1],add,_) \ fact(['a3:Agent', X1],del,U) <=> true | fact(['a3:Agent', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:primaryTopic', X, Y1],add,_), fact(['a3:primaryTopic', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a3:mbox_sha1sum', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108_has_produced', _, X1],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P35i_was_identified_by', _, X1],add,_) \ fact(['a1:E14_Condition_Assessment', X1],del,U) <=> true | fact(['a1:E14_Condition_Assessment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P76_has_contact_point', _, X1],add,_) \ fact(['a1:E51_Contact_Point', X1],del,U) <=> true | fact(['a1:E51_Contact_Point', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E84_Information_Carrier', X],add,_) \ fact(['a1:E22_Man-Made_Object', X],del,U) <=> true | fact(['a1:E22_Man-Made_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P48_has_preferred_identifier', Y, X],add,_) \ fact(['a1:P48i_is_preferred_identifier_of', X, Y],del,U) <=> true | fact(['a1:P48i_is_preferred_identifier_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P48i_is_preferred_identifier_of', Y, X],add,_) \ fact(['a1:P48_has_preferred_identifier', X, Y],del,U) <=> true | fact(['a1:P48_has_preferred_identifier', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:BasMitzvah', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P124i_was_transformed_by', Y, X],add,_) \ fact(['a1:P124_transformed', X, Y],del,U) <=> true | fact(['a1:P124_transformed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P124_transformed', Y, X],add,_) \ fact(['a1:P124i_was_transformed_by', X, Y],del,U) <=> true | fact(['a1:P124i_was_transformed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P92_brought_into_existence', X, Y],add,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U) <=> true | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13_destroyed', X, Y],add,_) \ fact(['a1:P93_took_out_of_existence', X, Y],del,U) <=> true | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P8_took_place_on_or_within', Y, X],add,_) \ fact(['a1:P8i_witnessed', X, Y],del,U) <=> true | fact(['a1:P8i_witnessed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P8i_witnessed', Y, X],add,_) \ fact(['a1:P8_took_place_on_or_within', X, Y],del,U) <=> true | fact(['a1:P8_took_place_on_or_within', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P76i_provides_access_to', Y, X],add,_) \ fact(['a1:P76_has_contact_point', X, Y],del,U) <=> true | fact(['a1:P76_has_contact_point', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P76_has_contact_point', Y, X],add,_) \ fact(['a1:P76i_provides_access_to', X, Y],del,U) <=> true | fact(['a1:P76i_provides_access_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P106i_forms_part_of', _, X1],add,_) \ fact(['a1:E90_Symbolic_Object', X1],del,U) <=> true | fact(['a1:E90_Symbolic_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P56_bears_feature', X, Y],add,_) \ fact(['a1:P46_is_composed_of', X, Y],del,U) <=> true | fact(['a1:P46_is_composed_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P145i_left_by', X, Y],add,_) \ fact(['a1:P11i_participated_in', X, Y],del,U) <=> true | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:mbox', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P53_has_former_or_current_location', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99i_was_dissolved_by', X, _],add,_) \ fact(['a1:E74_Group', X],del,U) <=> true | fact(['a1:E74_Group', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P25_moved', X, Y],add,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U) <=> true | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:immediatelyFollowingEvent', _, X1],add,_) \ fact(['a2:Event', X1],del,U) <=> true | fact(['a2:Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P96_by_mother', _, X1],add,_) \ fact(['a1:E21_Person', X1],del,U) <=> true | fact(['a1:E21_Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:msnChatID', X, Y],add,_) \ fact(['a3:nick', X, Y],del,U) <=> true | fact(['a3:nick', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P146i_lost_member_by', Y, X],add,_) \ fact(['a1:P146_separated_from', X, Y],del,U) <=> true | fact(['a1:P146_separated_from', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P146_separated_from', Y, X],add,_) \ fact(['a1:P146i_lost_member_by', X, Y],del,U) <=> true | fact(['a1:P146i_lost_member_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P40_observed_dimension', _, X1],add,_) \ fact(['a1:E54_Dimension', X1],del,U) <=> true | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:mother', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P33_used_specific_technique', _, X1],add,_) \ fact(['a1:E29_Design_or_Procedure', X1],del,U) <=> true | fact(['a1:E29_Design_or_Procedure', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41i_was_classified_by', X, Y],add,_) \ fact(['a1:P140i_was_attributed_by', X, Y],del,U) <=> true | fact(['a1:P140i_was_attributed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:schoolHomepage', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P52_has_current_owner', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P7_took_place_at', Y, X],add,_) \ fact(['a1:P7i_witnessed', X, Y],del,U) <=> true | fact(['a1:P7i_witnessed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P7i_witnessed', Y, X],add,_) \ fact(['a1:P7_took_place_at', X, Y],del,U) <=> true | fact(['a1:P7_took_place_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95_has_formed', _, X1],add,_) \ fact(['a1:E74_Group', X1],del,U) <=> true | fact(['a1:E74_Group', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:Person', X],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P127i_has_narrower_term', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E6_Destruction', X],add,_) \ fact(['a1:E64_End_of_Existence', X],del,U) <=> true | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P53i_is_former_or_current_location_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P134_continued', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:account', _, X1],add,_) \ fact(['a3:OnlineAccount', X1],del,U) <=> true | fact(['a3:OnlineAccount', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P127_has_broader_term', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P93_took_out_of_existence', _, X1],add,_) \ fact(['a1:E77_Persistent_Item', X1],del,U) <=> true | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P137_exemplifies', Y, X],add,_) \ fact(['a1:P137i_is_exemplified_by', X, Y],del,U) <=> true | fact(['a1:P137i_is_exemplified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P137i_is_exemplified_by', Y, X],add,_) \ fact(['a1:P137_exemplifies', X, Y],del,U) <=> true | fact(['a1:P137_exemplifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P22_transferred_title_to', X, _],add,_) \ fact(['a1:E8_Acquisition', X],del,U) <=> true | fact(['a1:E8_Acquisition', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:accountName', X, _],add,_) \ fact(['a3:OnlineAccount', X],del,U) <=> true | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:mother', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P30i_custody_transferred_through', _, X1],add,_) \ fact(['a1:E10_Transfer_of_Custody', X1],del,U) <=> true | fact(['a1:E10_Transfer_of_Custody', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P86_falls_within', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13i_was_destroyed_by', X, Y],add,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U) <=> true | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P20_had_specific_purpose', Y, X],add,_) \ fact(['a1:P20i_was_purpose_of', X, Y],del,U) <=> true | fact(['a1:P20i_was_purpose_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P20i_was_purpose_of', Y, X],add,_) \ fact(['a1:P20_had_specific_purpose', X, Y],del,U) <=> true | fact(['a1:P20_had_specific_purpose', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P89i_contains', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P5i_forms_part_of', X, _],add,_) \ fact(['a1:E3_Condition_State', X],del,U) <=> true | fact(['a1:E3_Condition_State', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P49i_is_former_or_current_keeper_of', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P128i_is_carried_by', X, _],add,_) \ fact(['a1:E73_Information_Object', X],del,U) <=> true | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Imprisonment', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:tipjar', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,_) \ fact(['a1:P12i_was_present_at', X, Y],del,U) <=> true | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98i_was_born', X, Y],add,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U) <=> true | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:organization', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:concurrentEvent', Y, X],add,_) \ fact(['a2:concurrentEvent', X, Y],del,U) <=> true | fact(['a2:concurrentEvent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:yahooChatID', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P42_assigned', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P91_has_unit', X, _],add,_) \ fact(['a1:E54_Dimension', X],del,U) <=> true | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Retirement', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:tipjar', X, Y],add,_) \ fact(['a3:page', X, Y],del,U) <=> true | fact(['a3:page', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P62_depicts', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:interval', _, X1],add,_) \ fact(['a2:Interval', X1],del,U) <=> true | fact(['a2:Interval', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:olb', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P117i_includes', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P88i_forms_part_of', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:mother', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73i_is_translation_of', X, Y],add,_) \ fact(['a1:P130i_features_are_also_found_on', X, Y],del,U) <=> true | fact(['a1:P130i_features_are_also_found_on', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:father', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135_created_type', X, _],add,_) \ fact(['a1:E83_Type_Creation', X],del,U) <=> true | fact(['a1:E83_Type_Creation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P59i_is_located_on_or_within', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Dismissal', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P96i_gave_birth', _, X1],add,_) \ fact(['a1:E67_Birth', X1],del,U) <=> true | fact(['a1:E67_Birth', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E27_Site', X],add,_) \ fact(['a1:E26_Physical_Feature', X],del,U) <=> true | fact(['a1:E26_Physical_Feature', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:principal', X, X2],add,_), fact(['a2:principal', X, X1],add,_), fact(['a2:IndividualEvent', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a3:msnChatID', _, X1],add,_) \ fact(['rdfs:Literal', X1],del,U) <=> true | fact(['rdfs:Literal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:homepage', Y1, X],add,_), fact(['a3:homepage', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P1i_identifies', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P10_falls_within', X, Y],add,_), fact(['a1:P10_falls_within', Y, Z],add,_) \ fact(['a1:P10_falls_within', X, Z],del,U) <=> true | fact(['a1:P10_falls_within', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P96_by_mother', X, _],add,_) \ fact(['a1:E67_Birth', X],del,U) <=> true | fact(['a1:E67_Birth', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Enrolment', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P75_possesses', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P93i_was_taken_out_of_existence_by', _, X1],add,_) \ fact(['a1:E64_End_of_Existence', X1],del,U) <=> true | fact(['a1:E64_End_of_Existence', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P100_was_death_of', _, X1],add,_) \ fact(['a1:E21_Person', X1],del,U) <=> true | fact(['a1:E21_Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P126i_was_employed_in', X, _],add,_) \ fact(['a1:E57_Material', X],del,U) <=> true | fact(['a1:E57_Material', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P9i_forms_part_of', _, X1],add,_) \ fact(['a1:E4_Period', X1],del,U) <=> true | fact(['a1:E4_Period', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:Person', X],add,_) \ fact(['a10:SpatialThing', X],del,U) <=> true | fact(['a10:SpatialThing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16_used_specific_object', X, Y],add,_) \ fact(['a1:P12_occurred_in_the_presence_of', X, Y],del,U) <=> true | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P92i_was_brought_into_existence_by', X, _],add,_) \ fact(['a1:E77_Persistent_Item', X],del,U) <=> true | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P54i_is_current_permanent_location_of', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P51i_is_former_or_current_owner_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P115i_is_finished_by', X, Y],add,_), fact(['a1:P115i_is_finished_by', Y, Z],add,_) \ fact(['a1:P115i_is_finished_by', X, Z],del,U) <=> true | fact(['a1:P115i_is_finished_by', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P137i_is_exemplified_by', X, Y],add,_) \ fact(['a1:P2i_is_type_of', X, Y],del,U) <=> true | fact(['a1:P2i_is_type_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:concludingEvent', _, X1],add,_) \ fact(['a2:Event', X1],del,U) <=> true | fact(['a2:Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:thumbnail', X, _],add,_) \ fact(['a3:Image', X],del,U) <=> true | fact(['a3:Image', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27i_was_origin_of', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:parent', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P44i_is_condition_of', X, _],add,_) \ fact(['a1:E3_Condition_State', X],del,U) <=> true | fact(['a1:E3_Condition_State', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P144i_gained_member_by', X, Y],add,_) \ fact(['a1:P11i_participated_in', X, Y],del,U) <=> true | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P118i_is_overlapped_in_time_by', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P129i_is_subject_of', _, X1],add,_) \ fact(['a1:E89_Propositional_Object', X1],del,U) <=> true | fact(['a1:E89_Propositional_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99_dissolved', _, X1],add,_) \ fact(['a1:E74_Group', X1],del,U) <=> true | fact(['a1:E74_Group', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P20_had_specific_purpose', _, X1],add,_) \ fact(['a1:E5_Event', X1],del,U) <=> true | fact(['a1:E5_Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98i_was_born', _, X1],add,_) \ fact(['a1:E67_Birth', X1],del,U) <=> true | fact(['a1:E67_Birth', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P32i_was_technique_of', X, Y],add,_) \ fact(['a1:P125i_was_type_of_object_used_in', X, Y],del,U) <=> true | fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16_used_specific_object', X, Y],add,_) \ fact(['a1:P15_was_influenced_by', X, Y],del,U) <=> true | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P65_shows_visual_item', X, _],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P129i_is_subject_of', X, Y],add,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],del,U) <=> true | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P134i_was_continued_by', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:msnChatID', Y1, X],add,_), fact(['a3:msnChatID', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P87_is_identified_by', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:Person', X],add,_), fact(['a3:Project', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E33_Linguistic_Object', X],add,_) \ fact(['a1:E73_Information_Object', X],del,U) <=> true | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:geekcode', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:officiator', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P114_is_equal_in_time_to', Y, X],add,_) \ fact(['a1:P114_is_equal_in_time_to', X, Y],del,U) <=> true | fact(['a1:P114_is_equal_in_time_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:partner', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:spectator', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P28i_surrendered_custody_through', X, Y],add,_) \ fact(['a1:P14i_performed', X, Y],del,U) <=> true | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P136i_supported_type_creation', X, Y],add,_) \ fact(['a1:P15i_influenced', X, Y],del,U) <=> true | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P72i_is_language_of', X, _],add,_) \ fact(['a1:E56_Language', X],del,U) <=> true | fact(['a1:E56_Language', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P96_by_mother', X, Y],add,_) \ fact(['a1:P11_had_participant', X, Y],del,U) <=> true | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P116_starts', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:img', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P100i_died_in', X, _],add,_) \ fact(['a1:E21_Person', X],del,U) <=> true | fact(['a1:E21_Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P96i_gave_birth', X, _],add,_) \ fact(['a1:E21_Person', X],del,U) <=> true | fact(['a1:E21_Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108i_was_produced_by', X, Y],add,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U) <=> true | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:familyName', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P148_has_component', X, Y],add,_), fact(['a1:P148_has_component', Y, Z],add,_) \ fact(['a1:P148_has_component', X, Z],del,U) <=> true | fact(['a1:P148_has_component', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P55i_currently_holds', _, X1],add,_) \ fact(['a1:E19_Physical_Object', X1],del,U) <=> true | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Event', X],add,_) \ fact(['a11:Event', X],del,U) <=> true | fact(['a11:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P97i_was_father_for', Y, X],add,_) \ fact(['a1:P97_from_father', X, Y],del,U) <=> true | fact(['a1:P97_from_father', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P97_from_father', Y, X],add,_) \ fact(['a1:P97i_was_father_for', X, Y],del,U) <=> true | fact(['a1:P97i_was_father_for', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P26_moved_to', X, _],add,_) \ fact(['a1:E9_Move', X],del,U) <=> true | fact(['a1:E9_Move', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E52_Time-Span', X],add,_), fact(['a1:E53_Place', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P89_falls_within', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E56_Language', X],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:spectator', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P40i_was_observed_in', Y, X],add,_) \ fact(['a1:P40_observed_dimension', X, Y],del,U) <=> true | fact(['a1:P40_observed_dimension', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P40_observed_dimension', Y, X],add,_) \ fact(['a1:P40i_was_observed_in', X, Y],del,U) <=> true | fact(['a1:P40i_was_observed_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,_), fact(['a1:P67_refers_to', X1, X2],add,_), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,_) \ fact(['a1:relatedManMadeThings', X0, X3],del,U) <=> true | fact(['a1:relatedManMadeThings', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a2:Adoption', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P42i_was_assigned_by', X, Y],add,_) \ fact(['a1:P141i_was_assigned_by', X, Y],del,U) <=> true | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P95_has_formed', X, Y],add,_) \ fact(['a1:P92_brought_into_existence', X, Y],del,U) <=> true | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P31i_was_modified_by', X, Y],add,_) \ fact(['a1:P12i_was_present_at', X, Y],del,U) <=> true | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P56i_is_found_on', X, Y],add,_) \ fact(['a1:P46i_forms_part_of', X, Y],del,U) <=> true | fact(['a1:P46i_forms_part_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P117_occurs_during', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99_dissolved', X, Y],add,_) \ fact(['a1:P93_took_out_of_existence', X, Y],del,U) <=> true | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41_classified', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:msnChatID', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P89i_contains', X, Y],add,_), fact(['a1:P89i_contains', Y, Z],add,_) \ fact(['a1:P89i_contains', X, Z],del,U) <=> true | fact(['a1:P89i_contains', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E31_Document', X0, X1],add,_), fact(['a1:P67_refers_to', X1, X2],add,_), fact(['a1:P_E31_Document', X2, X3],add,_) \ fact(['a1:relatedDocuments', X0, X3],del,U) <=> true | fact(['a1:relatedDocuments', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:P137i_is_exemplified_by', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P130_shows_features_of', Y, X],add,_) \ fact(['a1:P130i_features_are_also_found_on', X, Y],del,U) <=> true | fact(['a1:P130i_features_are_also_found_on', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P130i_features_are_also_found_on', Y, X],add,_) \ fact(['a1:P130_shows_features_of', X, Y],del,U) <=> true | fact(['a1:P130_shows_features_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P52i_is_current_owner_of', X, Y],add,_) \ fact(['a1:P51i_is_former_or_current_owner_of', X, Y],del,U) <=> true | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P46i_forms_part_of', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P19i_was_made_for', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E17_Type_Assignment', X],add,_) \ fact(['a1:E13_Attribute_Assignment', X],del,U) <=> true | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E32_Authority_Document', X],add,_) \ fact(['a1:E31_Document', X],del,U) <=> true | fact(['a1:E31_Document', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135i_was_created_by', Y, X],add,_) \ fact(['a1:P135_created_type', X, Y],del,U) <=> true | fact(['a1:P135_created_type', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135_created_type', Y, X],add,_) \ fact(['a1:P135i_was_created_by', X, Y],del,U) <=> true | fact(['a1:P135i_was_created_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P120_occurs_before', Y, X],add,_) \ fact(['a1:P120i_occurs_after', X, Y],del,U) <=> true | fact(['a1:P120i_occurs_after', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P120i_occurs_after', Y, X],add,_) \ fact(['a1:P120_occurs_before', X, Y],del,U) <=> true | fact(['a1:P120_occurs_before', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P107i_is_current_or_former_member_of', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:gender', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P19i_was_made_for', X, _],add,_) \ fact(['a1:E71_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P86_falls_within', X, Y],add,_), fact(['a1:P86_falls_within', Y, Z],add,_) \ fact(['a1:P86_falls_within', X, Z],del,U) <=> true | fact(['a1:P86_falls_within', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P120_occurs_before', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E19_Physical_Object', X],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P7i_witnessed', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P75i_is_possessed_by', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['rdfs:ContainerMembershipProperty', X],add,_) \ fact(['rdf:Property', X],del,U) <=> true | fact(['rdf:Property', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16_used_specific_object', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27i_was_origin_of', _, X1],add,_) \ fact(['a1:E9_Move', X1],del,U) <=> true | fact(['a1:E9_Move', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P92i_was_brought_into_existence_by', _, X1],add,_) \ fact(['a1:E63_Beginning_of_Existence', X1],del,U) <=> true | fact(['a1:E63_Beginning_of_Existence', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P113i_was_removed_by', _, X1],add,_) \ fact(['a1:E80_Part_Removal', X1],del,U) <=> true | fact(['a1:E80_Part_Removal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P103_was_intended_for', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:child', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:homepage', X, Y],add,_) \ fact(['a3:page', X, Y],del,U) <=> true | fact(['a3:page', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:partner', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39i_was_measured_by', X, Y],add,_) \ fact(['a1:P140i_was_attributed_by', X, Y],del,U) <=> true | fact(['a1:P140i_was_attributed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E48_Place_Name', X],add,_) \ fact(['a1:P_E53_Place', X, X],del,U) <=> true | fact(['a1:P_E53_Place', X, X],add,U), applied_rules(1,red).
phase(2), fact(['a3:schoolHomepage', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P34_concerned', X, _],add,_) \ fact(['a1:E14_Condition_Assessment', X],del,U) <=> true | fact(['a1:E14_Condition_Assessment', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Redundancy', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P28_custody_surrendered_by', Y, X],add,_) \ fact(['a1:P28i_surrendered_custody_through', X, Y],del,U) <=> true | fact(['a1:P28i_surrendered_custody_through', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P28i_surrendered_custody_through', Y, X],add,_) \ fact(['a1:P28_custody_surrendered_by', X, Y],del,U) <=> true | fact(['a1:P28_custody_surrendered_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27_moved_from', X, Y],add,_), fact(['a1:P27_moved_from', Y, Z],add,_) \ fact(['a1:P27_moved_from', X, Z],del,U) <=> true | fact(['a1:P27_moved_from', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:E80_Part_Removal', X],add,_) \ fact(['a1:E11_Modification', X],del,U) <=> true | fact(['a1:E11_Modification', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P102i_is_title_of', X, _],add,_) \ fact(['a1:E35_Title', X],del,U) <=> true | fact(['a1:E35_Title', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P116i_is_started_by', X, Y],add,_), fact(['a1:P116i_is_started_by', Y, Z],add,_) \ fact(['a1:P116i_is_started_by', X, Z],del,U) <=> true | fact(['a1:P116i_is_started_by', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:E44_Place_Appellation', X],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P54_has_current_permanent_location', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P38i_was_deassigned_by', Y, X],add,_) \ fact(['a1:P38_deassigned', X, Y],del,U) <=> true | fact(['a1:P38_deassigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P38_deassigned', Y, X],add,_) \ fact(['a1:P38i_was_deassigned_by', X, Y],del,U) <=> true | fact(['a1:P38i_was_deassigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P97i_was_father_for', _, X1],add,_) \ fact(['a1:E67_Birth', X1],del,U) <=> true | fact(['a1:E67_Birth', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P4_has_time-span', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Formation', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:agent', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P137_exemplifies', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P137i_is_exemplified_by', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P80_end_is_qualified_by', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:knows', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Disbanding', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P148i_is_component_of', X, Y],add,_), fact(['a1:P148i_is_component_of', Y, Z],add,_) \ fact(['a1:P148i_is_component_of', X, Z],del,U) <=> true | fact(['a1:P148i_is_component_of', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a3:yahooChatID', X, Y],add,_) \ fact(['a3:nick', X, Y],del,U) <=> true | fact(['a3:nick', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:death', X, Y],add,_) \ fact(['a2:event', X, Y],del,U) <=> true | fact(['a2:event', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P89_falls_within', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P115_finishes', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:death', _, X1],add,_) \ fact(['a2:Death', X1],del,U) <=> true | fact(['a2:Death', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P35i_was_identified_by', X, Y],add,_) \ fact(['a1:P141i_was_assigned_by', X, Y],del,U) <=> true | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P111_added', X, _],add,_) \ fact(['a1:E79_Part_Addition', X],del,U) <=> true | fact(['a1:E79_Part_Addition', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P37i_was_assigned_by', X, _],add,_) \ fact(['a1:E42_Identifier', X],del,U) <=> true | fact(['a1:E42_Identifier', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P42_assigned', X, _],add,_) \ fact(['a1:E17_Type_Assignment', X],del,U) <=> true | fact(['a1:E17_Type_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E73_Information_Object', X],add,_) \ fact(['a1:E90_Symbolic_Object', X],del,U) <=> true | fact(['a1:E90_Symbolic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P110_augmented', X, Y],add,_) \ fact(['a1:P31_has_modified', X, Y],del,U) <=> true | fact(['a1:P31_has_modified', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P78i_identifies', X, Y],add,_) \ fact(['a1:P1i_identifies', X, Y],del,U) <=> true | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P91i_is_unit_of', _, X1],add,_) \ fact(['a1:E54_Dimension', X1],del,U) <=> true | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P146_separated_from', X, _],add,_) \ fact(['a1:E86_Leaving', X],del,U) <=> true | fact(['a1:E86_Leaving', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:position', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P86i_contains', _, X1],add,_) \ fact(['a1:E52_Time-Span', X1],del,U) <=> true | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:mbox_sha1sum', Y1, X],add,_), fact(['a3:mbox_sha1sum', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:E74_Group', X],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P37i_was_assigned_by', X, Y],add,_) \ fact(['a1:P141i_was_assigned_by', X, Y],del,U) <=> true | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:yahooChatID', _, X1],add,_) \ fact(['rdfs:Literal', X1],del,U) <=> true | fact(['rdfs:Literal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P127i_has_narrower_term', X, Y],add,_), fact(['a1:P127i_has_narrower_term', Y, Z],add,_) \ fact(['a1:P127i_has_narrower_term', X, Z],del,U) <=> true | fact(['a1:P127i_has_narrower_term', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a3:member', _, X1],add,_) \ fact(['a3:Agent', X1],del,U) <=> true | fact(['a3:Agent', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P21i_was_purpose_of', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E29_Design_or_Procedure', X],add,_) \ fact(['a1:E73_Information_Object', X],del,U) <=> true | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Execution', X],add,_) \ fact(['a2:Death', X],del,U) <=> true | fact(['a2:Death', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P71_lists', Y, X],add,_) \ fact(['a1:P71i_is_listed_in', X, Y],del,U) <=> true | fact(['a1:P71i_is_listed_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P71i_is_listed_in', Y, X],add,_) \ fact(['a1:P71_lists', X, Y],del,U) <=> true | fact(['a1:P71_lists', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P84_had_at_most_duration', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P101i_was_use_of', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P142_used_constituent', Y, X],add,_) \ fact(['a1:P142i_was_used_in', X, Y],del,U) <=> true | fact(['a1:P142i_was_used_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P142i_was_used_in', Y, X],add,_) \ fact(['a1:P142_used_constituent', X, Y],del,U) <=> true | fact(['a1:P142_used_constituent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:position', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P147i_was_curated_by', _, X1],add,_) \ fact(['a1:E87_Curation_Activity', X1],del,U) <=> true | fact(['a1:E87_Curation_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P49_has_former_or_current_keeper', Y, X],add,_) \ fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],del,U) <=> true | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P49i_is_former_or_current_keeper_of', Y, X],add,_) \ fact(['a1:P49_has_former_or_current_keeper', X, Y],del,U) <=> true | fact(['a1:P49_has_former_or_current_keeper', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P38i_was_deassigned_by', X, Y],add,_) \ fact(['a1:P141i_was_assigned_by', X, Y],del,U) <=> true | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P145i_left_by', _, X1],add,_) \ fact(['a1:E86_Leaving', X1],del,U) <=> true | fact(['a1:E86_Leaving', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P91_has_unit', X, X2],add,_), fact(['a1:P91_has_unit', X, X1],add,_), fact(['a1:E54_Dimension', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a2:relationship', _, X1],add,_) \ fact(['a2:Relationship', X1],del,U) <=> true | fact(['a2:Relationship', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73i_is_translation_of', X, _],add,_) \ fact(['a1:E33_Linguistic_Object', X],del,U) <=> true | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P75i_is_possessed_by', X, _],add,_) \ fact(['a1:E30_Right', X],del,U) <=> true | fact(['a1:E30_Right', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:principal', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:OnlineEcommerceAccount', X],add,_) \ fact(['a3:OnlineAccount', X],del,U) <=> true | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P2i_is_type_of', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E31_Document', X],add,_) \ fact(['a1:P_E31_Document', X, X],del,U) <=> true | fact(['a1:P_E31_Document', X, X],add,U), applied_rules(1,red).
phase(2), fact(['a2:principal', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P144i_gained_member_by', X, _],add,_) \ fact(['a1:E74_Group', X],del,U) <=> true | fact(['a1:E74_Group', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P74i_is_current_or_former_residence_of', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:holdsAccount', _, X1],add,_) \ fact(['a3:OnlineAccount', X1],del,U) <=> true | fact(['a3:OnlineAccount', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P90_has_value', X, _],add,_) \ fact(['a1:E54_Dimension', X],del,U) <=> true | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:weblog', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41i_was_classified_by', _, X1],add,_) \ fact(['a1:E17_Type_Assignment', X1],del,U) <=> true | fact(['a1:E17_Type_Assignment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P123_resulted_in', X, Y],add,_) \ fact(['a1:P92_brought_into_existence', X, Y],del,U) <=> true | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P93_took_out_of_existence', X, _],add,_) \ fact(['a1:E64_End_of_Existence', X],del,U) <=> true | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:concurrentEvent', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P49i_is_former_or_current_keeper_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['rdfs:Datatype', X],add,_) \ fact(['rdfs:Class', X],del,U) <=> true | fact(['rdfs:Class', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P111i_was_added_by', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:father', X, _],add,_), fact(['a2:mother', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P125i_was_type_of_object_used_in', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P145_separated', X, Y],add,_) \ fact(['a1:P11_had_participant', X, Y],del,U) <=> true | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P57_has_number_of_parts', X, _],add,_) \ fact(['a1:E19_Physical_Object', X],del,U) <=> true | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39_measured', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Investiture', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P147_curated', X, _],add,_) \ fact(['a1:E87_Curation_Activity', X],del,U) <=> true | fact(['a1:E87_Curation_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P138i_has_representation', _, X1],add,_) \ fact(['a1:E36_Visual_Item', X1],del,U) <=> true | fact(['a1:E36_Visual_Item', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67i_is_referred_to_by', Y, X],add,_) \ fact(['a1:P67_refers_to', X, Y],del,U) <=> true | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67_refers_to', Y, X],add,_) \ fact(['a1:P67i_is_referred_to_by', X, Y],del,U) <=> true | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P50_has_current_keeper', Y, X],add,_) \ fact(['a1:P50i_is_current_keeper_of', X, Y],del,U) <=> true | fact(['a1:P50i_is_current_keeper_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P50i_is_current_keeper_of', Y, X],add,_) \ fact(['a1:P50_has_current_keeper', X, Y],del,U) <=> true | fact(['a1:P50_has_current_keeper', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P138_represents', X, _],add,_) \ fact(['a1:E36_Visual_Item', X],del,U) <=> true | fact(['a1:E36_Visual_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73_has_translation', X, Y],add,_) \ fact(['a1:P130_shows_features_of', X, Y],del,U) <=> true | fact(['a1:P130_shows_features_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:concurrentEvent', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a5:PeriodOfTime', X],add,_) \ fact(['a5:LocationPeriodOrJurisdiction', X],del,U) <=> true | fact(['a5:LocationPeriodOrJurisdiction', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P143i_was_joined_by', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P121_overlaps_with', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P34i_was_assessed_by', Y, X],add,_) \ fact(['a1:P34_concerned', X, Y],del,U) <=> true | fact(['a1:P34_concerned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P34_concerned', Y, X],add,_) \ fact(['a1:P34i_was_assessed_by', X, Y],del,U) <=> true | fact(['a1:P34i_was_assessed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108i_was_produced_by', _, X1],add,_) \ fact(['a1:E12_Production', X1],del,U) <=> true | fact(['a1:E12_Production', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P140i_was_attributed_by', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P117i_includes', X, Y],add,_), fact(['a1:P117i_includes', Y, Z],add,_) \ fact(['a1:P117i_includes', X, Z],del,U) <=> true | fact(['a1:P117i_includes', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P102i_is_title_of', X, Y],add,_) \ fact(['a1:P1i_identifies', X, Y],del,U) <=> true | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67_refers_to', X0, X1],add,_), fact(['a1:P67_refers_to', X2, X1],add,_) \ fact(['a1:referToSame', X0, X2],del,U) <=> true | fact(['a1:referToSame', X0, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:E71_Man-Made_Thing', X],add,_) \ fact(['a1:E70_Thing', X],del,U) <=> true | fact(['a1:E70_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P141_assigned', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P74_has_current_or_former_residence', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P84i_was_maximum_duration_of', Y, X],add,_) \ fact(['a1:P84_had_at_most_duration', X, Y],del,U) <=> true | fact(['a1:P84_had_at_most_duration', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P84_had_at_most_duration', Y, X],add,_) \ fact(['a1:P84i_was_maximum_duration_of', X, Y],del,U) <=> true | fact(['a1:P84i_was_maximum_duration_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:weblog', X, Y],add,_) \ fact(['a3:page', X, Y],del,U) <=> true | fact(['a3:page', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E77_Persistent_Item', X],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P104i_applies_to', Y, X],add,_) \ fact(['a1:P104_is_subject_to', X, Y],del,U) <=> true | fact(['a1:P104_is_subject_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P104_is_subject_to', Y, X],add,_) \ fact(['a1:P104i_applies_to', X, Y],del,U) <=> true | fact(['a1:P104i_applies_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E87_Curation_Activity', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:isPrimaryTopicOf', Y1, X],add,_), fact(['a3:isPrimaryTopicOf', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a2:Relationship', X],add,_) \ fact(['a6:Relationship', X],del,U) <=> true | fact(['a6:Relationship', X],add,U), applied_rules(1,red).
phase(2), fact(['a6:Relationship', X],add,_) \ fact(['a2:Relationship', X],del,U) <=> true | fact(['a2:Relationship', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:logo', Y1, X],add,_), fact(['a3:logo', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P92_brought_into_existence', X, _],add,_) \ fact(['a1:E63_Beginning_of_Existence', X],del,U) <=> true | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E48_Place_Name', X],add,_) \ fact(['a1:E44_Place_Appellation', X],del,U) <=> true | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P143i_was_joined_by', X, Y],add,_) \ fact(['a1:P11i_participated_in', X, Y],del,U) <=> true | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E2_Temporal_Entity', X],add,_), fact(['a1:E77_Persistent_Item', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P54i_is_current_permanent_location_of', _, X1],add,_) \ fact(['a1:E19_Physical_Object', X1],del,U) <=> true | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P145_separated', X, X2],add,_), fact(['a1:P145_separated', X, X1],add,_), fact(['a1:E86_Leaving', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P99i_was_dissolved_by', X, Y],add,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U) <=> true | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:Inauguration', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P125_used_object_of_type', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P25i_moved_by', _, X1],add,_) \ fact(['a1:E9_Move', X1],del,U) <=> true | fact(['a1:E9_Move', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P72i_is_language_of', Y, X],add,_) \ fact(['a1:P72_has_language', X, Y],del,U) <=> true | fact(['a1:P72_has_language', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P72_has_language', Y, X],add,_) \ fact(['a1:P72i_is_language_of', X, Y],del,U) <=> true | fact(['a1:P72i_is_language_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P101i_was_use_of', _, X1],add,_) \ fact(['a1:E70_Thing', X1],del,U) <=> true | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P123i_resulted_from', X, _],add,_) \ fact(['a1:E77_Persistent_Item', X],del,U) <=> true | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E66_Formation', X],add,_) \ fact(['a1:E63_Beginning_of_Existence', X],del,U) <=> true | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P1i_identifies', X, _],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a5:SizeOrDuration', X],add,_) \ fact(['a5:MediaTypeOrExtent', X],del,U) <=> true | fact(['a5:MediaTypeOrExtent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P92_brought_into_existence', Y, X],add,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U) <=> true | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P92i_was_brought_into_existence_by', Y, X],add,_) \ fact(['a1:P92_brought_into_existence', X, Y],del,U) <=> true | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:icqChatID', Y1, X],add,_), fact(['a3:icqChatID', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a3:OnlineChatAccount', X],add,_) \ fact(['a3:OnlineAccount', X],del,U) <=> true | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P97_from_father', _, X1],add,_) \ fact(['a1:E21_Person', X1],del,U) <=> true | fact(['a1:E21_Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P65i_is_shown_by', _, X1],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P86i_contains', X, Y],add,_), fact(['a1:P86i_contains', Y, Z],add,_) \ fact(['a1:P86i_contains', X, Z],del,U) <=> true | fact(['a1:P86i_contains', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a2:Coronation', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P148i_is_component_of', X, _],add,_) \ fact(['a1:E89_Propositional_Object', X],del,U) <=> true | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P34i_was_assessed_by', _, X1],add,_) \ fact(['a1:E14_Condition_Assessment', X1],del,U) <=> true | fact(['a1:E14_Condition_Assessment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P49_has_former_or_current_keeper', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P43i_is_dimension_of', _, X1],add,_) \ fact(['a1:E70_Thing', X1],del,U) <=> true | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P143i_was_joined_by', _, X1],add,_) \ fact(['a1:E85_Joining', X1],del,U) <=> true | fact(['a1:E85_Joining', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P21_had_general_purpose', Y, X],add,_) \ fact(['a1:P21i_was_purpose_of', X, Y],del,U) <=> true | fact(['a1:P21i_was_purpose_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P21i_was_purpose_of', Y, X],add,_) \ fact(['a1:P21_had_general_purpose', X, Y],del,U) <=> true | fact(['a1:P21_had_general_purpose', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P87i_identifies', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Funeral', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P11i_participated_in', Y, X],add,_) \ fact(['a1:P11_had_participant', X, Y],del,U) <=> true | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P11_had_participant', Y, X],add,_) \ fact(['a1:P11i_participated_in', X, Y],del,U) <=> true | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P111_added', Y, X],add,_) \ fact(['a1:P111i_was_added_by', X, Y],del,U) <=> true | fact(['a1:P111i_was_added_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P111i_was_added_by', Y, X],add,_) \ fact(['a1:P111_added', X, Y],del,U) <=> true | fact(['a1:P111_added', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67_refers_to', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E73_Information_Object', X],add,_) \ fact(['a1:P_E73_Information_Object', X, X],del,U) <=> true | fact(['a1:P_E73_Information_Object', X, X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P113_removed', X, _],add,_) \ fact(['a1:E80_Part_Removal', X],del,U) <=> true | fact(['a1:E80_Part_Removal', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P142i_was_used_in', X, Y],add,_) \ fact(['a1:P16i_was_used_for', X, Y],del,U) <=> true | fact(['a1:P16i_was_used_for', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:page', Y, X],add,_) \ fact(['a3:topic', X, Y],del,U) <=> true | fact(['a3:topic', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:topic', Y, X],add,_) \ fact(['a3:page', X, Y],del,U) <=> true | fact(['a3:page', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135i_was_created_by', X, Y],add,_) \ fact(['a1:P94i_was_created_by', X, Y],del,U) <=> true | fact(['a1:P94i_was_created_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P101_had_as_general_use', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:homepage', X, Y],add,_) \ fact(['a3:isPrimaryTopicOf', X, Y],del,U) <=> true | fact(['a3:isPrimaryTopicOf', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P127i_has_narrower_term', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P25i_moved_by', Y, X],add,_) \ fact(['a1:P25_moved', X, Y],del,U) <=> true | fact(['a1:P25_moved', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P25_moved', Y, X],add,_) \ fact(['a1:P25i_moved_by', X, Y],del,U) <=> true | fact(['a1:P25i_moved_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P3_has_note', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P38_deassigned', X, Y],add,_) \ fact(['a1:P141_assigned', X, Y],del,U) <=> true | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E42_Identifier', X],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P148_has_component', X, _],add,_) \ fact(['a1:E89_Propositional_Object', X],del,U) <=> true | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P122_borders_with', Y, X],add,_) \ fact(['a1:P122_borders_with', X, Y],del,U) <=> true | fact(['a1:P122_borders_with', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P59i_is_located_on_or_within', X, X2],add,_), fact(['a1:P59i_is_located_on_or_within', X, X1],add,_), fact(['a1:E53_Place', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P26i_was_destination_of', _, X1],add,_) \ fact(['a1:E9_Move', X1],del,U) <=> true | fact(['a1:E9_Move', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:accountServiceHomepage', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P68_foresees_use_of', Y, X],add,_) \ fact(['a1:P68i_use_foreseen_by', X, Y],del,U) <=> true | fact(['a1:P68i_use_foreseen_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P68i_use_foreseen_by', Y, X],add,_) \ fact(['a1:P68_foresees_use_of', X, Y],del,U) <=> true | fact(['a1:P68_foresees_use_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:eventInterval', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P128_carries', _, X1],add,_) \ fact(['a1:E73_Information_Object', X1],del,U) <=> true | fact(['a1:E73_Information_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E65_Creation', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:mbox_sha1sum', _, X1],add,_) \ fact(['rdfs:Literal', X1],del,U) <=> true | fact(['rdfs:Literal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:interval', X, _],add,_) \ fact(['a2:Relationship', X],del,U) <=> true | fact(['a2:Relationship', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P67_refers_to', X, Y],add,_), fact(['a1:P67_refers_to', Y, Z],add,_) \ fact(['a1:P67_refers_to', X, Z],del,U) <=> true | fact(['a1:P67_refers_to', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:E12_Production', X],add,_) \ fact(['a1:E11_Modification', X],del,U) <=> true | fact(['a1:E11_Modification', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P12i_was_present_at', X, _],add,_) \ fact(['a1:E77_Persistent_Item', X],del,U) <=> true | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P48_has_preferred_identifier', X, X2],add,_), fact(['a1:P48_has_preferred_identifier', X, X1],add,_), fact(['a1:E1_CRM_Entity', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P148_has_component', _, X1],add,_) \ fact(['a1:E89_Propositional_Object', X1],del,U) <=> true | fact(['a1:E89_Propositional_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P12_occurred_in_the_presence_of', _, X1],add,_) \ fact(['a1:E77_Persistent_Item', X1],del,U) <=> true | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P31i_was_modified_by', X, _],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P94i_was_created_by', X, _],add,_) \ fact(['a1:E28_Conceptual_Object', X],del,U) <=> true | fact(['a1:E28_Conceptual_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P107_has_current_or_former_member', X, _],add,_) \ fact(['a1:E74_Group', X],del,U) <=> true | fact(['a1:E74_Group', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P103i_was_intention_of', X, _],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P12i_was_present_at', _, X1],add,_) \ fact(['a1:E5_Event', X1],del,U) <=> true | fact(['a1:E5_Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P42_assigned', X, Y],add,_) \ fact(['a1:P141_assigned', X, Y],del,U) <=> true | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P41_classified', X, _],add,_) \ fact(['a1:E17_Type_Assignment', X],del,U) <=> true | fact(['a1:E17_Type_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P62i_is_depicted_by', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P4i_is_time-span_of', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P106i_forms_part_of', X, _],add,_) \ fact(['a1:E90_Symbolic_Object', X],del,U) <=> true | fact(['a1:E90_Symbolic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E26_Physical_Feature', X],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:immediatelyPrecedingEvent', X, Y],add,_) \ fact(['a2:precedingEvent', X, Y],del,U) <=> true | fact(['a2:precedingEvent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:Resignation', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:BarMitzvah', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E2_Temporal_Entity', X],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P123i_resulted_from', X, Y],add,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U) <=> true | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E54_Dimension', X],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P131i_identifies', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Baptism', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P122_borders_with', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P94_has_created', X, Y],add,_) \ fact(['a1:P92_brought_into_existence', X, Y],del,U) <=> true | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P115_finishes', X, Y],add,_), fact(['a1:P115_finishes', Y, Z],add,_) \ fact(['a1:P115_finishes', X, Z],del,U) <=> true | fact(['a1:P115_finishes', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a3:openid', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P1i_identifies', Y, X],add,_) \ fact(['a1:P1_is_identified_by', X, Y],del,U) <=> true | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P1_is_identified_by', Y, X],add,_) \ fact(['a1:P1i_identifies', X, Y],del,U) <=> true | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P52_has_current_owner', X, Y],add,_) \ fact(['a1:P51_has_former_or_current_owner', X, Y],del,U) <=> true | fact(['a1:P51_has_former_or_current_owner', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P102i_is_title_of', Y, X],add,_) \ fact(['a1:P102_has_title', X, Y],del,U) <=> true | fact(['a1:P102_has_title', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P102_has_title', Y, X],add,_) \ fact(['a1:P102i_is_title_of', X, Y],del,U) <=> true | fact(['a1:P102i_is_title_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P59_has_section', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P79_beginning_is_qualified_by', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:jabberID', Y1, X],add,_), fact(['a3:jabberID', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P140_assigned_attribute_to', Y, X],add,_) \ fact(['a1:P140i_was_attributed_by', X, Y],del,U) <=> true | fact(['a1:P140i_was_attributed_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P140i_was_attributed_by', Y, X],add,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],del,U) <=> true | fact(['a1:P140_assigned_attribute_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98_brought_into_life', _, X1],add,_) \ fact(['a1:E21_Person', X1],del,U) <=> true | fact(['a1:E21_Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P8_took_place_on_or_within', X, _],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P8_took_place_on_or_within', _, X1],add,_) \ fact(['a1:E19_Physical_Object', X1],del,U) <=> true | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E22_Man-Made_Object', X],add,_) \ fact(['a1:E19_Physical_Object', X],del,U) <=> true | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P114_is_equal_in_time_to', X, Y],add,_), fact(['a1:P114_is_equal_in_time_to', Y, Z],add,_) \ fact(['a1:P114_is_equal_in_time_to', X, Z],del,U) <=> true | fact(['a1:P114_is_equal_in_time_to', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E73_Information_Object', X0, X1],add,_), fact(['a1:referredBySame', X1, X2],add,_), fact(['a1:P_E73_Information_Object', X2, X3],add,_) \ fact(['a1:relatedInformationObjects', X0, X3],del,U) <=> true | fact(['a1:relatedInformationObjects', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a2:Burial', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P140i_was_attributed_by', _, X1],add,_) \ fact(['a1:E13_Attribute_Assignment', X1],del,U) <=> true | fact(['a1:E13_Attribute_Assignment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E53_Place', X],add,_) \ fact(['a1:P_E53_Place', X, X],del,U) <=> true | fact(['a1:P_E53_Place', X, X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P23_transferred_title_from', Y, X],add,_) \ fact(['a1:P23i_surrendered_title_through', X, Y],del,U) <=> true | fact(['a1:P23i_surrendered_title_through', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P23i_surrendered_title_through', Y, X],add,_) \ fact(['a1:P23_transferred_title_from', X, Y],del,U) <=> true | fact(['a1:P23_transferred_title_from', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27i_was_origin_of', X, Y],add,_), fact(['a1:P27i_was_origin_of', Y, Z],add,_) \ fact(['a1:P27i_was_origin_of', X, Z],del,U) <=> true | fact(['a1:P27i_was_origin_of', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P33i_was_used_by', X, _],add,_) \ fact(['a1:E29_Design_or_Procedure', X],del,U) <=> true | fact(['a1:E29_Design_or_Procedure', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P74i_is_current_or_former_residence_of', Y, X],add,_) \ fact(['a1:P74_has_current_or_former_residence', X, Y],del,U) <=> true | fact(['a1:P74_has_current_or_former_residence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P74_has_current_or_former_residence', Y, X],add,_) \ fact(['a1:P74i_is_current_or_former_residence_of', X, Y],del,U) <=> true | fact(['a1:P74i_is_current_or_former_residence_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E90_Symbolic_Object', X],add,_) \ fact(['a1:E28_Conceptual_Object', X],del,U) <=> true | fact(['a1:E28_Conceptual_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P107_has_current_or_former_member', Y, X],add,_) \ fact(['a1:P107i_is_current_or_former_member_of', X, Y],del,U) <=> true | fact(['a1:P107i_is_current_or_former_member_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P107i_is_current_or_former_member_of', Y, X],add,_) \ fact(['a1:P107_has_current_or_former_member', X, Y],del,U) <=> true | fact(['a1:P107_has_current_or_former_member', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P131i_identifies', X, Y],add,_) \ fact(['a1:P1i_identifies', X, Y],del,U) <=> true | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:keywords', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P87_is_identified_by', _, X1],add,_) \ fact(['a1:E44_Place_Appellation', X1],del,U) <=> true | fact(['a1:E44_Place_Appellation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P15i_influenced', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P109_has_current_or_former_curator', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P141i_was_assigned_by', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E16_Measurement', X],add,_) \ fact(['a1:E13_Attribute_Assignment', X],del,U) <=> true | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P124_transformed', _, X1],add,_) \ fact(['a1:E77_Persistent_Item', X1],del,U) <=> true | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P120i_occurs_after', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E53_Place', X0, X1],add,_), fact(['a1:P67_refers_to', X1, X2],add,_), fact(['a1:P_E53_Place', X2, X3],add,_) \ fact(['a1:relatedPlaces', X0, X3],del,U) <=> true | fact(['a1:relatedPlaces', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a5:Agent', X],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:Agent', X],add,_) \ fact(['a5:Agent', X],del,U) <=> true | fact(['a5:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P62_depicts', X, _],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P65_shows_visual_item', _, X1],add,_) \ fact(['a1:E36_Visual_Item', X1],del,U) <=> true | fact(['a1:E36_Visual_Item', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:initiatingEvent', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P11i_participated_in', _, X1],add,_) \ fact(['a1:E5_Event', X1],del,U) <=> true | fact(['a1:E5_Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39_measured', X, Y],add,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],del,U) <=> true | fact(['a1:P140_assigned_attribute_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P136i_supported_type_creation', _, X1],add,_) \ fact(['a1:E83_Type_Creation', X1],del,U) <=> true | fact(['a1:E83_Type_Creation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E55_Type', X],add,_) \ fact(['a1:E28_Conceptual_Object', X],del,U) <=> true | fact(['a1:E28_Conceptual_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:officiator', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:relatedPlaces', Y, X],add,_) \ fact(['a1:relatedPlaces', X, Y],del,U) <=> true | fact(['a1:relatedPlaces', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P147_curated', Y, X],add,_) \ fact(['a1:P147i_was_curated_by', X, Y],del,U) <=> true | fact(['a1:P147i_was_curated_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P147i_was_curated_by', Y, X],add,_) \ fact(['a1:P147_curated', X, Y],del,U) <=> true | fact(['a1:P147_curated', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P53_has_former_or_current_location', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Birth', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:keywords', X, Y],add,_) \ fact(['a12:subject', X, Y],del,U) <=> true | fact(['a12:subject', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P5_consists_of', X, _],add,_) \ fact(['a1:E3_Condition_State', X],del,U) <=> true | fact(['a1:E3_Condition_State', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:icqChatID', X, Y],add,_) \ fact(['a3:nick', X, Y],del,U) <=> true | fact(['a3:nick', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P118i_is_overlapped_in_time_by', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P48_has_preferred_identifier', _, X1],add,_) \ fact(['a1:E42_Identifier', X1],del,U) <=> true | fact(['a1:E42_Identifier', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P44i_is_condition_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P69_is_associated_with', X, _],add,_) \ fact(['a1:E29_Design_or_Procedure', X],del,U) <=> true | fact(['a1:E29_Design_or_Procedure', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E11_Modification', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P93i_was_taken_out_of_existence_by', Y, X],add,_) \ fact(['a1:P93_took_out_of_existence', X, Y],del,U) <=> true | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P93_took_out_of_existence', Y, X],add,_) \ fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],del,U) <=> true | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P109i_is_current_or_former_curator_of', _, X1],add,_) \ fact(['a1:E78_Collection', X1],del,U) <=> true | fact(['a1:E78_Collection', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P76i_provides_access_to', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P94i_was_created_by', X, Y],add,_) \ fact(['a1:P92i_was_brought_into_existence_by', X, Y],del,U) <=> true | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E86_Leaving', X],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:Document', X],add,_), fact(['a3:Project', X],add,_) \ fact(['owl:Nothing', X],del,U) <=> true | fact(['owl:Nothing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P20i_was_purpose_of', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Event', X],add,_) \ fact(['a13:Event', X],del,U) <=> true | fact(['a13:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27_moved_from', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:birthday', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P143_joined', X, _],add,_) \ fact(['a1:E85_Joining', X],del,U) <=> true | fact(['a1:E85_Joining', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P115_finishes', Y, X],add,_) \ fact(['a1:P115i_is_finished_by', X, Y],del,U) <=> true | fact(['a1:P115i_is_finished_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P115i_is_finished_by', Y, X],add,_) \ fact(['a1:P115_finishes', X, Y],del,U) <=> true | fact(['a1:P115_finishes', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P25i_moved_by', X, _],add,_) \ fact(['a1:E19_Physical_Object', X],del,U) <=> true | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:witness', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E38_Image', X],add,_) \ fact(['a1:E36_Visual_Item', X],del,U) <=> true | fact(['a1:E36_Visual_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P73_has_translation', X, _],add,_) \ fact(['a1:E33_Linguistic_Object', X],del,U) <=> true | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P26i_was_destination_of', X, Y],add,_) \ fact(['a1:P7i_witnessed', X, Y],del,U) <=> true | fact(['a1:P7i_witnessed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:weblog', Y1, X],add,_), fact(['a3:weblog', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P17i_motivated', X, Y],add,_) \ fact(['a1:P15i_influenced', X, Y],del,U) <=> true | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P142_used_constituent', _, X1],add,_) \ fact(['a1:E41_Appellation', X1],del,U) <=> true | fact(['a1:E41_Appellation', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P125i_was_type_of_object_used_in', Y, X],add,_) \ fact(['a1:P125_used_object_of_type', X, Y],del,U) <=> true | fact(['a1:P125_used_object_of_type', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P125_used_object_of_type', Y, X],add,_) \ fact(['a1:P125i_was_type_of_object_used_in', X, Y],del,U) <=> true | fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:workplaceHomepage', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P134i_was_continued_by', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E89_Propositional_Object', X],add,_) \ fact(['a1:E28_Conceptual_Object', X],del,U) <=> true | fact(['a1:E28_Conceptual_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:skypeID', _, X1],add,_) \ fact(['rdfs:Literal', X1],del,U) <=> true | fact(['rdfs:Literal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:isPrimaryTopicOf', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P88_consists_of', Y, X],add,_) \ fact(['a1:P88i_forms_part_of', X, Y],del,U) <=> true | fact(['a1:P88i_forms_part_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P88i_forms_part_of', Y, X],add,_) \ fact(['a1:P88_consists_of', X, Y],del,U) <=> true | fact(['a1:P88_consists_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:relationship', Y, X],add,_) \ fact(['a2:participant', X, Y],del,U) <=> true | fact(['a2:participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:participant', Y, X],add,_) \ fact(['a2:relationship', X, Y],del,U) <=> true | fact(['a2:relationship', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P21i_was_purpose_of', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P17_was_motivated_by', _, X1],add,_) \ fact(['a1:E1_CRM_Entity', X1],del,U) <=> true | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P34_concerned', X, Y],add,_) \ fact(['a1:P140_assigned_attribute_to', X, Y],del,U) <=> true | fact(['a1:P140_assigned_attribute_to', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P25_moved', X, _],add,_) \ fact(['a1:E9_Move', X],del,U) <=> true | fact(['a1:E9_Move', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Accession', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:interest', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E58_Measurement_Unit', X],add,_) \ fact(['a1:E55_Type', X],del,U) <=> true | fact(['a1:E55_Type', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P105i_has_right_on', Y, X],add,_) \ fact(['a1:P105_right_held_by', X, Y],del,U) <=> true | fact(['a1:P105_right_held_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P105_right_held_by', Y, X],add,_) \ fact(['a1:P105i_has_right_on', X, Y],del,U) <=> true | fact(['a1:P105i_has_right_on', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:Assassination', X],add,_) \ fact(['a2:Murder', X],del,U) <=> true | fact(['a2:Murder', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P108_has_produced', X, _],add,_) \ fact(['a1:E12_Production', X],del,U) <=> true | fact(['a1:E12_Production', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E35_Title', X],add,_) \ fact(['a1:E33_Linguistic_Object', X],del,U) <=> true | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:witness', X, Y],add,_) \ fact(['a2:spectator', X, Y],del,U) <=> true | fact(['a2:spectator', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E83_Type_Creation', X],add,_) \ fact(['a1:E65_Creation', X],del,U) <=> true | fact(['a1:E65_Creation', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:mother', X, Y1],add,_), fact(['a2:mother', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P32i_was_technique_of', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P65_shows_visual_item', X, Y],add,_) \ fact(['a1:P128_carries', X, Y],del,U) <=> true | fact(['a1:P128_carries', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P69_is_associated_with', _, X1],add,_) \ fact(['a1:E29_Design_or_Procedure', X1],del,U) <=> true | fact(['a1:E29_Design_or_Procedure', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P135_created_type', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P22_transferred_title_to', X, Y],add,_) \ fact(['a1:P14_carried_out_by', X, Y],del,U) <=> true | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P49_has_former_or_current_keeper', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P104i_applies_to', X, _],add,_) \ fact(['a1:E30_Right', X],del,U) <=> true | fact(['a1:E30_Right', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P86i_contains', Y, X],add,_) \ fact(['a1:P86_falls_within', X, Y],del,U) <=> true | fact(['a1:P86_falls_within', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P86_falls_within', Y, X],add,_) \ fact(['a1:P86i_contains', X, Y],del,U) <=> true | fact(['a1:P86i_contains', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P11_had_participant', X, _],add,_) \ fact(['a1:E5_Event', X],del,U) <=> true | fact(['a1:E5_Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P2i_is_type_of', Y, X],add,_) \ fact(['a1:P2_has_type', X, Y],del,U) <=> true | fact(['a1:P2_has_type', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P2_has_type', Y, X],add,_) \ fact(['a1:P2i_is_type_of', X, Y],del,U) <=> true | fact(['a1:P2i_is_type_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:workplaceHomepage', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E52_Time-Span', X],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13i_was_destroyed_by', _, X1],add,_) \ fact(['a1:E6_Destruction', X1],del,U) <=> true | fact(['a1:E6_Destruction', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P129_is_about', X, _],add,_) \ fact(['a1:E89_Propositional_Object', X],del,U) <=> true | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P103i_was_intention_of', Y, X],add,_) \ fact(['a1:P103_was_intended_for', X, Y],del,U) <=> true | fact(['a1:P103_was_intended_for', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P103_was_intended_for', Y, X],add,_) \ fact(['a1:P103i_was_intention_of', X, Y],del,U) <=> true | fact(['a1:P103i_was_intention_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:birthday', X, Y1],add,_), fact(['a3:birthday', X, Y2],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:E34_Inscription', X],add,_) \ fact(['a1:E33_Linguistic_Object', X],del,U) <=> true | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P21_had_general_purpose', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E69_Death', X],add,_) \ fact(['a1:E64_End_of_Existence', X],del,U) <=> true | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E18_Physical_Thing', X],add,_) \ fact(['a1:E72_Legal_Object', X],del,U) <=> true | fact(['a1:E72_Legal_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P_E53_Place', X0, X1],add,_), fact(['a1:referToSame', X1, X2],add,_), fact(['a1:P_E53_Place', X2, X3],add,_) \ fact(['a1:relatedPlaces', X0, X3],del,U) <=> true | fact(['a1:relatedPlaces', X0, X3],add,U), applied_rules(1,red).
phase(2), fact(['a1:P143_joined', X, Y],add,_) \ fact(['a1:P11_had_participant', X, Y],del,U) <=> true | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P35_has_identified', X, Y],add,_) \ fact(['a1:P141_assigned', X, Y],del,U) <=> true | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:employer', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P145_separated', X, _],add,_) \ fact(['a1:E86_Leaving', X],del,U) <=> true | fact(['a1:E86_Leaving', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98i_was_born', X, X2],add,_), fact(['a1:P98i_was_born', X, X1],add,_), fact(['a1:E21_Person', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P114_is_equal_in_time_to', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P20i_was_purpose_of', X, _],add,_) \ fact(['a1:E5_Event', X],del,U) <=> true | fact(['a1:E5_Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P38i_was_deassigned_by', _, X1],add,_) \ fact(['a1:E15_Identifier_Assignment', X1],del,U) <=> true | fact(['a1:E15_Identifier_Assignment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P83_had_at_least_duration', _, X1],add,_) \ fact(['a1:E54_Dimension', X1],del,U) <=> true | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:page', _, X1],add,_) \ fact(['a3:Document', X1],del,U) <=> true | fact(['a3:Document', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:precedingEvent', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P134i_was_continued_by', X, Y],add,_) \ fact(['a1:P15i_influenced', X, Y],del,U) <=> true | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E67_Birth', X],add,_) \ fact(['a1:E63_Beginning_of_Existence', X],del,U) <=> true | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P133_is_separated_from', _, X1],add,_) \ fact(['a1:E4_Period', X1],del,U) <=> true | fact(['a1:E4_Period', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:pastProject', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:concludingEvent', X, Y],add,_) \ fact(['owl:differentFrom', X, Y],del,U) <=> true | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P19_was_intended_use_of', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E35_Title', X],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98_brought_into_life', X, _],add,_) \ fact(['a1:E67_Birth', X],del,U) <=> true | fact(['a1:E67_Birth', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P68_foresees_use_of', _, X1],add,_) \ fact(['a1:E57_Material', X1],del,U) <=> true | fact(['a1:E57_Material', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P33_used_specific_technique', X, Y],add,_) \ fact(['a1:P16_used_specific_object', X, Y],del,U) <=> true | fact(['a1:P16_used_specific_object', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:precedingEvent', _, X1],add,_) \ fact(['a2:Event', X1],del,U) <=> true | fact(['a2:Event', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P17i_motivated', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E68_Dissolution', X],add,_) \ fact(['a1:E64_End_of_Existence', X],del,U) <=> true | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,_) \ fact(['a1:P12i_was_present_at', X, Y],del,U) <=> true | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P52i_is_current_owner_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P120_occurs_before', X, Y],add,_), fact(['a1:P120_occurs_before', Y, Z],add,_) \ fact(['a1:P120_occurs_before', X, Z],del,U) <=> true | fact(['a1:P120_occurs_before', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P89i_contains', Y, X],add,_) \ fact(['a1:P89_falls_within', X, Y],del,U) <=> true | fact(['a1:P89_falls_within', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P89_falls_within', Y, X],add,_) \ fact(['a1:P89i_contains', X, Y],del,U) <=> true | fact(['a1:P89i_contains', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P121_overlaps_with', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P88_consists_of', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P129_is_about', Y, X],add,_) \ fact(['a1:P129i_is_subject_of', X, Y],del,U) <=> true | fact(['a1:P129i_is_subject_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P129i_is_subject_of', Y, X],add,_) \ fact(['a1:P129_is_about', X, Y],del,U) <=> true | fact(['a1:P129_is_about', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:state', X, Y],add,_) \ fact(['a2:agent', X, Y],del,U) <=> true | fact(['a2:agent', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P50i_is_current_keeper_of', X, Y],add,_) \ fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],del,U) <=> true | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:precedingEvent', X, Y],add,_), fact(['a2:precedingEvent', Y, Z],add,_) \ fact(['a2:precedingEvent', X, Z],del,U) <=> true | fact(['a2:precedingEvent', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a3:member', X, _],add,_) \ fact(['a3:Group', X],del,U) <=> true | fact(['a3:Group', X],add,U), applied_rules(1,red).
phase(2), fact(['rdfs:Class', X],add,_) \ fact(['rdfs:Resource', X],del,U) <=> true | fact(['rdfs:Resource', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P4i_is_time-span_of', Y, X],add,_) \ fact(['a1:P4_has_time-span', X, Y],del,U) <=> true | fact(['a1:P4_has_time-span', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P4_has_time-span', Y, X],add,_) \ fact(['a1:P4i_is_time-span_of', X, Y],del,U) <=> true | fact(['a1:P4i_is_time-span_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P105_right_held_by', X, _],add,_) \ fact(['a1:E72_Legal_Object', X],del,U) <=> true | fact(['a1:E72_Legal_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:aimChatID', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P122_borders_with', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:OnlineGamingAccount', X],add,_) \ fact(['a3:OnlineAccount', X],del,U) <=> true | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P26_moved_to', X, Y],add,_) \ fact(['a1:P7_took_place_at', X, Y],del,U) <=> true | fact(['a1:P7_took_place_at', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P31_has_modified', _, X1],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X1],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P83_had_at_least_duration', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:GroupEvent', X],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P86_falls_within', _, X1],add,_) \ fact(['a1:E52_Time-Span', X1],del,U) <=> true | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:yahooChatID', Y1, X],add,_), fact(['a3:yahooChatID', Y2, X],add,_) \ fact(['owl:sameAs', Y1, Y2],del,U) <=> true | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P106i_forms_part_of', Y, X],add,_) \ fact(['a1:P106_is_composed_of', X, Y],del,U) <=> true | fact(['a1:P106_is_composed_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P106_is_composed_of', Y, X],add,_) \ fact(['a1:P106i_forms_part_of', X, Y],del,U) <=> true | fact(['a1:P106i_forms_part_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P40i_was_observed_in', X, Y],add,_) \ fact(['a1:P141i_was_assigned_by', X, Y],del,U) <=> true | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P133_is_separated_from', Y, X],add,_) \ fact(['a1:P133_is_separated_from', X, Y],del,U) <=> true | fact(['a1:P133_is_separated_from', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P130_shows_features_of', X, _],add,_) \ fact(['a1:E70_Thing', X],del,U) <=> true | fact(['a1:E70_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Interval', X],add,_) \ fact(['a14:ProperInterval', X],del,U) <=> true | fact(['a14:ProperInterval', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P52i_is_current_owner_of', Y, X],add,_) \ fact(['a1:P52_has_current_owner', X, Y],del,U) <=> true | fact(['a1:P52_has_current_owner', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P52_has_current_owner', Y, X],add,_) \ fact(['a1:P52i_is_current_owner_of', X, Y],del,U) <=> true | fact(['a1:P52i_is_current_owner_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P100i_died_in', _, X1],add,_) \ fact(['a1:E69_Death', X1],del,U) <=> true | fact(['a1:E69_Death', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:maker', Y, X],add,_) \ fact(['a3:made', X, Y],del,U) <=> true | fact(['a3:made', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a3:made', Y, X],add,_) \ fact(['a3:maker', X, Y],del,U) <=> true | fact(['a3:maker', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P124_transformed', X, _],add,_) \ fact(['a1:E81_Transformation', X],del,U) <=> true | fact(['a1:E81_Transformation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E82_Actor_Appellation', X],add,_) \ fact(['a1:E41_Appellation', X],del,U) <=> true | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P32_used_general_technique', _, X1],add,_) \ fact(['a1:E55_Type', X1],del,U) <=> true | fact(['a1:E55_Type', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P123i_resulted_from', Y, X],add,_) \ fact(['a1:P123_resulted_in', X, Y],del,U) <=> true | fact(['a1:P123_resulted_in', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P123_resulted_in', Y, X],add,_) \ fact(['a1:P123i_resulted_from', X, Y],del,U) <=> true | fact(['a1:P123i_resulted_from', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P10i_contains', X, Y],add,_), fact(['a1:P10i_contains', Y, Z],add,_) \ fact(['a1:P10i_contains', X, Z],del,U) <=> true | fact(['a1:P10i_contains', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P51i_is_former_or_current_owner_of', Y, X],add,_) \ fact(['a1:P51_has_former_or_current_owner', X, Y],del,U) <=> true | fact(['a1:P51_has_former_or_current_owner', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P51_has_former_or_current_owner', Y, X],add,_) \ fact(['a1:P51i_is_former_or_current_owner_of', X, Y],del,U) <=> true | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P142i_was_used_in', _, X1],add,_) \ fact(['a1:E15_Identifier_Assignment', X1],del,U) <=> true | fact(['a1:E15_Identifier_Assignment', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Death', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P98_brought_into_life', X, Y],add,_) \ fact(['a1:P92_brought_into_existence', X, Y],del,U) <=> true | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P93i_was_taken_out_of_existence_by', X, _],add,_) \ fact(['a1:E77_Persistent_Item', X],del,U) <=> true | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39_measured', Y, X],add,_) \ fact(['a1:P39i_was_measured_by', X, Y],del,U) <=> true | fact(['a1:P39i_was_measured_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P39i_was_measured_by', Y, X],add,_) \ fact(['a1:P39_measured', X, Y],del,U) <=> true | fact(['a1:P39_measured', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P116i_is_started_by', _, X1],add,_) \ fact(['a1:E2_Temporal_Entity', X1],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E41_Appellation', X],add,_) \ fact(['a1:E90_Symbolic_Object', X],del,U) <=> true | fact(['a1:E90_Symbolic_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P106i_forms_part_of', X, Y],add,_), fact(['a1:P106i_forms_part_of', Y, Z],add,_) \ fact(['a1:P106i_forms_part_of', X, Z],del,U) <=> true | fact(['a1:P106i_forms_part_of', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:P50_has_current_keeper', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P9_consists_of', X, _],add,_) \ fact(['a1:E4_Period', X],del,U) <=> true | fact(['a1:E4_Period', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P144_joined_with', _, X1],add,_) \ fact(['a1:E74_Group', X1],del,U) <=> true | fact(['a1:E74_Group', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:publications', X, _],add,_) \ fact(['a3:Person', X],del,U) <=> true | fact(['a3:Person', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P46_is_composed_of', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P59_has_section', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:E36_Visual_Item', X],add,_) \ fact(['a1:E73_Information_Object', X],del,U) <=> true | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P112i_was_diminished_by', _, X1],add,_) \ fact(['a1:E80_Part_Removal', X1],del,U) <=> true | fact(['a1:E80_Part_Removal', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P11i_participated_in', X, _],add,_) \ fact(['a1:E39_Actor', X],del,U) <=> true | fact(['a1:E39_Actor', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P78_is_identified_by', X, _],add,_) \ fact(['a1:E52_Time-Span', X],del,U) <=> true | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P34_concerned', _, X1],add,_) \ fact(['a1:E18_Physical_Thing', X1],del,U) <=> true | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P112i_was_diminished_by', X, _],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P136i_supported_type_creation', X, _],add,_) \ fact(['a1:E1_CRM_Entity', X],del,U) <=> true | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P144i_gained_member_by', Y, X],add,_) \ fact(['a1:P144_joined_with', X, Y],del,U) <=> true | fact(['a1:P144_joined_with', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P144_joined_with', Y, X],add,_) \ fact(['a1:P144i_gained_member_by', X, Y],del,U) <=> true | fact(['a1:P144i_gained_member_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:Cremation', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P119_meets_in_time_with', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Marriage', X],add,_) \ fact(['a7:WeddingEvent_Generic', X],del,U) <=> true | fact(['a7:WeddingEvent_Generic', X],add,U), applied_rules(1,red).
phase(2), fact(['a7:WeddingEvent_Generic', X],add,_) \ fact(['a2:Marriage', X],del,U) <=> true | fact(['a2:Marriage', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16i_was_used_for', _, X1],add,_) \ fact(['a1:E7_Activity', X1],del,U) <=> true | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:Image', X],add,_) \ fact(['a3:Document', X],del,U) <=> true | fact(['a3:Document', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P143_joined', Y, X],add,_) \ fact(['a1:P143i_was_joined_by', X, Y],del,U) <=> true | fact(['a1:P143i_was_joined_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P143i_was_joined_by', Y, X],add,_) \ fact(['a1:P143_joined', X, Y],del,U) <=> true | fact(['a1:P143_joined', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P24i_changed_ownership_through', _, X1],add,_) \ fact(['a1:E8_Acquisition', X1],del,U) <=> true | fact(['a1:E8_Acquisition', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P115i_is_finished_by', X, _],add,_) \ fact(['a1:E2_Temporal_Entity', X],del,U) <=> true | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P103_was_intended_for', X, _],add,_) \ fact(['a1:E71_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P53i_is_former_or_current_location_of', X, _],add,_) \ fact(['a1:E53_Place', X],del,U) <=> true | fact(['a1:E53_Place', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P128_carries', X, _],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a5:LicenseDocument', X],add,_) \ fact(['a5:RightsStatement', X],del,U) <=> true | fact(['a5:RightsStatement', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P68_foresees_use_of', X, _],add,_) \ fact(['a1:E29_Design_or_Procedure', X],del,U) <=> true | fact(['a1:E29_Design_or_Procedure', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P89i_contains', _, X1],add,_) \ fact(['a1:E53_Place', X1],del,U) <=> true | fact(['a1:E53_Place', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P20_had_specific_purpose', X, _],add,_) \ fact(['a1:E7_Activity', X],del,U) <=> true | fact(['a1:E7_Activity', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P46_is_composed_of', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P7i_witnessed', _, X1],add,_) \ fact(['a1:E4_Period', X1],del,U) <=> true | fact(['a1:E4_Period', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:Naturalization', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P23i_surrendered_title_through', X, Y],add,_) \ fact(['a1:P14i_performed', X, Y],del,U) <=> true | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:E30_Right', X],add,_) \ fact(['a1:E89_Propositional_Object', X],del,U) <=> true | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P9_consists_of', _, X1],add,_) \ fact(['a1:E4_Period', X1],del,U) <=> true | fact(['a1:E4_Period', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P106_is_composed_of', _, X1],add,_) \ fact(['a1:E90_Symbolic_Object', X1],del,U) <=> true | fact(['a1:E90_Symbolic_Object', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:tipjar', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a3:account', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E70_Thing', X],add,_) \ fact(['a1:E77_Persistent_Item', X],del,U) <=> true | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P22i_acquired_title_through', X, Y],add,_) \ fact(['a1:P14i_performed', X, Y],del,U) <=> true | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P27_moved_from', X, _],add,_) \ fact(['a1:E9_Move', X],del,U) <=> true | fact(['a1:E9_Move', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P105_right_held_by', _, X1],add,_) \ fact(['a1:E39_Actor', X1],del,U) <=> true | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,red).
phase(2), fact(['a3:icqChatID', X, _],add,_) \ fact(['a3:Agent', X],del,U) <=> true | fact(['a3:Agent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:E78_Collection', X],add,_) \ fact(['a1:E24_Physical_Man-Made_Thing', X],del,U) <=> true | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P13i_was_destroyed_by', X, X2],add,_), fact(['a1:P13i_was_destroyed_by', X, X1],add,_), fact(['a1:E18_Physical_Thing', X],add,_) \ fact(['owl:sameAs', X1, X2],del,U) <=> true | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,red).
phase(2), fact(['a1:P136_was_based_on', X, Y],add,_) \ fact(['a1:P15_was_influenced_by', X, Y],del,U) <=> true | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16i_was_used_for', Y, X],add,_) \ fact(['a1:P16_used_specific_object', X, Y],del,U) <=> true | fact(['a1:P16_used_specific_object', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P16_used_specific_object', Y, X],add,_) \ fact(['a1:P16i_was_used_for', X, Y],del,U) <=> true | fact(['a1:P16i_was_used_for', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P88_consists_of', X, Y],add,_), fact(['a1:P88_consists_of', Y, Z],add,_) \ fact(['a1:P88_consists_of', X, Z],del,U) <=> true | fact(['a1:P88_consists_of', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a15:Performance', X],add,_) \ fact(['a2:Performance', X],del,U) <=> true | fact(['a2:Performance', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:Performance', X],add,_) \ fact(['a15:Performance', X],del,U) <=> true | fact(['a15:Performance', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P54_has_current_permanent_location', X, _],add,_) \ fact(['a1:E19_Physical_Object', X],del,U) <=> true | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P88i_forms_part_of', X, Y],add,_), fact(['a1:P88i_forms_part_of', Y, Z],add,_) \ fact(['a1:P88i_forms_part_of', X, Z],del,U) <=> true | fact(['a1:P88i_forms_part_of', X, Z],add,U), applied_rules(1,red).
phase(2), fact(['a1:E25_Man-Made_Feature', X],add,_) \ fact(['a1:E26_Physical_Feature', X],del,U) <=> true | fact(['a1:E26_Physical_Feature', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P94_has_created', X, _],add,_) \ fact(['a1:E65_Creation', X],del,U) <=> true | fact(['a1:E65_Creation', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P128_carries', Y, X],add,_) \ fact(['a1:P128i_is_carried_by', X, Y],del,U) <=> true | fact(['a1:P128i_is_carried_by', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P128i_is_carried_by', Y, X],add,_) \ fact(['a1:P128_carries', X, Y],del,U) <=> true | fact(['a1:P128_carries', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a2:Emigration', X],add,_) \ fact(['a2:IndividualEvent', X],del,U) <=> true | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P112_diminished', X, Y],add,_) \ fact(['a1:P31_has_modified', X, Y],del,U) <=> true | fact(['a1:P31_has_modified', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P33i_was_used_by', X, Y],add,_) \ fact(['a1:P16i_was_used_for', X, Y],del,U) <=> true | fact(['a1:P16i_was_used_for', X, Y],add,U), applied_rules(1,red).
phase(2), fact(['a1:P83i_was_minimum_duration_of', _, X1],add,_) \ fact(['a1:E52_Time-Span', X1],del,U) <=> true | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,red).
phase(2), fact(['a2:organization', X, _],add,_) \ fact(['a2:Event', X],del,U) <=> true | fact(['a2:Event', X],add,U), applied_rules(1,red).
phase(2), fact(['a1:P113i_was_removed_by', X, _],add,_) \ fact(['a1:E18_Physical_Thing', X],del,U) <=> true | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,red).
phase(2), fact(['a2:child', _, X1],add,_) \ fact(['a3:Person', X1],del,U) <=> true | fact(['a3:Person', X1],add,U), applied_rules(1,red).
phase(2), fact(['a1:P78_is_identified_by', _, X1],add,_) \ fact(['a1:E49_Time_Appellation', X1],del,U) <=> true | fact(['a1:E49_Time_Appellation', X1],add,U), applied_rules(1,red).

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
phase(5), fact(['a1:P22i_acquired_title_through', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P24_transferred_title_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P110i_was_augmented_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E79_Part_Addition', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', X, X2],add,U1), fact(['a1:P41_classified', X, X1],add,U2), fact(['a1:E17_Type_Assignment', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P33_used_specific_technique', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P116_starts', X, Y],add,U1), fact(['a1:P116_starts', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P116_starts', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P124i_was_transformed_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E81_Transformation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P104_is_subject_to', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P114_is_equal_in_time_to', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P127_has_broader_term', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P127i_has_narrower_term', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P127i_has_narrower_term', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P127_has_broader_term', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:followingEvent', X, Y],add,U1), fact(['a2:followingEvent', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a2:followingEvent', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E34_Inscription', X],add,U1) ==> member(U,[U1]) | fact(['a1:E37_Mark', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P94i_was_created_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E65_Creation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:aimChatID', _, X1],add,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E7_Activity', X],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:depiction', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Image', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P23_transferred_title_from', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Murder', X],add,U1) ==> member(U,[U1]) | fact(['a2:Death', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E14_Condition_Assessment', X],add,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P31_has_modified', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P123i_resulted_from', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E81_Transformation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:homepage', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P96_by_mother', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P96i_gave_birth', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P96i_gave_birth', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P96_by_mother', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P100_was_death_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E69_Death', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41i_was_classified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P71i_is_listed_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41i_was_classified_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P41_classified', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P41i_was_classified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P14_carried_out_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P93_took_out_of_existence', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P54_has_current_permanent_location', X, X2],add,U1), fact(['a1:P54_has_current_permanent_location', X, X1],add,U2), fact(['a1:E19_Physical_Object', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P146_separated_from', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P17_was_motivated_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P17i_motivated', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P17i_motivated', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P17_was_motivated_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39i_was_measured_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P113_removed', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73_has_translation', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P73i_is_translation_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P73_has_translation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P2i_is_type_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P141i_was_assigned_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P102_has_title', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P38_deassigned', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P54_has_current_permanent_location', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P54i_is_current_permanent_location_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P54i_is_current_permanent_location_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P54_has_current_permanent_location', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E21_Person', X],add,U1) ==> member(U,[U1]) | fact(['a1:E20_Biological_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['rdfs:Container', X],add,U1) ==> member(U,[U1]) | fact(['rdfs:Resource', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:publications', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedInformationObjects', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:relatedInformationObjects', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P126_employed', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:death', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Divorce', X],add,U1) ==> member(U,[U1]) | fact(['a2:GroupEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P136_was_based_on', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E83_Type_Creation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Graduation', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P29i_received_custody_through', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P29_custody_received_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P29_custody_received_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P29i_received_custody_through', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P10_falls_within', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P10i_contains', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P10i_contains', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P10_falls_within', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P142_used_constituent', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P16_used_specific_object', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P147i_was_curated_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E78_Collection', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E53_Place', X],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P72i_is_language_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P70_documents', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P124_transformed', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Person', X],add,U1) ==> member(U,[U1]) | fact(['a4:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E24_Physical_Man-Made_Thing', X],add,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P148i_is_component_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P148_has_component', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P148_has_component', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P148i_is_component_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P15_was_influenced_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P107_has_current_or_former_member', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:made', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P30_transferred_custody_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P30i_custody_transferred_through', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P30i_custody_transferred_through', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P30_transferred_custody_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P125_used_object_of_type', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:birth', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E65_Creation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E81_Transformation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P24i_changed_ownership_through', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P24_transferred_title_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P24_transferred_title_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P24i_changed_ownership_through', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Annulment', X],add,U1) ==> member(U,[U1]) | fact(['a2:GroupEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Promotion', X],add,U1) ==> member(U,[U1]) | fact(['a2:PositionChange', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P31_has_modified', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Ordination', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P130_shows_features_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P118_overlaps_in_time_with', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P144i_gained_member_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E85_Joining', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P124i_was_transformed_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P15_was_influenced_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E79_Part_Addition', X],add,U1), fact(['a1:E80_Part_Removal', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135_created_type', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P94_has_created', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P7_took_place_at', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a5:Jurisdiction', X],add,U1) ==> member(U,[U1]) | fact(['a5:LocationPeriodOrJurisdiction', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P56i_is_found_on', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E26_Physical_Feature', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P1_is_identified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P126i_was_employed_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P126_employed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P126_employed', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P126i_was_employed_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:principal', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:myersBriggs', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Demotion', X],add,U1) ==> member(U,[U1]) | fact(['a2:PositionChange', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:relationship', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P112_diminished', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P112i_was_diminished_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P112i_was_diminished_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P112_diminished', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:openid', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:isPrimaryTopicOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P141_assigned', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P141i_was_assigned_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P44_has_condition', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P45_consists_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P50i_is_current_keeper_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P26_moved_to', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P26i_was_destination_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P26i_was_destination_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P26_moved_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:img', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:depiction', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P24_transferred_title_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P133_is_separated_from', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P94_has_created', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P94i_was_created_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P94i_was_created_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P94_has_created', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67i_is_referred_to_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P9_consists_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P9i_forms_part_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P9i_forms_part_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P9_consists_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P51_has_former_or_current_owner', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P68i_use_foreseen_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:IndividualEvent', X],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P138i_has_representation', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P138_represents', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P138_represents', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P138i_has_representation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P51_has_former_or_current_owner', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Organization', X],add,U1), fact(['a3:Person', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:state', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, Y],add,U1) ==> member(U,[U1]) | fact(['a6:childOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55i_currently_holds', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P19_was_intended_use_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E47_Spatial_Coordinates', X],add,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:workInfoHomepage', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:depicts', Y, X],add,U1) ==> member(U,[U1]) | fact(['a3:depiction', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:depiction', Y, X],add,U1) ==> member(U,[U1]) | fact(['a3:depicts', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['rdfs:Literal', X],add,U1) ==> member(U,[U1]) | fact(['rdfs:Resource', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P52_has_current_owner', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P105_right_held_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:concurrentEvent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P58_has_section_definition', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E46_Section_Definition', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:surname', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P56i_is_found_on', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P144_joined_with', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E85_Joining', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P130i_features_are_also_found_on', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:event', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P43_has_dimension', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P56_bears_feature', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P56i_is_found_on', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P56i_is_found_on', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P56_bears_feature', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P83_had_at_least_duration', X, X2],add,U1), fact(['a1:P83_had_at_least_duration', X, X1],add,U2), fact(['a1:E52_Time-Span', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a2:participant', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Relationship', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P140_assigned_attribute_to', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P4_has_time-span', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13_destroyed', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P13i_was_destroyed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P13_destroyed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P107i_is_current_or_former_member_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E12_Production', X],add,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:employer', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E15_Identifier_Assignment', X],add,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P117_occurs_during', X, Y],add,U1), fact(['a1:P117_occurs_during', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P117_occurs_during', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E63_Beginning_of_Existence', X],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P117i_includes', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P117_occurs_during', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P117_occurs_during', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P117i_includes', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P10i_contains', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P120i_occurs_after', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P28_custody_surrendered_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P84i_was_maximum_duration_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P37i_was_assigned_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', X, X2],add,U1), fact(['a1:P39_measured', X, X1],add,U2), fact(['a1:E16_Measurement', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P147_curated', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E78_Collection', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E68_Dissolution', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P65i_is_shown_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P65_shows_visual_item', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P65_shows_visual_item', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P65i_is_shown_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P56_bears_feature', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E90_Symbolic_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P120_occurs_before', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E24_Physical_Man-Made_Thing', X],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E85_Joining', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P58_has_section_definition', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P146i_lost_member_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E86_Leaving', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P8i_witnessed', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P37_assigned', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P118_overlaps_in_time_with', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E4_Period', X],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Event', X],add,U1) ==> member(U,[U1]) | fact(['a7:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:officiator', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P62i_is_depicted_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P72_has_language', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E56_Language', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P138_represents', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P70i_is_documented_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E31_Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P32_used_general_technique', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:aimChatID', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P105i_has_right_on', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:age', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P100_was_death_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P100i_died_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P100i_died_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P100_was_death_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:skypeID', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:participant', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P11_had_participant', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:father', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P82_at_some_time_within', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P31i_was_modified_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:gender', X, Y1],add,U1), fact(['a3:gender', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedPlaces', X, Y],add,U1), fact(['a1:relatedPlaces', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:relatedPlaces', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P141_assigned', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Document', X],add,U1), fact(['a3:Organization', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P72_has_language', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P105i_has_right_on', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P97_from_father', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P110i_was_augmented_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P136_was_based_on', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P136i_supported_type_creation', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P136i_supported_type_creation', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P136_was_based_on', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P22i_acquired_title_through', Y1, X],add,U1), fact(['a1:P22i_acquired_title_through', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P100_was_death_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P45_consists_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P45i_is_incorporated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P45i_is_incorporated_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P45_consists_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:jabberID', _, X1],add,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P78i_identifies', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:primaryTopic', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P53_has_former_or_current_location', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P53i_is_former_or_current_location_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P53_has_former_or_current_location', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P37_assigned', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P37i_was_assigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P37i_was_assigned_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P37_assigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:lastName', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P84i_was_maximum_duration_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P32_used_general_technique', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P125_used_object_of_type', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P32_used_general_technique', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P32i_was_technique_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P32i_was_technique_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P32_used_general_technique', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P59i_is_located_on_or_within', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P59_has_section', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P59_has_section', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P59i_is_located_on_or_within', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox', Y1, X],add,U1), fact(['a3:mbox', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Marriage', X],add,U1) ==> member(U,[U1]) | fact(['a2:GroupEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E79_Part_Addition', X],add,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P35_has_identified', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P35i_was_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P35i_was_identified_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P35_has_identified', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:focus', X, _],add,U1) ==> member(U,[U1]) | fact(['a8:Concept', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:img', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Image', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Organization', X],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:topic_interest', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:eventInterval', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Interval', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P116i_is_started_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P31i_was_modified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:birth', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Birth', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P132_overlaps_with', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P132_overlaps_with', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E71_Man-Made_Thing', X],add,U1) ==> member(U,[U1]) | fact(['a1:P_E71_Man-Made_Thing', X, X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E66_Formation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P40_observed_dimension', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E16_Measurement', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyPrecedingEvent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P70_documents', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P131_is_identified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P102i_is_title_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P11i_participated_in', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P29_custody_received_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:event', Y, X],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:agent', Y, X],add,U1) ==> member(U,[U1]) | fact(['a2:event', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P109_has_current_or_former_curator', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E78_Collection', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P136_was_based_on', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P30_transferred_custody_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyFollowingEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P124i_was_transformed_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P132_overlaps_with', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P110_augmented', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P110i_was_augmented_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P110i_was_augmented_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P110_augmented', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P142i_was_used_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E21_Person', X],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P44_has_condition', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P78_is_identified_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P78i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P78i_identifies', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P78_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P112_diminished', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P8i_witnessed', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P5i_forms_part_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P5_consists_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P5_consists_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P5i_forms_part_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P116_starts', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39i_was_measured_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E16_Measurement', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:precedingEvent', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,U1), fact(['a1:referToSame', X1, X2],add,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedManMadeThings', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P5i_forms_part_of', X, X2],add,U1), fact(['a1:P5i_forms_part_of', X, X1],add,U2), fact(['a1:E3_Condition_State', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P10i_contains', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P125i_was_type_of_object_used_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P138_represents', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P10_falls_within', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P56_bears_feature', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E26_Physical_Feature', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E44_Place_Appellation', X],add,U1), fact(['a1:E49_Time_Appellation', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P71_lists', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyPrecedingEvent', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:child', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Event', X],add,U1) ==> member(U,[U1]) | fact(['a9:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P91i_is_unit_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E58_Measurement_Unit', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E50_Date', X],add,U1) ==> member(U,[U1]) | fact(['a1:E49_Time_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P23_transferred_title_from', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P110_augmented', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P55i_currently_holds', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55i_currently_holds', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P55_has_current_location', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E31_Document', X0, X1],add,U1), fact(['a1:referredBySame', X1, X2],add,U2), fact(['a1:P_E31_Document', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedDocuments', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedManMadeThings', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:relatedManMadeThings', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P74i_is_current_or_former_residence_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P103i_was_intention_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P84_had_at_most_duration', X, X2],add,U1), fact(['a1:P84_had_at_most_duration', X, X1],add,U2), fact(['a1:E52_Time-Span', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P88_consists_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E83_Type_Creation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P119i_is_met_in_time_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E16_Measurement', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P97i_was_father_for', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P42i_was_assigned_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E17_Type_Assignment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P106_is_composed_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P43_has_dimension', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P81_ongoing_throughout', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:family_name', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P140_assigned_attribute_to', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P70i_is_documented_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P7_took_place_at', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P45i_is_incorporated_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E10_Transfer_of_Custody', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73_has_translation', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', X, X2],add,U1), fact(['a1:P95i_was_formed_by', X, X1],add,U2), fact(['a1:E74_Group', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P134_continued', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P138i_has_representation', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P109_has_current_or_former_curator', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P109i_is_current_or_former_curator_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P109i_is_current_or_former_curator_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P109_has_current_or_former_curator', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P11_had_participant', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P71_lists', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P44_has_condition', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P44i_is_condition_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P44i_is_condition_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P44_has_condition', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:openid', Y1, X],add,U1), fact(['a3:openid', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P132_overlaps_with', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P111i_was_added_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E79_Part_Addition', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P40i_was_observed_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E16_Measurement', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P102_has_title', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E35_Title', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P99_dissolved', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P99i_was_dissolved_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P119_meets_in_time_with', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P144_joined_with', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:parent', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P140_assigned_attribute_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:initiatingEvent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P104i_applies_to', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P71i_is_listed_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E32_Authority_Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P35i_was_identified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E57_Material', X],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E53_Place', X0, X1],add,U1), fact(['a1:referredBySame', X1, X2],add,U2), fact(['a1:P_E53_Place', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedPlaces', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P34i_was_assessed_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P121_overlaps_with', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P121_overlaps_with', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13_destroyed', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E6_Destruction', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P84_had_at_most_duration', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P45_consists_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P100i_died_in', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P123_resulted_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E51_Contact_Point', X],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, X2],add,U1), fact(['a2:father', X, X1],add,U2), fact(['a3:Person', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, X4],add,U1), fact(['a2:mother', X, X3],add,U2), fact(['a3:Person', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X3, X4],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P9i_forms_part_of', X, X2],add,U1), fact(['a1:P9i_forms_part_of', X, X1],add,U2), fact(['a1:E4_Period', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P15i_influenced', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P15_was_influenced_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:parent', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P14i_performed', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P14_carried_out_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95_has_formed', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P95i_was_formed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P95_has_formed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P42i_was_assigned_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P94_has_created', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P131_is_identified_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E82_Actor_Appellation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:based_near', _, X1],add,U1) ==> member(U,[U1]) | fact(['a10:SpatialThing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P108i_was_produced_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P108_has_produced', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P112i_was_diminished_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P31i_was_modified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E46_Section_Definition', X],add,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P58i_defines_section', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P58_has_section_definition', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P58_has_section_definition', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P58i_defines_section', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:age', X, Y1],add,U1), fact(['a3:age', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P23i_surrendered_title_through', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P78_is_identified_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P7i_witnessed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:currentProject', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P119i_is_met_in_time_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:aimChatID', Y1, X],add,U1), fact(['a3:aimChatID', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P27_moved_from', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P27i_was_origin_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P37_assigned', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P116i_is_started_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P116_starts', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P116_starts', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P116i_is_started_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:sha1', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:agent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P12_occurred_in_the_presence_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P117i_includes', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P29i_received_custody_through', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P102_has_title', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P118i_is_overlapped_in_time_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P118_overlaps_in_time_with', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P118_overlaps_in_time_with', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P118i_is_overlapped_in_time_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P89_falls_within', X, Y],add,U1), fact(['a1:P89_falls_within', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P89_falls_within', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P138i_has_representation', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, Y1],add,U1), fact(['a2:father', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a3:status', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P137_exemplifies', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P2_has_type', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:event', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:followingEvent', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E49_Time_Appellation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:witness', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P48i_is_preferred_identifier_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P26i_was_destination_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:openid', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:organization', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P14i_performed', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P48i_is_preferred_identifier_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:plan', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P34i_was_assessed_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P140i_was_attributed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P131_is_identified_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P131i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P131i_identifies', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P131_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P148i_is_component_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P1_is_identified_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P129_is_about', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P115i_is_finished_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P42_assigned', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P42i_was_assigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P42i_was_assigned_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P42_assigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:employer', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P31_has_modified', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P87_is_identified_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P87i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P87i_identifies', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P87_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:spectator', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E28_Conceptual_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E68_Dissolution', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:birth', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:event', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', X, X2],add,U1), fact(['a1:P135i_was_created_by', X, X1],add,U2), fact(['a1:E55_Type', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E9_Move', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P128i_is_carried_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P71i_is_listed_in', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P5_consists_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P78i_identifies', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E49_Time_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P65i_is_shown_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P128i_is_carried_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E8_Acquisition', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:followingEvent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:icqChatID', _, X1],add,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a5:PhysicalMedium', X],add,U1) ==> member(U,[U1]) | fact(['a5:MediaType', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P70i_is_documented_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P70_documents', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P70_documents', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P70i_is_documented_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E75_Conceptual_Object_Appellation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P83i_was_minimum_duration_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Group', X],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P126_employed', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P40i_was_observed_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:agent', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P71_lists', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E32_Authority_Document', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P32i_was_technique_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E20_Biological_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P87i_identifies', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P130i_features_are_also_found_on', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P119i_is_met_in_time_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P119_meets_in_time_with', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P119_meets_in_time_with', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P119i_is_met_in_time_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:interest', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P146i_lost_member_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P30i_custody_transferred_through', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P104_is_subject_to', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E30_Right', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P110_augmented', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E79_Part_Addition', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:based_near', X, _],add,U1) ==> member(U,[U1]) | fact(['a10:SpatialThing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E72_Legal_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67i_is_referred_to_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P112_diminished', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E80_Part_Removal', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:NameChange', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E37_Mark', X],add,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E73_Information_Object', X0, X1],add,U1), fact(['a1:P67_refers_to', X1, X2],add,U2), fact(['a1:P_E73_Information_Object', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedInformationObjects', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a3:depicts', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Image', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:isPrimaryTopicOf', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P146i_lost_member_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P59i_is_located_on_or_within', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X1, X0],add,U1), fact(['a1:P67_refers_to', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['a1:referredBySame', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P28i_surrendered_custody_through', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P87i_identifies', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P68i_use_foreseen_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P17i_motivated', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P22_transferred_title_to', X, Y1],add,U1), fact(['a1:P22_transferred_title_to', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P86i_contains', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P25i_moved_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P40_observed_dimension', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P46_is_composed_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P46i_forms_part_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P46i_forms_part_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P46_is_composed_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P48_has_preferred_identifier', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P91_has_unit', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E58_Measurement_Unit', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P127_has_broader_term', X, Y],add,U1), fact(['a1:P127_has_broader_term', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P127_has_broader_term', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a2:event', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E3_Condition_State', X],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:accountServiceHomepage', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P70i_is_documented_in', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:holdsAccount', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X0, X1],add,U1), fact(['a1:P_E31_Document', X1, X2],add,U2) ==> member(U,[U1,U2]) | fact(['a1:refersToDocument', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P146_separated_from', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P45i_is_incorporated_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P88i_forms_part_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P24i_changed_ownership_through', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:jabberID', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:participant', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P4_has_time-span', X, X2],add,U1), fact(['a1:P4_has_time-span', X, X1],add,U2), fact(['a1:E2_Temporal_Entity', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', X, X2],add,U1), fact(['a1:P55_has_current_location', X, X1],add,U2), fact(['a1:E19_Physical_Object', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P120i_occurs_after', X, Y],add,U1), fact(['a1:P120i_occurs_after', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P120i_occurs_after', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E13_Attribute_Assignment', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:knows', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:weblog', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:PositionChange', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P134_continued', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P134i_was_continued_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P134i_was_continued_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P134_continued', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P29_custody_received_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P43i_is_dimension_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P137_exemplifies', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P65i_is_shown_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P91i_is_unit_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P91_has_unit', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P91_has_unit', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P91i_is_unit_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55_has_current_location', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P53_has_former_or_current_location', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P145i_left_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P145_separated', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P145_separated', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P145i_left_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95_has_formed', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E66_Formation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P38i_was_deassigned_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyPrecedingEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:isPrimaryTopicOf', Y, X],add,U1) ==> member(U,[U1]) | fact(['a3:primaryTopic', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:primaryTopic', Y, X],add,U1) ==> member(U,[U1]) | fact(['a3:isPrimaryTopicOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P38_deassigned', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P17_was_motivated_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P4i_is_time-span_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E31_Document', X0, X1],add,U1), fact(['a1:referToSame', X1, X2],add,U2), fact(['a1:P_E31_Document', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedDocuments', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Performance', X],add,U1) ==> member(U,[U1]) | fact(['a2:GroupEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:PersonalProfileDocument', X],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P17_was_motivated_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P19_was_intended_use_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P19i_was_made_for', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P19i_was_made_for', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P19_was_intended_use_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P29i_received_custody_through', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P30_transferred_custody_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:skypeID', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P101_had_as_general_use', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P101i_was_use_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P101i_was_use_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P101_had_as_general_use', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P131_is_identified_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P46i_forms_part_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P76_has_contact_point', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:death', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:followingEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P58i_defines_section', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedDocuments', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:relatedDocuments', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P75_possesses', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E30_Right', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E5_Event', X],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P131i_identifies', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E82_Actor_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P35_has_identified', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E14_Condition_Assessment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P143_joined', X, X2],add,U1), fact(['a1:P143_joined', X, X1],add,U2), fact(['a1:E85_Joining', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P83_had_at_least_duration', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P83i_was_minimum_duration_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P83i_was_minimum_duration_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P83_had_at_least_duration', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P113i_was_removed_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P113_removed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P113_removed', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P113i_was_removed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P7_took_place_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E73_Information_Object', X0, X1],add,U1), fact(['a1:referToSame', X1, X2],add,U2), fact(['a1:P_E73_Information_Object', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedInformationObjects', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E31_Document', X],add,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E40_Legal_Body', X],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P106_is_composed_of', X, Y],add,U1), fact(['a1:P106_is_composed_of', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P106_is_composed_of', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P62i_is_depicted_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P62_depicts', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P62_depicts', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P62i_is_depicted_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:birth', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E39_Actor', X],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E64_End_of_Existence', X],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P74_has_current_or_former_residence', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P110i_was_augmented_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P31i_was_modified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P52i_is_current_owner_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P105i_has_right_on', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P101_had_as_general_use', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13_destroyed', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P142_used_constituent', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E45_Address', X],add,U1) ==> member(U,[U1]) | fact(['a1:E51_Contact_Point', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P43i_is_dimension_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P43_has_dimension', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P43_has_dimension', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P43i_is_dimension_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P21_had_general_purpose', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:relationship', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a5:AgentClass', X],add,U1) ==> member(U,[U1]) | fact(['rdfs:Class', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P31i_was_modified_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P31_has_modified', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P31_has_modified', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P31i_was_modified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:partner', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P98_brought_into_life', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98_brought_into_life', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P98i_was_born', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyFollowingEvent', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P134_continued', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P35_has_identified', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P51i_is_former_or_current_owner_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, Y],add,U1) ==> member(U,[U1]) | fact(['a6:childOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P115_finishes', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:thumbnail', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Image', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P2_has_type', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P5i_forms_part_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P22i_acquired_title_through', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P22_transferred_title_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P22_transferred_title_to', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P22i_acquired_title_through', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P25_moved', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P127_has_broader_term', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P69_is_associated_with', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P69_is_associated_with', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P139_has_alternative_form', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P26_moved_to', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P123_resulted_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E81_Transformation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P92_brought_into_existence', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a5:FileFormat', X],add,U1) ==> member(U,[U1]) | fact(['a5:MediaType', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P50_has_current_keeper', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:firstName', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P2_has_type', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E25_Man-Made_Feature', X],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E73_Information_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P96i_gave_birth', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P28_custody_surrendered_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55i_currently_holds', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P53i_is_former_or_current_location_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P87_is_identified_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P37_assigned', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:workInfoHomepage', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E22_Man-Made_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P109i_is_current_or_former_curator_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P15i_influenced', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', X, X2],add,U1), fact(['a1:P73i_is_translation_of', X, X1],add,U2), fact(['a1:E33_Linguistic_Object', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95i_was_formed_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E66_Formation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P129_is_about', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E81_Transformation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E31_Document', X0, X1],add,U1), fact(['a1:refersToDocument', X1, X2],add,U2), fact(['a1:refersToDocument', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedDocuments', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P33i_was_used_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P33_used_specific_technique', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P33_used_specific_technique', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P33i_was_used_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P111_added', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P129i_is_subject_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P9i_forms_part_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P14_carried_out_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P126i_was_employed_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,U1), fact(['a1:referredBySame', X1, X2],add,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedManMadeThings', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P58i_defines_section', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E46_Section_Definition', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P14i_performed', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P139_has_alternative_form', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P75_possesses', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P75i_is_possessed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P75i_is_possessed_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P75_possesses', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:position', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P145i_left_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P10_falls_within', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E45_Address', X],add,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyFollowingEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:followingEvent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Employment', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a5:Location', X],add,U1) ==> member(U,[U1]) | fact(['a5:LocationPeriodOrJurisdiction', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P33i_was_used_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:topic', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P12_occurred_in_the_presence_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P12i_was_present_at', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P117_occurs_during', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P76i_provides_access_to', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E51_Contact_Point', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P70_documents', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E31_Document', X],add,U), applied_rules(1,ins).
phase(5), fact(['a5:MediaType', X],add,U1) ==> member(U,[U1]) | fact(['a5:MediaTypeOrExtent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:maker', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:primaryTopic', X, Y1],add,U1), fact(['a3:primaryTopic', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox_sha1sum', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P35i_was_identified_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E14_Condition_Assessment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P76_has_contact_point', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E51_Contact_Point', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E84_Information_Carrier', X],add,U1) ==> member(U,[U1]) | fact(['a1:E22_Man-Made_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P48_has_preferred_identifier', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P48i_is_preferred_identifier_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P48i_is_preferred_identifier_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P48_has_preferred_identifier', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:BasMitzvah', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P124i_was_transformed_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P124_transformed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P124_transformed', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P124i_was_transformed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P92_brought_into_existence', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13_destroyed', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P8_took_place_on_or_within', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P8i_witnessed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P8i_witnessed', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P8_took_place_on_or_within', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P76i_provides_access_to', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P76_has_contact_point', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P76_has_contact_point', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P76i_provides_access_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P106i_forms_part_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P56_bears_feature', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P46_is_composed_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P145i_left_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P53_has_former_or_current_location', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P25_moved', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyFollowingEvent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P96_by_mother', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:msnChatID', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P146i_lost_member_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P146_separated_from', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P146_separated_from', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P146i_lost_member_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P40_observed_dimension', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P33_used_specific_technique', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41i_was_classified_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P140i_was_attributed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:schoolHomepage', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P52_has_current_owner', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P7_took_place_at', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P7i_witnessed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P7i_witnessed', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P7_took_place_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95_has_formed', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Person', X],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P127i_has_narrower_term', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E6_Destruction', X],add,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P53i_is_former_or_current_location_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P134_continued', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:account', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P127_has_broader_term', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P93_took_out_of_existence', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P137_exemplifies', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P137i_is_exemplified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P137i_is_exemplified_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P137_exemplifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P22_transferred_title_to', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:accountName', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P30i_custody_transferred_through', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E10_Transfer_of_Custody', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P86_falls_within', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P20_had_specific_purpose', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P20i_was_purpose_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P20i_was_purpose_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P20_had_specific_purpose', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P89i_contains', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P5i_forms_part_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P49i_is_former_or_current_keeper_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P128i_is_carried_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Imprisonment', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:tipjar', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:organization', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:concurrentEvent', Y, X],add,U1) ==> member(U,[U1]) | fact(['a2:concurrentEvent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:yahooChatID', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P42_assigned', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P91_has_unit', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Retirement', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:tipjar', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P62_depicts', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:interval', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Interval', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:olb', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P117i_includes', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P88i_forms_part_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135_created_type', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E83_Type_Creation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P59i_is_located_on_or_within', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Dismissal', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P96i_gave_birth', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E27_Site', X],add,U1) ==> member(U,[U1]) | fact(['a1:E26_Physical_Feature', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:principal', X, X2],add,U1), fact(['a2:principal', X, X1],add,U2), fact(['a2:IndividualEvent', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a3:msnChatID', _, X1],add,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:homepage', Y1, X],add,U1), fact(['a3:homepage', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P1i_identifies', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P10_falls_within', X, Y],add,U1), fact(['a1:P10_falls_within', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P10_falls_within', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P96_by_mother', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Enrolment', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P75_possesses', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P93i_was_taken_out_of_existence_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P100_was_death_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P126i_was_employed_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P9i_forms_part_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Person', X],add,U1) ==> member(U,[U1]) | fact(['a10:SpatialThing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12_occurred_in_the_presence_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P92i_was_brought_into_existence_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P54i_is_current_permanent_location_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P51i_is_former_or_current_owner_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P115i_is_finished_by', X, Y],add,U1), fact(['a1:P115i_is_finished_by', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P115i_is_finished_by', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P137i_is_exemplified_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P2i_is_type_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:concludingEvent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:thumbnail', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Image', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:parent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P44i_is_condition_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P144i_gained_member_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P118i_is_overlapped_in_time_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P129i_is_subject_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P20_had_specific_purpose', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P32i_was_technique_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P65_shows_visual_item', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P129i_is_subject_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P134i_was_continued_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:msnChatID', Y1, X],add,U1), fact(['a3:msnChatID', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P87_is_identified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Person', X],add,U1), fact(['a3:Project', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E33_Linguistic_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:geekcode', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:officiator', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P114_is_equal_in_time_to', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P114_is_equal_in_time_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:partner', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:spectator', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P28i_surrendered_custody_through', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P136i_supported_type_creation', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P72i_is_language_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E56_Language', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P96_by_mother', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P116_starts', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:img', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P100i_died_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P96i_gave_birth', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:familyName', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P148_has_component', X, Y],add,U1), fact(['a1:P148_has_component', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P148_has_component', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P55i_currently_holds', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Event', X],add,U1) ==> member(U,[U1]) | fact(['a11:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P97i_was_father_for', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P97_from_father', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P97_from_father', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P97i_was_father_for', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P26_moved_to', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E52_Time-Span', X],add,U1), fact(['a1:E53_Place', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P89_falls_within', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E56_Language', X],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:spectator', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P40i_was_observed_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P40_observed_dimension', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P40_observed_dimension', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P40i_was_observed_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E71_Man-Made_Thing', X0, X1],add,U1), fact(['a1:P67_refers_to', X1, X2],add,U2), fact(['a1:P_E71_Man-Made_Thing', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedManMadeThings', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Adoption', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P42i_was_assigned_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P95_has_formed', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P31i_was_modified_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P56i_is_found_on', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P46i_forms_part_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P117_occurs_during', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99_dissolved', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:msnChatID', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P89i_contains', X, Y],add,U1), fact(['a1:P89i_contains', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P89i_contains', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E31_Document', X0, X1],add,U1), fact(['a1:P67_refers_to', X1, X2],add,U2), fact(['a1:P_E31_Document', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedDocuments', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P137i_is_exemplified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P130_shows_features_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P130i_features_are_also_found_on', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P130i_features_are_also_found_on', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P130_shows_features_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P52i_is_current_owner_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P46i_forms_part_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P19i_was_made_for', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E17_Type_Assignment', X],add,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E32_Authority_Document', X],add,U1) ==> member(U,[U1]) | fact(['a1:E31_Document', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P135_created_type', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135_created_type', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P135i_was_created_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P120_occurs_before', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P120i_occurs_after', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P120i_occurs_after', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P120_occurs_before', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P107i_is_current_or_former_member_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:gender', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P19i_was_made_for', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P86_falls_within', X, Y],add,U1), fact(['a1:P86_falls_within', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P86_falls_within', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P120_occurs_before', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E19_Physical_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P7i_witnessed', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P75i_is_possessed_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['rdfs:ContainerMembershipProperty', X],add,U1) ==> member(U,[U1]) | fact(['rdf:Property', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P92i_was_brought_into_existence_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P113i_was_removed_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E80_Part_Removal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P103_was_intended_for', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:child', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:homepage', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:partner', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39i_was_measured_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P140i_was_attributed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E48_Place_Name', X],add,U1) ==> member(U,[U1]) | fact(['a1:P_E53_Place', X, X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:schoolHomepage', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P34_concerned', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E14_Condition_Assessment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Redundancy', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P28_custody_surrendered_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P28i_surrendered_custody_through', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P28i_surrendered_custody_through', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P28_custody_surrendered_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', X, Y],add,U1), fact(['a1:P27_moved_from', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P27_moved_from', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E80_Part_Removal', X],add,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P102i_is_title_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E35_Title', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P116i_is_started_by', X, Y],add,U1), fact(['a1:P116i_is_started_by', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P116i_is_started_by', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E44_Place_Appellation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P54_has_current_permanent_location', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P38i_was_deassigned_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P38_deassigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P38_deassigned', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P38i_was_deassigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P97i_was_father_for', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P4_has_time-span', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Formation', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:agent', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P137_exemplifies', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P137i_is_exemplified_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P80_end_is_qualified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:knows', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Disbanding', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P148i_is_component_of', X, Y],add,U1), fact(['a1:P148i_is_component_of', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P148i_is_component_of', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a3:yahooChatID', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:death', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:event', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P89_falls_within', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P115_finishes', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:death', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Death', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P35i_was_identified_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P111_added', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E79_Part_Addition', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P37i_was_assigned_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P42_assigned', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E17_Type_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E73_Information_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P110_augmented', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P31_has_modified', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P78i_identifies', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P91i_is_unit_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P146_separated_from', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E86_Leaving', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:position', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P86i_contains', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox_sha1sum', Y1, X],add,U1), fact(['a3:mbox_sha1sum', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E74_Group', X],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P37i_was_assigned_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:yahooChatID', _, X1],add,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P127i_has_narrower_term', X, Y],add,U1), fact(['a1:P127i_has_narrower_term', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P127i_has_narrower_term', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a3:member', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P21i_was_purpose_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E29_Design_or_Procedure', X],add,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Execution', X],add,U1) ==> member(U,[U1]) | fact(['a2:Death', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P71_lists', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P71i_is_listed_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P71i_is_listed_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P71_lists', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P84_had_at_most_duration', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P101i_was_use_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P142_used_constituent', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P142i_was_used_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P142i_was_used_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P142_used_constituent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:position', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P147i_was_curated_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E87_Curation_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P49_has_former_or_current_keeper', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P49i_is_former_or_current_keeper_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P49_has_former_or_current_keeper', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P38i_was_deassigned_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P145i_left_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E86_Leaving', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P91_has_unit', X, X2],add,U1), fact(['a1:P91_has_unit', X, X1],add,U2), fact(['a1:E54_Dimension', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a2:relationship', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Relationship', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73i_is_translation_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P75i_is_possessed_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E30_Right', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:principal', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:OnlineEcommerceAccount', X],add,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P2i_is_type_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E31_Document', X],add,U1) ==> member(U,[U1]) | fact(['a1:P_E31_Document', X, X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:principal', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P144i_gained_member_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P74i_is_current_or_former_residence_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:holdsAccount', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P90_has_value', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:weblog', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41i_was_classified_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E17_Type_Assignment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P123_resulted_in', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P93_took_out_of_existence', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:concurrentEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P49i_is_former_or_current_keeper_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['rdfs:Datatype', X],add,U1) ==> member(U,[U1]) | fact(['rdfs:Class', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P111i_was_added_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:father', X, _],add,U1), fact(['a2:mother', X, _],add,U2) ==> member(U,[U1,U2]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P125i_was_type_of_object_used_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P145_separated', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P57_has_number_of_parts', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Investiture', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P147_curated', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E87_Curation_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P138i_has_representation', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67i_is_referred_to_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P67_refers_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P67i_is_referred_to_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P50_has_current_keeper', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P50i_is_current_keeper_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P50i_is_current_keeper_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P50_has_current_keeper', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P138_represents', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73_has_translation', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P130_shows_features_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:concurrentEvent', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a5:PeriodOfTime', X],add,U1) ==> member(U,[U1]) | fact(['a5:LocationPeriodOrJurisdiction', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P143i_was_joined_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P121_overlaps_with', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P34i_was_assessed_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P34_concerned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P34_concerned', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P34i_was_assessed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108i_was_produced_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E12_Production', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P140i_was_attributed_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P117i_includes', X, Y],add,U1), fact(['a1:P117i_includes', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P117i_includes', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P102i_is_title_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X0, X1],add,U1), fact(['a1:P67_refers_to', X2, X1],add,U2) ==> member(U,[U1,U2]) | fact(['a1:referToSame', X0, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E71_Man-Made_Thing', X],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P141_assigned', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P74_has_current_or_former_residence', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P84i_was_maximum_duration_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P84_had_at_most_duration', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P84_had_at_most_duration', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P84i_was_maximum_duration_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:weblog', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E77_Persistent_Item', X],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P104i_applies_to', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P104_is_subject_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P104_is_subject_to', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P104i_applies_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E87_Curation_Activity', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:isPrimaryTopicOf', Y1, X],add,U1), fact(['a3:isPrimaryTopicOf', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Relationship', X],add,U1) ==> member(U,[U1]) | fact(['a6:Relationship', X],add,U), applied_rules(1,ins).
phase(5), fact(['a6:Relationship', X],add,U1) ==> member(U,[U1]) | fact(['a2:Relationship', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:logo', Y1, X],add,U1), fact(['a3:logo', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P92_brought_into_existence', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E48_Place_Name', X],add,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P143i_was_joined_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E2_Temporal_Entity', X],add,U1), fact(['a1:E77_Persistent_Item', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P54i_is_current_permanent_location_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P145_separated', X, X2],add,U1), fact(['a1:P145_separated', X, X1],add,U2), fact(['a1:E86_Leaving', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P99i_was_dissolved_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Inauguration', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P125_used_object_of_type', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P25i_moved_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P72i_is_language_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P72_has_language', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P72_has_language', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P72i_is_language_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P101i_was_use_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P123i_resulted_from', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E66_Formation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P1i_identifies', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a5:SizeOrDuration', X],add,U1) ==> member(U,[U1]) | fact(['a5:MediaTypeOrExtent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P92_brought_into_existence', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P92i_was_brought_into_existence_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:icqChatID', Y1, X],add,U1), fact(['a3:icqChatID', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a3:OnlineChatAccount', X],add,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P97_from_father', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P65i_is_shown_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P86i_contains', X, Y],add,U1), fact(['a1:P86i_contains', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P86i_contains', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Coronation', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P148i_is_component_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P34i_was_assessed_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E14_Condition_Assessment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P49_has_former_or_current_keeper', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P43i_is_dimension_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P143i_was_joined_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E85_Joining', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P21_had_general_purpose', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P21i_was_purpose_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P21i_was_purpose_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P21_had_general_purpose', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P87i_identifies', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Funeral', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P11i_participated_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P11_had_participant', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P11i_participated_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P111_added', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P111i_was_added_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P111i_was_added_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P111_added', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E73_Information_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:P_E73_Information_Object', X, X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P113_removed', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E80_Part_Removal', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P142i_was_used_in', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P16i_was_used_for', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:page', Y, X],add,U1) ==> member(U,[U1]) | fact(['a3:topic', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:topic', Y, X],add,U1) ==> member(U,[U1]) | fact(['a3:page', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135i_was_created_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P94i_was_created_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P101_had_as_general_use', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:homepage', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:isPrimaryTopicOf', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P127i_has_narrower_term', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P25i_moved_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P25_moved', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P25_moved', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P25i_moved_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P3_has_note', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P38_deassigned', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E42_Identifier', X],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P148_has_component', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P122_borders_with', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P122_borders_with', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P59i_is_located_on_or_within', X, X2],add,U1), fact(['a1:P59i_is_located_on_or_within', X, X1],add,U2), fact(['a1:E53_Place', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P26i_was_destination_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:accountServiceHomepage', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P68_foresees_use_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P68i_use_foreseen_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P68i_use_foreseen_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P68_foresees_use_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:eventInterval', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P128_carries', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E65_Creation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:mbox_sha1sum', _, X1],add,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:interval', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Relationship', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P67_refers_to', X, Y],add,U1), fact(['a1:P67_refers_to', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P67_refers_to', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E12_Production', X],add,U1) ==> member(U,[U1]) | fact(['a1:E11_Modification', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P12i_was_present_at', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P48_has_preferred_identifier', X, X2],add,U1), fact(['a1:P48_has_preferred_identifier', X, X1],add,U2), fact(['a1:E1_CRM_Entity', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P148_has_component', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P12_occurred_in_the_presence_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P31i_was_modified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P94i_was_created_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P107_has_current_or_former_member', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P103i_was_intention_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P12i_was_present_at', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P42_assigned', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P41_classified', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E17_Type_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P62i_is_depicted_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P4i_is_time-span_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P106i_forms_part_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E26_Physical_Feature', X],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:immediatelyPrecedingEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:precedingEvent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Resignation', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:BarMitzvah', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E2_Temporal_Entity', X],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P123i_resulted_from', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E54_Dimension', X],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P131i_identifies', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Baptism', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P122_borders_with', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P94_has_created', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P115_finishes', X, Y],add,U1), fact(['a1:P115_finishes', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P115_finishes', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a3:openid', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P1i_identifies', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P1_is_identified_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P1_is_identified_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P52_has_current_owner', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P102i_is_title_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P102_has_title', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P102_has_title', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P102i_is_title_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P59_has_section', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P79_beginning_is_qualified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:jabberID', Y1, X],add,U1), fact(['a3:jabberID', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P140_assigned_attribute_to', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P140i_was_attributed_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P140i_was_attributed_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P140_assigned_attribute_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98_brought_into_life', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E21_Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P8_took_place_on_or_within', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P8_took_place_on_or_within', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E22_Man-Made_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P114_is_equal_in_time_to', X, Y],add,U1), fact(['a1:P114_is_equal_in_time_to', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P114_is_equal_in_time_to', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E73_Information_Object', X0, X1],add,U1), fact(['a1:referredBySame', X1, X2],add,U2), fact(['a1:P_E73_Information_Object', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedInformationObjects', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Burial', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P140i_was_attributed_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E53_Place', X],add,U1) ==> member(U,[U1]) | fact(['a1:P_E53_Place', X, X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P23_transferred_title_from', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P23i_surrendered_title_through', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P23i_surrendered_title_through', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P23_transferred_title_from', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27i_was_origin_of', X, Y],add,U1), fact(['a1:P27i_was_origin_of', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P27i_was_origin_of', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P33i_was_used_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P74i_is_current_or_former_residence_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P74_has_current_or_former_residence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P74_has_current_or_former_residence', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P74i_is_current_or_former_residence_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E90_Symbolic_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P107_has_current_or_former_member', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P107i_is_current_or_former_member_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P107i_is_current_or_former_member_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P107_has_current_or_former_member', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P131i_identifies', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P1i_identifies', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:keywords', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P87_is_identified_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E44_Place_Appellation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P15i_influenced', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P109_has_current_or_former_curator', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P141i_was_assigned_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E16_Measurement', X],add,U1) ==> member(U,[U1]) | fact(['a1:E13_Attribute_Assignment', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P124_transformed', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P120i_occurs_after', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E53_Place', X0, X1],add,U1), fact(['a1:P67_refers_to', X1, X2],add,U2), fact(['a1:P_E53_Place', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedPlaces', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a5:Agent', X],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Agent', X],add,U1) ==> member(U,[U1]) | fact(['a5:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P62_depicts', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P65_shows_visual_item', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:initiatingEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P11i_participated_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P140_assigned_attribute_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P136i_supported_type_creation', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E83_Type_Creation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E55_Type', X],add,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:officiator', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:relatedPlaces', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:relatedPlaces', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P147_curated', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P147i_was_curated_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P147i_was_curated_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P147_curated', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P53_has_former_or_current_location', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Birth', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:keywords', X, Y],add,U1) ==> member(U,[U1]) | fact(['a12:subject', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P5_consists_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E3_Condition_State', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:icqChatID', X, Y],add,U1) ==> member(U,[U1]) | fact(['a3:nick', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P118i_is_overlapped_in_time_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P48_has_preferred_identifier', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E42_Identifier', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P44i_is_condition_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P69_is_associated_with', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E11_Modification', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P93i_was_taken_out_of_existence_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P93_took_out_of_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P93_took_out_of_existence', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P109i_is_current_or_former_curator_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E78_Collection', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P76i_provides_access_to', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P94i_was_created_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92i_was_brought_into_existence_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E86_Leaving', X],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Document', X],add,U1), fact(['a3:Project', X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:Nothing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P20i_was_purpose_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Event', X],add,U1) ==> member(U,[U1]) | fact(['a13:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:birthday', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P143_joined', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E85_Joining', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P115_finishes', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P115i_is_finished_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P115i_is_finished_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P115_finishes', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P25i_moved_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:witness', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E38_Image', X],add,U1) ==> member(U,[U1]) | fact(['a1:E36_Visual_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P73_has_translation', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P26i_was_destination_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P7i_witnessed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:weblog', Y1, X],add,U1), fact(['a3:weblog', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P17i_motivated', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P142_used_constituent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P125i_was_type_of_object_used_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P125_used_object_of_type', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P125_used_object_of_type', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P125i_was_type_of_object_used_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:workplaceHomepage', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P134i_was_continued_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E89_Propositional_Object', X],add,U1) ==> member(U,[U1]) | fact(['a1:E28_Conceptual_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:skypeID', _, X1],add,U1) ==> member(U,[U1]) | fact(['rdfs:Literal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:isPrimaryTopicOf', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P88_consists_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P88i_forms_part_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P88i_forms_part_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P88_consists_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:relationship', Y, X],add,U1) ==> member(U,[U1]) | fact(['a2:participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:participant', Y, X],add,U1) ==> member(U,[U1]) | fact(['a2:relationship', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P21i_was_purpose_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P17_was_motivated_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P34_concerned', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P140_assigned_attribute_to', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P25_moved', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Accession', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:interest', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E58_Measurement_Unit', X],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P105i_has_right_on', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P105_right_held_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P105_right_held_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P105i_has_right_on', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Assassination', X],add,U1) ==> member(U,[U1]) | fact(['a2:Murder', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P108_has_produced', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E12_Production', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E35_Title', X],add,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:witness', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:spectator', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E83_Type_Creation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E65_Creation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:mother', X, Y1],add,U1), fact(['a2:mother', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P32i_was_technique_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P65_shows_visual_item', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P128_carries', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P69_is_associated_with', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P135_created_type', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P22_transferred_title_to', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P14_carried_out_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P49_has_former_or_current_keeper', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P104i_applies_to', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E30_Right', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P86i_contains', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P86_falls_within', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P86_falls_within', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P86i_contains', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P11_had_participant', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P2i_is_type_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P2_has_type', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P2_has_type', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P2i_is_type_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:workplaceHomepage', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E52_Time-Span', X],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E6_Destruction', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P129_is_about', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P103i_was_intention_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P103_was_intended_for', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P103_was_intended_for', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P103i_was_intention_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:birthday', X, Y1],add,U1), fact(['a3:birthday', X, Y2],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E34_Inscription', X],add,U1) ==> member(U,[U1]) | fact(['a1:E33_Linguistic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P21_had_general_purpose', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E69_Death', X],add,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E18_Physical_Thing', X],add,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P_E53_Place', X0, X1],add,U1), fact(['a1:referToSame', X1, X2],add,U2), fact(['a1:P_E53_Place', X2, X3],add,U3) ==> member(U,[U1,U2,U3]) | fact(['a1:relatedPlaces', X0, X3],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P143_joined', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P11_had_participant', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P35_has_identified', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141_assigned', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:employer', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P145_separated', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E86_Leaving', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98i_was_born', X, X2],add,U1), fact(['a1:P98i_was_born', X, X1],add,U2), fact(['a1:E21_Person', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P114_is_equal_in_time_to', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P20i_was_purpose_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E5_Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P38i_was_deassigned_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P83_had_at_least_duration', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E54_Dimension', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:page', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:precedingEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P134i_was_continued_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P15i_influenced', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E67_Birth', X],add,U1) ==> member(U,[U1]) | fact(['a1:E63_Beginning_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P133_is_separated_from', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:pastProject', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:concludingEvent', X, Y],add,U1) ==> member(U,[U1]) | fact(['owl:differentFrom', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P19_was_intended_use_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E35_Title', X],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98_brought_into_life', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E67_Birth', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P68_foresees_use_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E57_Material', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P33_used_specific_technique', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P16_used_specific_object', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:precedingEvent', _, X1],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P17i_motivated', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E68_Dissolution', X],add,U1) ==> member(U,[U1]) | fact(['a1:E64_End_of_Existence', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P93i_was_taken_out_of_existence_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P12i_was_present_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P52i_is_current_owner_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P120_occurs_before', X, Y],add,U1), fact(['a1:P120_occurs_before', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P120_occurs_before', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P89i_contains', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P89_falls_within', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P89_falls_within', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P89i_contains', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P121_overlaps_with', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P88_consists_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P129_is_about', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P129i_is_subject_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P129i_is_subject_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P129_is_about', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:state', X, Y],add,U1) ==> member(U,[U1]) | fact(['a2:agent', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P50i_is_current_keeper_of', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P49i_is_former_or_current_keeper_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:precedingEvent', X, Y],add,U1), fact(['a2:precedingEvent', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a2:precedingEvent', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a3:member', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Group', X],add,U), applied_rules(1,ins).
phase(5), fact(['rdfs:Class', X],add,U1) ==> member(U,[U1]) | fact(['rdfs:Resource', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P4i_is_time-span_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P4_has_time-span', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P4_has_time-span', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P4i_is_time-span_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P105_right_held_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E72_Legal_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:aimChatID', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P122_borders_with', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:OnlineGamingAccount', X],add,U1) ==> member(U,[U1]) | fact(['a3:OnlineAccount', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P26_moved_to', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P7_took_place_at', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P31_has_modified', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P83_had_at_least_duration', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:GroupEvent', X],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P86_falls_within', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:yahooChatID', Y1, X],add,U1), fact(['a3:yahooChatID', Y2, X],add,U2) ==> member(U,[U1,U2]) | fact(['owl:sameAs', Y1, Y2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P106i_forms_part_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P106_is_composed_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P106_is_composed_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P106i_forms_part_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P40i_was_observed_in', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P141i_was_assigned_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P133_is_separated_from', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P133_is_separated_from', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P130_shows_features_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E70_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Interval', X],add,U1) ==> member(U,[U1]) | fact(['a14:ProperInterval', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P52i_is_current_owner_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P52_has_current_owner', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P52_has_current_owner', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P52i_is_current_owner_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P100i_died_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E69_Death', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:maker', Y, X],add,U1) ==> member(U,[U1]) | fact(['a3:made', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a3:made', Y, X],add,U1) ==> member(U,[U1]) | fact(['a3:maker', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P124_transformed', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E81_Transformation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E82_Actor_Appellation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E41_Appellation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P32_used_general_technique', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E55_Type', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P123i_resulted_from', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P123_resulted_in', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P123_resulted_in', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P123i_resulted_from', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P10i_contains', X, Y],add,U1), fact(['a1:P10i_contains', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P10i_contains', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P51i_is_former_or_current_owner_of', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P51_has_former_or_current_owner', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P51_has_former_or_current_owner', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P51i_is_former_or_current_owner_of', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P142i_was_used_in', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E15_Identifier_Assignment', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Death', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P98_brought_into_life', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P92_brought_into_existence', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P93i_was_taken_out_of_existence_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39_measured', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P39i_was_measured_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P39i_was_measured_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P39_measured', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P116i_is_started_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E41_Appellation', X],add,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P106i_forms_part_of', X, Y],add,U1), fact(['a1:P106i_forms_part_of', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P106i_forms_part_of', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P50_has_current_keeper', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P9_consists_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P144_joined_with', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E74_Group', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:publications', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P46_is_composed_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P59_has_section', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E36_Visual_Item', X],add,U1) ==> member(U,[U1]) | fact(['a1:E73_Information_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P112i_was_diminished_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E80_Part_Removal', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P11i_participated_in', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P78_is_identified_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P34_concerned', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P112i_was_diminished_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P136i_supported_type_creation', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E1_CRM_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P144i_gained_member_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P144_joined_with', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P144_joined_with', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P144i_gained_member_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Cremation', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P119_meets_in_time_with', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Marriage', X],add,U1) ==> member(U,[U1]) | fact(['a7:WeddingEvent_Generic', X],add,U), applied_rules(1,ins).
phase(5), fact(['a7:WeddingEvent_Generic', X],add,U1) ==> member(U,[U1]) | fact(['a2:Marriage', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:Image', X],add,U1) ==> member(U,[U1]) | fact(['a3:Document', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P143_joined', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P143i_was_joined_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P143i_was_joined_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P143_joined', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P24i_changed_ownership_through', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E8_Acquisition', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P115i_is_finished_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E2_Temporal_Entity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P103_was_intended_for', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E71_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P53i_is_former_or_current_location_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P128_carries', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a5:LicenseDocument', X],add,U1) ==> member(U,[U1]) | fact(['a5:RightsStatement', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P68_foresees_use_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E29_Design_or_Procedure', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P89i_contains', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E53_Place', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P20_had_specific_purpose', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E7_Activity', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P46_is_composed_of', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P7i_witnessed', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Naturalization', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P23i_surrendered_title_through', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E30_Right', X],add,U1) ==> member(U,[U1]) | fact(['a1:E89_Propositional_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P9_consists_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E4_Period', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P106_is_composed_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E90_Symbolic_Object', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:tipjar', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a3:account', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E70_Thing', X],add,U1) ==> member(U,[U1]) | fact(['a1:E77_Persistent_Item', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P22i_acquired_title_through', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P14i_performed', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P27_moved_from', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E9_Move', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P105_right_held_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E39_Actor', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a3:icqChatID', X, _],add,U1) ==> member(U,[U1]) | fact(['a3:Agent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E78_Collection', X],add,U1) ==> member(U,[U1]) | fact(['a1:E24_Physical_Man-Made_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P13i_was_destroyed_by', X, X2],add,U1), fact(['a1:P13i_was_destroyed_by', X, X1],add,U2), fact(['a1:E18_Physical_Thing', X],add,U3) ==> member(U,[U1,U2,U3]) | fact(['owl:sameAs', X1, X2],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P136_was_based_on', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P15_was_influenced_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16i_was_used_for', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P16_used_specific_object', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P16_used_specific_object', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P16i_was_used_for', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P88_consists_of', X, Y],add,U1), fact(['a1:P88_consists_of', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P88_consists_of', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a15:Performance', X],add,U1) ==> member(U,[U1]) | fact(['a2:Performance', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Performance', X],add,U1) ==> member(U,[U1]) | fact(['a15:Performance', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P54_has_current_permanent_location', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E19_Physical_Object', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P88i_forms_part_of', X, Y],add,U1), fact(['a1:P88i_forms_part_of', Y, Z],add,U2) ==> member(U,[U1,U2]) | fact(['a1:P88i_forms_part_of', X, Z],add,U), applied_rules(1,ins).
phase(5), fact(['a1:E25_Man-Made_Feature', X],add,U1) ==> member(U,[U1]) | fact(['a1:E26_Physical_Feature', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P94_has_created', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E65_Creation', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P128_carries', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P128i_is_carried_by', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P128i_is_carried_by', Y, X],add,U1) ==> member(U,[U1]) | fact(['a1:P128_carries', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a2:Emigration', X],add,U1) ==> member(U,[U1]) | fact(['a2:IndividualEvent', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P112_diminished', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P31_has_modified', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P33i_was_used_by', X, Y],add,U1) ==> member(U,[U1]) | fact(['a1:P16i_was_used_for', X, Y],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P83i_was_minimum_duration_of', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E52_Time-Span', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a2:organization', X, _],add,U1) ==> member(U,[U1]) | fact(['a2:Event', X],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P113i_was_removed_by', X, _],add,U1) ==> member(U,[U1]) | fact(['a1:E18_Physical_Thing', X],add,U), applied_rules(1,ins).
phase(5), fact(['a2:child', _, X1],add,U1) ==> member(U,[U1]) | fact(['a3:Person', X1],add,U), applied_rules(1,ins).
phase(5), fact(['a1:P78_is_identified_by', _, X1],add,U1) ==> member(U,[U1]) | fact(['a1:E49_Time_Appellation', X1],add,U), applied_rules(1,ins).

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
