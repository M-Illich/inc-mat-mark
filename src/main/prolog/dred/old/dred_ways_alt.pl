/*
Delete/Rederive
with memorizing if alternative duplicate occurred

connections among ways of OSM map data based on GPS tracks
*/

:- use_module(library(chr)).
:- chr_constraint init/1, stream/1,
	read_stream/1, phase/1,
	available_input/1, extract_input/2,
	update/2, stream_end/0,
	fact/4, finish_update/0,
	num_updates/1,
	clean/0, applied_rules/2, print/0.

%:- chr_option(debug, off).
:- chr_option(optimize, off).


% initialization
init(Port) <=> 
	setup_call_cleanup(
		% connect to server 
		tcp_connect(Port, Stream, []),		
		(	stream(Stream),
			num_updates(0),
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
print, applied_rules(N,P) ==> writeln(applied_rules(N,P)).


% -- remove constraints for simpler output --
clean \ fact(_,_,_,_) <=> true.	
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
	fact(F,del,_,_),
	update(del,Fs).
	
	
%-----------------
% no duplicates
% but remember that alternative occurred
fact(F,O,A,_) \ fact(F,O,_,_) <=> A = 1.


%-------------------------------------------------
% -- deletions --
% remove deleted add-fact
fact(F,del,A,U) \ fact(F,add,A2,U2) <=> U = U2, A = A2.


% -- delete every fact that depends on a deleted fact --
phase(1), 
fact([nextInWay,X1,Y1,Z1],O1,_,_), fact([nextInWay,X2,Y2,Z2],O2,_,_)
 \ fact([connection,Z1,Z2],add,A,U) <=> 
	Z1 \== Z2,
	member(del,[O1,O2]),
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2) |
	fact([connection,Z1,Z2],del,A,U),
	applied_rules(1,del).	
	
phase(1), 
fact([connection,X,Y],O1,_,_), fact([connection,Y,Z],O2,_,_) 
\ fact([connection,X,Z],add,A,U) <=> 
	X \== Y, 
	member(del,[O1,O2]) |
	fact([connection,X,Z],del,A,U),
	applied_rules(1,del).	

phase(1) <=> phase(2).


% -- re-add deleted facts that still have some alternative derivation --

% directly remove facts for which no duplicate has occurred
phase(2) \ fact(_,del,A,_) <=> var(A) | true.

% only facts for which a duplicate occurred need to be checked
phase(2), 
fact([nextInWay,X1,Y1,Z1],add,_,U), fact([nextInWay,X2,Y2,Z2],add,_,_) 
\ fact([connection,Z1,Z2],del,1,_) <=> 
	Z1 \== Z2,
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2) |
	fact([connection,Z1,Z2],add,1,U),
	applied_rules(1,red).
	
phase(2), 
fact([connection,X,Y],add,_,U), fact([connection,Y,Z],add,_,_) 
\ fact([connection,X,Z],del,1,_) <=> 
	X \== Y |
	fact([connection,X,Z],add,1,U),
	applied_rules(1,red).	

phase(2) <=> phase(3).


% -- remove facts that cannot be rederived --
phase(3) \ fact(_,del,_,_) <=> true.
phase(3) <=> true.


%-------------------------------------------------
% -- insertions --

% finish processing when every new fact has been inserted
update(add,[]) <=> phase(5), finish_update.
% insert every new fact
num_updates(U) \ update(add,[F|Fs]) <=>
	fact(F,add,_,U),
	update(add,Fs).
	
% -- compute new derivable facts	--
phase(5), num_updates(U), 
fact([nextInWay,X1,Y1,Z1],add,_,U1), fact([nextInWay,X2,Y2,Z2],add,_,U2)  ==> 
	member(U,[U1,U2]),
	Z1 \== Z2,
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2)	|
	fact([connection,Z1,Z2],add,_,U),
	applied_rules(1,ins).
phase(5), num_updates(U), 
fact([connection,X,Y],add,_,U1), fact([connection,Y,Z],add,_,U2) ==> 
	X \== Y,
	member(U,[U1,U2]) |
	fact([connection,X,Z],add,_,U),
	applied_rules(1,ins).


%----------------
% -- write materialization to stream --
finish_update, stream(S), num_updates(N) ==> writeln(S,materialization(N)). 	
finish_update, stream(S), fact(F,add,_,_) ==> writeln(S,F).	
finish_update, stream(S) ==> writeln(S,""), flush_output(S).

% -- move on to next update --
finish_update, phase(5) <=> read_stream(infinite).
