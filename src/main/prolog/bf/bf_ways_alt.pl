/*
Backward/Forward 

connections among ways of OSM map data based on GPS tracks
*/

:- use_module(library(chr)).
:- chr_constraint init/1, stream/1,
	read_stream/1, phase/1,
	available_input/1, extract_input/2,
	update/3, stream_end/0,
	fact/4, finish_update/0,
	check_done/0, no_del/0,
	num_updates/1, current_update/1,
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
			current_update(1),
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
		

% start processing when every deleted fact has been inserted
current_update(U) \ update(del,[],U) <=> phase(1).
% insert every deleted fact for current update
current_update(U) \ update(del,[F|Fs],U) <=>
	fact(_,F,del,U),
	update(del,Fs,U).
	
	
	
%-----------------
% no duplicates
% memorize that duplicate occurred
fact(A,F,O,_) \ fact(_,F,O,_) <=> A = 1.
	

%-------------------------------------------------
% -- deletions --
% remove deleted add-fact
fact(_,F,del,_) \ fact(_,F,add,_) <=> true.


% -- find every directly affected fact that needs to be checked --
phase(1), 
fact(_,[nextInWay,X1,Y1,Z1],O1,_), fact(_,[nextInWay,X2,Y2,Z2],O2,_) \ fact(A,[connection,Z1,Z2],add,U) <=> 
	Z1 \== Z2,
	member(del,[O1,O2]),
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2) |
	fact(A,[connection,Z1,Z2],chk,U),
	applied_rules(1,del).
	
phase(1), 
fact(_,[connection,X,Y],O1,_), fact(_,[connection,Y,Z],O2,_) \ fact(A,[connection,X,Z],add,U) <=> 
	member(del,[O1,O2]),
	X \== Y |
	fact(A,[connection,X,Z],chk,U),
	applied_rules(1,del).


% -- delete already processed del-facts to avoid repetitions with new del-facts --
phase(1) <=> phase(2).
phase(2) \ fact(_,_,del,_) <=> true.
phase(2) <=> no_del, phase(3).


% prevent repeated checking
fact(_,F,chk1,_) \ fact(_,F,chk,_) <=> true.
fact(_,F,chk1,_) \ fact(_,F,add,_) <=> true.

% -- check facts for alternative derivation --
% only check fact if it had an alternative derivation before ...
phase(3) \ fact(1,F,chk,U) <=> fact(1,F,chk1,U), check_done.
% ... else directly delete it
phase(3) \ fact(_,F,chk,U) <=> fact(_,F,del,U).

% fact can be proven
fact(_,F,prv,_) \ fact(_,F,_,_) <=> true.
	

% - forward -
fact(_,[nextInWay,X1,Y1,Z1],prv,_), fact(_,[nextInWay,X2,Y2,Z2],prv,_) \ fact(A,[connection,Z1,Z2],chk1,U) <=> 
	Z1 \== Z2,
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2) |
	fact(A,[connection,Z1,Z2],prv,U),
	applied_rules(1,fwd).
	
fact(_,[connection,X,Y],prv,_), fact(_,[connection,Y,Z],prv,_)  \ fact(A,[connection,X,Z],chk1,U) <=>
	X \== Y |
	fact(A,[connection,X,Z],prv,U),
	applied_rules(1,fwd).		
	
fact(_,[nextInWay,X1,Y1,Z1],prv,_), fact(_,[nextInWay,X2,Y2,Z2],prv,_) \ fact(A,[connection,Z1,Z2],chk,U) <=> 
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2)	|
	fact(A,[connection,Z1,Z2],prv,U),
	applied_rules(1,fwd).
	
fact(_,[connection,X,Y],prv,_), fact(_,[connection,Y,Z],prv,_)  \ fact(A,[connection,X,Z],chk,U) <=>
	X \== Y |
	fact(A,[connection,X,Z],prv,U),
	applied_rules(1,fwd).		


	
% - backward -
fact(_,[connection,Z1,Z2],chk1,_) \
fact(A1,[nextInWay,X1,Y1,Z1],add,U1), fact(A2,[nextInWay,X2,Y2,Z2],add,U2) <=>
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2) |
	fact(A1,[nextInWay,X1,Y1,Z1],prv,U1), 
	fact(A2,[nextInWay,X2,Y2,Z2],prv,U2),	
	applied_rules(1,bwd).
fact(_,[connection,Z1,Z2],chk1,_), 
fact(_,[nextInWay,X1,Y1,Z1],prv,_) \ fact(A,[nextInWay,X2,Y2,Z2],add,U2) <=>
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2) |
	fact(A,[nextInWay,X2,Y2,Z2],prv,U2),	
	applied_rules(1,bwd).
fact(_,[connection,Z1,Z2],chk1,_), 
fact(_,[nextInWay,X2,Y2,Z2],prv,_) \ fact(A,[nextInWay,X1,Y1,Z1],add,U1) <=>
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2) |
	fact(A,[nextInWay,X1,Y1,Z1],prv,U1), 
	applied_rules(1,bwd).
	
fact(_,[connection,X,Z],chk1,_) \ fact(A1,[connection,X,Y],add,U1), fact(A2,[connection,Y,Z],add,U2) <=>
	X \== Y |
	fact(A1,[connection,X,Y],chk1,U1), 
	fact(A2,[connection,Y,Z],chk1,U2),	
	applied_rules(1,bwd).
fact(_,[connection,X,Z],chk1,_), fact(_,[connection,X,Y],O1,_) \ fact(A,[connection,Y,Z],add,U2) <=>
	member(O1, [chk1, prv]),
	X \== Y |
	fact(A,[connection,Y,Z],chk1,U2),	
	applied_rules(1,bwd).	
fact(_,[connection,X,Z],chk1,_), fact(_,[connection,Y,Z],O2,_) \ fact(A,[connection,X,Y],add,U1)<=>
	member(O2, [chk1, prv]),
	X \== Y |
	fact(A,[connection,X,Y],chk1,U1),	
	applied_rules(1,bwd).	

	
% turn facts without proof into del-facts
check_done \ fact(A,F,chk1,U) <=> fact(A,F,del,U).
check_done <=> true.


% -- repeat above steps iff new del-facts given --
fact(_,_,del,_) \ no_del <=> true.
phase(3), no_del  <=> phase(4). % move to insertion phase
phase(3) <=> phase(1).


% -- reset deletion phase --
phase(4) \ fact(A,F,prv,U) <=> fact(A,F,add,U).
phase(4) <=> true.


%-------------------------------------------------
% -- insertions --

% finish processing when every new fact has been inserted
current_update(U) \ update(add,[],U) <=> phase(5), finish_update.
% insert every new fact
current_update(U) \ update(add,[F|Fs],U) <=>
	fact(_,F,add,U),
	update(add,Fs,U).
	
% -- compute new derivable facts	--
phase(5),  current_update(U), 
fact(_,[nextInWay,X1,Y1,Z1],add,U1), fact(_,[nextInWay,X2,Y2,Z2],add,U2) ==> 
	member(U,[U1,U2]),
	Z1 \== Z2,
	(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2) |
	fact(_,[connection,Z1,Z2],add,U),
	applied_rules(1,ins).
phase(5),  current_update(U), 
fact(_,[connection,X,Y],add,U1), fact(_,[connection,Y,Z],add,U2) ==> 
	member(U,[U1,U2]),
	X \== Y |	
	fact(_,[connection,X,Z],add,U),
	applied_rules(1,ins).



%----------------
% -- write materialization to stream --
finish_update, stream(S), current_update(N) ==> writeln(S, materialization(N)). 	
finish_update, stream(S), fact(_,F,add,_) ==> writeln(S,F).	
finish_update, stream(S) ==> writeln(S,""), flush_output(S).


% -- move on to next update --

% start next update's processing
finish_update, phase(5), current_update(U) <=> 
	V is U + 1,
	read_stream(infinite),
	current_update(V).

