	
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