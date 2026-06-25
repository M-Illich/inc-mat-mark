
% -- remove facts that cannot be rederived --
phase(3) \ fact(_,del,_,_) <=> true.
phase(3) <=> true.


%-------------------------------------------------
% -- insertions --

% finish processing when every new fact has been inserted
current_update(U) \ update(add,[],U) <=> phase(4), finish_update.
% insert every new fact
current_update(U) \ update(add,[F|Fs],U) <=>
	fact(F,add,_,U),
	update(add,Fs,U).
	
% -- compute new derivable facts	--