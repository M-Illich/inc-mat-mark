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