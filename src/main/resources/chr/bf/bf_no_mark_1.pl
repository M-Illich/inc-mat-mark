
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
	
