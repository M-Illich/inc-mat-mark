package data;

import java.util.List;

public class Fact extends Atom {
	
	public Fact(String predicate, List<String> arguments) {
		super(predicate, arguments);
	}

	/**
	 * 
	 * @param string {@code String} that represents a fact in the form of
	 *               {@code [predicate, arg1, arg2, ...]} or
	 *               {@code predicate(arg1, arg2, ...)}. *
	 * 
	 */
	public Fact(String fact) {
		super(fact);
	}

	/**
	 * Check if fact does not contain variables.
	 * 
	 * @return {@code true} if the arguments of the fact do not contain any
	 *         variable, else {@code false}
	 */
	public boolean isFact() {
		for (String arg : arguments) {
			if (isVariable(arg)) {
				return false;
			}
		}
		return true;
	}

}
