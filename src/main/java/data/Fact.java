package data;

public class Fact extends Atom {

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

	/**
	 * Check if String is a variable in the form of {@code ?x} or {@code X} (upper case).
	 * 
	 * @param arg A {@code String}
	 * @return {@code true} if argument is a variable, else {@code false}
	 */
	private boolean isVariable(String arg) {
		if (arg.startsWith("?") || Character.isUpperCase(arg.charAt(0))) {
			return true;
		}
		return false;
	}

}
