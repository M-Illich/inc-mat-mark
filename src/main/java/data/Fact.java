package data;

import java.util.List;

public class Fact extends Atom implements Comparable<Fact> {
	
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

	@Override
	public int compareTo(Fact o) {
		// compare predicates
		int c = this.predicate.compareTo(o.predicate);
		// compare arguments
		if (c == 0) {
			// compare number of arguments
			Integer.compare(this.arguments.size(), o.arguments.size());
			// compare individual arguments
			for (int i = 0; i < this.arguments.size() && c == 0; i++) {
				c = this.arguments.get(i).compareTo(o.arguments.get(i));
			}
		}
		
		return c;
	}

}
