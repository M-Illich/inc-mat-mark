package data;

import java.util.LinkedList;
import java.util.List;

public class Rule {

	public Atom head;
	public List<Atom> body;
	public List<Constraint> constraints;

	public Rule(Atom head, List<Atom> body, List<Constraint> constraints) {
		this.head = head;
		this.body = body;
		this.constraints = constraints;
	}

	public Rule(Atom head, List<Atom> body) {
		this.head = head;
		this.body = body;
		this.constraints = new LinkedList<>();
	}

	/**
	 * 
	 * @param ruleString String in the form of {@code head :- body1, body2, ..., .}
	 *                   where the atoms {@code head} and {@code body1} etc. might
	 *                   be of the form {@code predicate[?var1, ..., const1, ...]}
	 *                   or {@code predicate(?var1, ..., const1, ...)}
	 */
	public Rule(String ruleString) {
		// extract head
		this.head = new Atom(ruleString.substring(0, ruleString.indexOf(":-")).trim());

		// extract body atoms
		this.body = new LinkedList<>();
		String bodyString = ruleString.trim().substring(ruleString.indexOf(":-") + 2, ruleString.lastIndexOf(".")).trim();
		// transform p[...] into p(...)
		bodyString = bodyString.replace("[", "(");
		bodyString = bodyString.replace("]", ")");
		// get individual body atoms
		String[] parts = bodyString.split("\\)");
		for (int i = 0; i < parts.length; i++) {
			// remove leading whitespace and comma, and add removed closing parenthesis
			String str = parts[i].trim() + ")";
			if (str.startsWith(",")) {
				str = str.substring(1).trim();
			}
			if (!str.isEmpty()) {
				body.add(new Atom(str));
			}
		}
		
		/*
		 * TODO
		 * handle rules with constraints, e.g., X < Y etc.
		 */
		this.constraints = new LinkedList<>();

	}

}
