package data;

import java.util.HashSet;
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
		String bodyString = ruleString.trim().substring(ruleString.indexOf(":-") + 2, ruleString.lastIndexOf("."))
				.trim();
		// transform p(...) into p[...]
		bodyString = bodyString.replace("(", "[");
		bodyString = bodyString.replace(")", "]");
		// get individual body atoms
		String[] parts = bodyString.split("\\]");
		for (int i = 0; i < parts.length; i++) {
			// remove leading whitespace and comma, and add removed closing parenthesis
			String str = parts[i].trim() + "]";
			if (str.startsWith(",")) {
				str = str.substring(1).trim();
			}
			if (!str.isEmpty()) {
				body.add(new Atom(str));
			}
		}

		// replace singleton variables by anonymous variables
		replaceSingletonVariables();

		/*
		 * TODO handle rules with constraints, e.g., X < Y etc. 
		 * NOTE: For our evaluation, we only consider knowledge bases where rules do not 
		 * have constraints (except for "ways" where constraints are explicitly defined 
		 * and not read from file)
		 */
		this.constraints = new LinkedList<>();

	}

	/**
	 * Replace variables that only occur once in the rule by unnamed variables (to
	 * avoid conflicts with SWI-Prolog)
	 */
	public void replaceSingletonVariables() {
		HashSet<String> checkedVariables = new HashSet<>();

		for (int i = 0; i < body.size(); i++) {
			Atom atom = body.get(i);
			List<String> args = new LinkedList<>(atom.arguments);

			for (int j = 0; j < args.size(); j++) {
				String arg = args.get(j);
				if (checkedVariables.add(arg)) {
					if (atom.isVariable(arg)) {
						boolean duplicateFound = false;

						// compare to arguments of same atom
						for (int k = j + 1; k < args.size(); k++) {
							if (arg.equals(args.get(k))) {
								duplicateFound = true;
								break;
							}
						}

						// compare to head
						for (int m = 0; m < head.arguments.size(); m++) {
							if (arg.equals(head.arguments.get(m))) {
								duplicateFound = true;
								break;
							}
						}

						// compare to other body facts
						for (int l = i + 1; l < body.size() && !duplicateFound; l++) {
							Atom atom2 = body.get(l);
							for (int n = 0; n < atom2.arguments.size(); n++) {
								if (arg.equals(atom2.arguments.get(n))) {
									duplicateFound = true;
									break;
								}
							}
						}

						if (!duplicateFound) {
							List<String> newArgs = args;
							// replace singleton variable
							newArgs.add(j, "_");
							newArgs.remove(j + 1);
							atom.arguments = newArgs;
						}
					}
				}
			}
		}
	}

	public String toString() {
		String str = body.getFirst().toString();
		// add body atoms
		for (int i = 1; i < body.size(); i++) {
			str += ", " + body.get(i).toString();
		}
		// add constraints
		for (int i = 0; i < constraints.size(); i++) {
			str += ", " + constraints.get(i).toString();
		}
		// add head
		str += " -> " + head.toString();

		return str;
	}

}
