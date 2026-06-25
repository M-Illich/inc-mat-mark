package data;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

public class Atom {

	public String predicate;
	public List<String> arguments;

	public Atom(String predicate, List<String> arguments) {
		this.predicate = predicate;
		this.arguments = arguments;
	}

	/**
	 * 
	 * @param string {@code String} that represents an atom in the form of
	 *               {@code [predicate, arg1, arg2, ...]} or
	 *               {@code predicate(arg1, arg2, ...)} or
	 *               {@code predicate[arg1, ...]} where {@code arg1} etc. start with
	 *               a lowercase letter for constants and either an uppercase letter
	 *               or {@code ?} for variables
	 * 
	 */
	public Atom(String string) {
		// transform variables that start with ? into ones that start with uppercase
		// letter
		string = string.replace("?", "X");

		// [predicate, arg1, arg2, ...]
		if (string.startsWith("[") && string.endsWith("]")) {
			String[] parts = string.substring(1, string.length() - 1).split(",");
			for (int i = 0; i < parts.length; i++) {
				parts[i] = parts[i].trim();
			}
			this.predicate = parts[0];
			this.arguments = Arrays.asList(parts).subList(1, parts.length);
		}

		else {
			// transform p[...] into p(...)
			string = string.replace("[", "(");
			string = string.replace("]", ")");

			// predicate(arg1, arg2, ...)
			this.predicate = string.substring(0, string.indexOf("("));
			String[] parts = string.substring(string.indexOf("(") + 1, string.length() - 1).split(",");
			for (int i = 0; i < parts.length; i++) {
				parts[i] = parts[i].trim();
			}
			this.arguments = Arrays.asList(parts).subList(0, parts.length);
		}

	}

	/**
	 * Transforms atom {@code p(a1,a2,...)} into a String {@code [p,a1,a2,...]}
	 */
	public String toString() {
		LinkedList<String> atomList = new LinkedList<>(arguments);
		atomList.addFirst(predicate);
		return atomList.toString();
	}

	@Override
	public boolean equals(Object a) {
		return this.toString().equals(a.toString());

	}

	@Override
	public int hashCode() {
		return this.toString().hashCode();
	}

}