package data;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

public class Atom {

	public String predicate;
	public List<String> arguments;

	public Atom(String predicate, List<String> arguments) {
		this.predicate = ensureCorrectFormat(predicate);
		this.arguments = arguments.stream().map(a -> ensureCorrectFormat(a)).toList();
	}

	/**
	 * 
	 * @param string {@code String} that represents an atom in the form of
	 *               {@code [predicate, arg1, arg2, ...]} or
	 *               {@code predicate(arg1, arg2, ...)} or
	 *               {@code predicate[arg1, ...]} where {@code arg1} etc. start with
	 *               a lowercase letter for constants and either an uppercase letter
	 *               or {@code ?} for variables. Note that arguments must not
	 *               contain any commas.
	 * 
	 */
	public Atom(String string) {

		// transform atom into form [p, a1, a2, ...]
		if (!string.startsWith("[")) {

			// transform p(...) into p[...]
			string = string.replace("(", "[");
			string = string.replace(")", "]");

			String predicate = string.substring(0, string.indexOf("["));
			string = "[" + predicate + ", " + string.substring(string.indexOf("[") + 1);
		}

		String[] parts = string.substring(1, string.length() - 1).split(",");

		for (int i = 0; i < parts.length; i++) {
			String s = parts[i].trim();
			s = ensureCorrectFormat(s);
			parts[i] = s;

		}
		this.predicate = parts[0];
		this.arguments = Arrays.asList(parts).subList(1, parts.length);

	}

	/**
	 * Ensure compatibility with SWI-Prolog by writing variables with uppercase
	 * letters and by surrounding elements that contain colon with '...', e.g.,
	 * {@code p(?x, a:B)} turns into {@code p(X, 'a:B')}.
	 * 
	 * @param arg {@code String} representing the predicate or some argument of an
	 *            atom
	 * @return {@code String} of potentially adapted version of {@code arg}
	 */
	public String ensureCorrectFormat(String arg) {

		// surround elements that contain colon with '...' for compatibility with
		// SWI-Prolog
		if (arg.contains(":")) {
			if (!arg.startsWith("'")) {
				arg = "'" + arg;
			}
			if (!arg.endsWith("'")) {
				arg += "'";
			}
		}

		char[] chars = arg.toCharArray();
		for (int i = 0; i < chars.length; i++) {
			if (chars[i] == '?') {
				i++;
				chars[i] = (chars[i] + "").toUpperCase().charAt(0);
			}
		}

		return String.valueOf(chars).replace("?", "");
	}

	/**
	 * Check if String is a variable in the form of {@code ?x} or {@code X} (upper
	 * case).
	 * 
	 * @param arg A {@code String}
	 * @return {@code true} if argument is a variable, else {@code false}
	 */
	public boolean isVariable(String arg) {
		if (arg.startsWith("?") || Character.isUpperCase(arg.charAt(0))) {
			return true;
		}
		return false;
	}

	/**
	 * Transforms atom {@code p(a1,a2,...)} into a String {@code [p,a1,a2,...]}
	 */
	public String toBracketString() {
		LinkedList<String> atomList = new LinkedList<>(arguments);
		atomList.addFirst(predicate);
		return atomList.toString();
	}

	public String toString() {
		String args = arguments.toString().substring(1, arguments.toString().length() - 1);
		return predicate + "(" + args + ")";
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