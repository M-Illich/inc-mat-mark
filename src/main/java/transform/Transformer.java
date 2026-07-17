package transform;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import data.Atom;
import data.Rule;

public abstract class Transformer {

	/**
	 * {@link List} of {@link Rule} objects representing (positive) Datalog rules
	 */
	public List<Rule> ruleSet;

	/**
	 * Predicates of atoms that only occur in body atoms
	 */
	public List<String> explicitPredicates;

	/**
	 * Get every explicit predicate that only appears as part of body atoms in the
	 * given set of rules
	 * 
	 * @param ruleset a {@link List} of {@link Rule} objects
	 * @return A {@link List} of {@link String}
	 */
	public List<String> getExplicitPredicates(List<Rule> ruleset) {
		List<String> predicates = new LinkedList<>();
		Set<String> checked = new HashSet<>();

		// go through rules and extract predicates that only occur in body atom
		for (Rule r : ruleset) {
			for (Atom b : r.body) {
				if (checked.add(b.predicate)) {
					boolean isExplicit = true;
					for (Rule r2 : ruleset) {
						if (r2.head.predicate.equals(b.predicate)) {
							isExplicit = false;
							break;
						}
					}
					if (isExplicit) {
						predicates.add(b.predicate);
					}
				}
			}
		}

		return predicates;
	}

	/**
	 * Create a CHR program based on the transformer's set of rules
	 * 
	 * @param name     {@link String} as name for created CHR program
	 * @param withMark {@code boolean} which states whether the algorithm should
	 *                 include marking or not
	 * @return {@link String} address of file that contains CHR program
	 */
	public abstract String createCHRProgram(String name, boolean withMark);

}
