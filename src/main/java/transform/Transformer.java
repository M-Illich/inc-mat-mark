package transform;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import data.Atom;
import data.Constraint;
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
	 * Create the CHR rule for the insertion phase of algorithm based on the given
	 * Datalog rule.
	 * 
	 * @param rule     A {@link Rule}
	 * @param withMark States whether or not the rule should include fact marking
	 * @return A {@code String} with the transformed CHR rule
	 */
	public String createInsertRule(Rule rule, boolean withMark) {

		// initialize transformed rule
		String chr = "phase(5)";
		// add transformed body atoms
		for (int i = 0; i < rule.body.size(); i++) {
			chr += ", fact(" + rule.body.get(i).toString() + ",add" + (withMark ? ",M" + (i + 1) : "") + ",U" + (i + 1)
					+ ")";
		}
		// add guard conditions
		chr += " ==> ";
		for (Constraint con : rule.constraints) {
			chr += con.toString() + ", ";
		}
		chr += "member(U,[U1";
		for (int i = 1; i < rule.body.size(); i++) {
			chr += ",U" + (i + 1);
		}
		chr += "]) | ";
		// add marking if needed
		if (withMark) {
			chr += "check_neg_mark([M1";
			for (int i = 1; i < rule.body.size(); i++) {
				chr += ",M" + (i + 1);
			}
			chr += "],M), ";
		}
		// add new head
		chr += "fact(" + rule.head.toString() + ",add" + (withMark ? ",M" : "") + ",U), applied_rules(1,ins).";

		return chr;
	}

}
