package eval;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import data.Atom;
import data.Rule;
import transform.BFTransformer;
import transform.DRedTransformer;
import transform.RuleReader;
import transform.Transformer;

public class AlgorithmsPreparer {

	final static Set<String> ALGORITHMS = Set.of("dred", "bf");
	final static Set<String> KNOWLEDGE_BASES = Set.of("path", "sequence", "claros", "dbpedia", "family", "lubm",
			"relations");
	// Note: "ways" is already handled by tests for DRedTransformer

	public static void main(String[] args) {

		for (String algo : ALGORITHMS) {
			for (String kb : KNOWLEDGE_BASES) {
				createAlgosInCHR(algo, kb);
			}
		}
	}

	/**
	 * Create two CHR programs for the specified algorithm (with and without
	 * marking) based on the rules in the given knowledge base.
	 * 
	 * @param algorithm     {@code String} name of algorithm
	 * @param knowledgeBase {@code String} name of knowledge base from which rules
	 *                      are used
	 */
	public static void createAlgosInCHR(String algorithm, String knowledgeBase) {
		System.out.println("Knowledge base: " + knowledgeBase);

		// read rules
		System.out.println("Read rules.");
		RuleReader rr = new RuleReader(new File("src/main/resources/" + knowledgeBase + "/" + knowledgeBase + ".dlog"));
		List<Rule> rules = rr.rules;
//		for (Rule r : rr.rules) {
//			System.out.println(r.toString());
//		}
//		System.out.println();

		// prepare transformer
		Transformer transformer;
		if (algorithm == "dred") {
			transformer = new DRedTransformer(rules);
		} else {
			transformer = new BFTransformer(rules);
		}
		// get number of rules with explicit (edb) predicates in body
		HashMap<Integer, Integer> explicitCounts = new HashMap<>();
		for (Rule r : rules) {
			for (Atom a : r.body) {
				if (transformer.explicitPredicates.contains(a.predicate)) {
					explicitCounts.putIfAbsent(r.body.size(), 0);
					explicitCounts.compute(r.body.size(), (_, v) -> v + 1);
					break;
				}
			}
		}

		rr.ruleSizes.forEach((k, v) -> System.out.println("  Rule body size " + k + ": " + v + " (where "
				+ (explicitCounts.get(k) == null ? 0 : explicitCounts.get(k)) + " contain(s) explicit predicates)"));

		// transform Datalog rules into CHR programs
		System.out.println("Transform rules into CHR.");
		String chrNoMark = transformer.createCHRProgram(knowledgeBase, false);
		String chrMark = transformer.createCHRProgram(knowledgeBase, true);
		// print out address of CHR files
		System.out.println("  " + chrNoMark);
		System.out.println("  " + chrMark);
		System.out.println();
	}

}
