package eval;

import java.io.File;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.commons.lang3.StringUtils;

import data.Atom;
import data.Fact;
import data.Graph;
import data.Rule;
import data.Update;
import transform.BFTransformer;
import transform.DRedTransformer;
import transform.FactExtracter;
import transform.RuleReader;
import transform.Transformer;
import transform.UpdatesCreator;

public class EvaluationPreparer {

	final static Set<String> ALGORITHMS = Set.of("dred", "bf");

	final static Set<String> TEST_CASES = Set.of("random", "random-large", "batch", "overlap", "scale-update",
			"scale-data"); // Note: "real" updates are already provided

	final static Set<String> KNOWLEDGE_BASES = Set.of("path", "sequence", "claros", "dbpedia", "family", "lubm",
			"relations"); // Note: "ways" is already handled by tests for DRedTransformer

	final static List<Long> RANDOM_SEEDS = List.of(3682876523426446494l, -7227433133872759647l, -1521870568993095474l,
			414674000676533665l, -5535749218636893965l, 7217840207545846233l, -433576350867050697l,
			7450081150186899609l, -2232030332154254329l, 3341732484960904427l, 8087371546052459341l,
			1169850498570268648l, -2050702418703038236l, 5572221214320583751l, -8362907299058540472l,
			-3902863331811833142l, 7847669574699938735l, 8075569538961924907l);

	public static void main(String[] args) {

		for (String algo : ALGORITHMS) {
			for (String kb : KNOWLEDGE_BASES) {
				createAlgosInCHR(algo, kb);
			}
		}

		for (String tc : TEST_CASES) {
			for (String kb : KNOWLEDGE_BASES) {
				for (int i = 0; i < 3; i++) {
					createUpdateStreamFiles(tc, kb, i);
				}
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
		RuleReader rr = new RuleReader(
				new File("src/main/resources/kb/" + knowledgeBase + "/" + knowledgeBase + ".dlog"));
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

	/**
	 * Create a directory with files that each represent an update of a stream based
	 * on the given data.
	 * 
	 * @param testCase      {@code String} Determines predefined properties of
	 *                      updates
	 * @param knowledgeBase {@code String} Name of knowledge base from which facts
	 *                      are used to create updates
	 * @param testRun       {@code int} Determines which predefined random seed is
	 *                      chosen (0, 1, or 2)
	 */
	public static void createUpdateStreamFiles(String testCase, String knowledgeBase, int testRun) {
		// default setting for random test case
		int dataPoolSize = 200;
		int updateNumber = 50;
		List<Integer> initialUpdateSizes = new LinkedList<>(List.of(100));
		List<Integer> updateSizes = new LinkedList<>(List.of(10));
		int updateOverlapDel = 0;
		int updateOverlapAdd = 0;
		boolean asBatch = false;
		int testRunOffset = 0;

		switch (testCase) {
		case "random-large":
			dataPoolSize = 10000;
			testRunOffset = 3;
			break;
		case "batch":
			asBatch = true;
			testRunOffset = 6;
			break;
		case "overlap":
			updateOverlapDel = 5;
			updateOverlapAdd = 5;
			testRunOffset = 9;
			break;
		case "scale-update":
			updateNumber = 30;
			initialUpdateSizes = new LinkedList<>(List.of(100, 100, 100, 100, 100, 100, 100, 100, 100, 100));
			updateSizes = new LinkedList<>(List.of(5, 10, 15, 20, 25, 30, 35, 40, 45, 50));
			testRunOffset = 12;
			break;
		case "scale-data":
			dataPoolSize = 2000;
			updateNumber = 10;
			initialUpdateSizes = new LinkedList<>(List.of(100, 200, 300, 400, 500));
			updateSizes = new LinkedList<>(List.of(10, 20, 30, 40, 50));
			testRunOffset = 15;
		}

		try {

			long randomSeed = RANDOM_SEEDS.get(testRun + testRunOffset);
			String directory = "src/main/resources/updates/" + testCase + "/" + knowledgeBase + "/" + testRun + "/";
			System.out.println("--  Test case: " + testCase + "  --  Knowledge base: " + knowledgeBase
					+ "  --  Test run: " + testRun);

			// load data
			LinkedHashSet<Fact> dataPool = loadDataPool(knowledgeBase, dataPoolSize);

			for (int i = 0; i < updateSizes.size(); i++) {
				int initialUpdateSize = initialUpdateSizes.get(i);
				int updateSize = updateSizes.get(i);

				String testRunName = StringUtils.leftPad("" + initialUpdateSize,
						(initialUpdateSizes.getLast() + "").length(), "0") + "-"
						+ StringUtils.leftPad("" + updateSize, (updateSizes.getLast() + "").length(), "0") + "-"
						+ dataPoolSize;
				System.out.println(testRunName);

				// create updates
				UpdatesCreator uc = new UpdatesCreator(dataPool);
				List<Update> updates = uc.createRandomUpdates(updateNumber, initialUpdateSize, updateSize,
						updateOverlapDel, updateOverlapAdd, asBatch, randomSeed);

				// create directory for update stream
				Files.createDirectories(Paths.get(directory + testRunName));
				// create file for each update
				for (int j = 0; j < updates.size(); j++) {
					String num = StringUtils.leftPad("" + j, (updates.size() + "").length(), "0");
					writeUpdateToFile(updates.get(j), directory + testRunName + "/" + num);
				}

			}

		} catch (Exception e) {
			e.printStackTrace();
		}

	}

	private static LinkedHashSet<Fact> loadDataPool(String knowledgeBase, int dataPoolSize) {
		LinkedHashSet<Fact> dataPool;

		if (knowledgeBase == "lubm") {
			// OWL
			File fileOWL = new File("src/main/resources/kb/lubm/university.owl");
			dataPool = FactExtracter.getFactsFromOWL(fileOWL);
		} else if (knowledgeBase == "path" || knowledgeBase == "sequence") {
			// create set of edges as facts
			int nodesNum = 110;
			while (dataPoolSize > nodesNum * nodesNum) {
				nodesNum += 10;
			}
			Graph graph = new Graph(nodesNum, dataPoolSize, 123456789);
			dataPool = graph.edges;
		} else {
			// RDF
			File fileRDF = new File("src/main/resources/kb/" + knowledgeBase + "/" + knowledgeBase);
			dataPool = FactExtracter.getFactsFromRDF(fileRDF, "TURTLE");
		}

		// ensure that only explicit facts are used for updates
		RuleReader rr = new RuleReader(
				new File("src/main/resources/kb/" + knowledgeBase + "/" + knowledgeBase + ".dlog"));
		Transformer trf = new DRedTransformer(rr.rules);
		dataPool.removeIf(f -> !trf.explicitPredicates.contains(f.predicate));
		// limit size of data pool
		int dataPoolOffset = 0;
		dataPool = new LinkedHashSet<>(Arrays
				.asList(Arrays.copyOfRange(dataPool.toArray(new Fact[dataPoolSize]), dataPoolOffset, dataPoolSize)));

		return dataPool;
	}

	private static void writeUpdateToFile(Update update, String file) {
		try {
			PrintWriter writer = new PrintWriter(file + ".pl", "UTF-8");

			// write added facts
			for (Fact fact : update.added) {
				writer.println("add(" + fact.toString() + ").");
			}
			// write deleted facts
			for (Fact fact : update.deleted) {
				writer.println("delete(" + fact.toString() + ").");
			}

			writer.close();
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

}
