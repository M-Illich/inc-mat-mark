package eval;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import data.Fact;
import data.Graph;
import data.Update;
import transform.DRedTransformer;
import transform.FactExtracter;
import transform.RuleReader;
import transform.Transformer;
import transform.UpdatesCreator;

public class Evaluation {

	final static int REPETITIONS = 5;
	final static Set<String> ALGORITHMS = Set.of("dred", "bf");
	final static Set<String> TEST_CASES = Set.of("random", "random-large", "batch", "overlap", "scale-update",
			"scale-data", "real");
	final static Set<String> KNOWLEDGE_BASES = Set.of("path", "sequence", "claros", "dbpedia", "family", "lubm",
			"relations", "ways");
	final static List<Long> RANDOM_SEEDS = List.of(3682876523426446494l, -7227433133872759647l, -1521870568993095474l,
			414674000676533665l, -5535749218636893965l, 7217840207545846233l, -433576350867050697l,
			7450081150186899609l, -2232030332154254329l, 3341732484960904427l, 8087371546052459341l,
			1169850498570268648l, -2050702418703038236l, 5572221214320583751l, -8362907299058540472l,
			-3902863331811833142l, 7847669574699938735l, 8075569538961924907l);

	public static void main(String[] args) throws Exception {

		String algorithm = "dred";
		String testCase = "random";
		String knowledgeBase = "lubm";
		int testRun = 1;
		
		if (args.length == 4) {
			algorithm = args[0];
			testCase = args[1];
			knowledgeBase = args[2];
			testRun = Integer.parseInt(args[3]);
		}

		if (!ALGORITHMS.contains(algorithm)) {
			throw new Exception("Invalid algorithm.");
		}
		if (!TEST_CASES.contains(testCase)) {
			throw new Exception("Invalid test case.");
		}
		if (!KNOWLEDGE_BASES.contains(knowledgeBase)) {
			throw new Exception("Invalid knowledge base.");
		}
		if (testRun < 0 || testRun > 2) {
			throw new Exception("Invalid test run selection.");
		}

		if (testCase == "real") {
			knowledgeBase = "ways";
		}

		performEvaluation(algorithm, testCase, knowledgeBase, testRun);

	}

	private static void performEvaluation(String algorithm, String testCase, String knowledgeBase, int testRun)
			throws Exception {

		// default setting for random test case
		int dataPoolSize = 200;
		int updateNumber = 50;
		List<Integer> initialUpdateSizes = new LinkedList<>(List.of(100));
		List<Integer> updateSizes = new LinkedList<>(List.of(10));
		int updateOverlapDel = 0;
		int updateOverlapAdd = 0;
		boolean asBatch = false;
		boolean realTest = false;

		switch (testCase) {
		case "random-large":
			dataPoolSize = 10000;
			testRun += 3;
			break;
		case "batch":
			asBatch = true;
			testRun += 6;
			break;
		case "overlap":
			updateOverlapDel = 5;
			updateOverlapAdd = 5;
			testRun += 9;
			break;
		case "scale-update":
			updateNumber = 30;
			initialUpdateSizes = new LinkedList<>(List.of(100, 100, 100, 100, 100, 100, 100, 100, 100, 100));
			updateSizes = new LinkedList<>(List.of(5, 10, 15, 20, 25, 30, 35, 40, 45, 50));
			testRun += 12;
			break;
		case "scale-data":
			dataPoolSize = 2000;
			updateNumber = 10;
			initialUpdateSizes = new LinkedList<>(List.of(100, 200, 300, 400, 500));
			updateSizes = new LinkedList<>(List.of(10, 20, 30, 40, 50));
			testRun += 15;
			break;
		case "real":
			realTest = true;
		}

		System.out.println(
				"Algorithm: " + algorithm + "  --  Knowledge base: " + knowledgeBase + "  --  Test run: " + testRun);

		if (realTest) {
			List<Update> updates = new UpdateStreamRun("",
					"src/main/resources/ways/updates_track" + testRun).updateList;

			// prepare directories to store statistics
			String directory = "results/" + algorithm + "/" + testCase + "/" + knowledgeBase + "/" + "updates_track"
					+ testRun;
			String testRunName = "";

			// perform evaluation
			processAlgorithms(algorithm, knowledgeBase, directory, testRunName, updates);
		} else {
			try {

				long randomSeed = RANDOM_SEEDS.get(testRun);

				for (int i = 0; i < updateSizes.size(); i++) {
					int initialUpdateSize = initialUpdateSizes.get(i);
					int updateSize = updateSizes.get(i);

					// load data
					System.out.println("Load data pool.");
					LinkedHashSet<Fact> dataPool = loadDataPool(knowledgeBase, dataPoolSize);
					System.out.println("  Data pool size: " + dataPool.size());

					// create updates
					System.out.println("Create updates.");
					UpdatesCreator uc = new UpdatesCreator(dataPool);
					List<Update> updates = uc.createRandomUpdates(updateNumber, initialUpdateSize, updateSize,
							updateOverlapDel, updateOverlapAdd, asBatch, randomSeed);

					// prepare directories to store statistics
					String directory = "results/" + algorithm + "/" + testCase + "/" + knowledgeBase + "/" + randomSeed;
					String testRunName = initialUpdateSize + "-" + updateSize + "-" + dataPoolSize;

					// perform evaluation
					processAlgorithms(algorithm, knowledgeBase, directory, testRunName + "/", updates);
				}

			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	private static void processAlgorithms(String algorithm, String knowledgeBase, String directory, String testRunName,
			List<Update> updates) {
		for (String approach : List.of("no_mark", "mark")) {
			// get CHR code with algorithm
			String chrFile = "src/main/prolog/" + algorithm + "/" + algorithm + "_" + knowledgeBase + "_" + approach
					+ ".pl";
			// process update stream
			System.out.println();
			System.out.println("Approach: " + approach);
			// collect statistics
			List<Statistics> stats = new LinkedList<>();
			for (int round = 1; round <= REPETITIONS; round++) {
				System.out.println("Round: " + round);
				UpdateStreamRun usr = new UpdateStreamRun(chrFile, updates);
				usr.execute(false, false, false);
				stats.add(usr.statistics);
			}
			// store statistics in files
			storeStatistics(directory + "/" + approach + "/" + testRunName, stats);
		}
	}

	private static void storeStatistics(String directory, List<Statistics> stats) {
		try {
			Files.createDirectories(Paths.get(directory));
			PrintWriter writer;
			String line;

			// update times
			writer = new PrintWriter(directory + "update_times" + ".csv", "UTF-8");
			for (Statistics stat : stats) {
				line = stat.updateTimes.toString();
				line = line.substring(1, line.length() - 1);
				writer.println(line);
			}
			writer.close();

			// number of applied rules
			for (String type : stats.get(0).appliedRules.keySet()) {
				writer = new PrintWriter(directory + "/applied_rules_" + type + ".csv", "UTF-8");
				for (Statistics stat : stats) {
					line = stat.appliedRules.get(type).toString();
					line = line.substring(1, line.length() - 1);
					writer.println(line);
				}
				writer.close();
			}

			// number of marked facts
			if (!stats.get(0).markedFacts.isEmpty()) {
				for (String type : stats.get(0).markedFacts.keySet()) {
					writer = new PrintWriter(directory + "/marked_facts_" + type + ".csv", "UTF-8");
					for (Statistics stat : stats) {
						line = stat.markedFacts.get(type).toString();
						line = line.substring(1, line.length() - 1);
						writer.println(line);
					}
					writer.close();
				}
			}

		} catch (IOException e) {
			e.printStackTrace();
		}

	}

	private static LinkedHashSet<Fact> loadDataPool(String knowledgeBase, int dataPoolSize) {
		LinkedHashSet<Fact> dataPool;

		if (knowledgeBase == "lubm") {
			// OWL
			File fileOWL = new File("src/main/resources/lubm/university.owl");
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
			File fileRDF = new File("src/main/resources/" + knowledgeBase + "/" + knowledgeBase);
			dataPool = FactExtracter.getFactsFromRDF(fileRDF, "TURTLE");
		}

		// ensure that only explicit facts are used for updates
		RuleReader rr = new RuleReader(new File("src/main/resources/" + knowledgeBase + "/" + knowledgeBase + ".dlog"));
		Transformer trf = new DRedTransformer(rr.rules);
		dataPool.removeIf(f -> !trf.explicitPredicates.contains(f.predicate));
		// limit size of data pool
		int dataPoolOffset = 0;
		dataPool = new LinkedHashSet<>(Arrays
				.asList(Arrays.copyOfRange(dataPool.toArray(new Fact[dataPoolSize]), dataPoolOffset, dataPoolSize)));

		return dataPool;
	}

}
