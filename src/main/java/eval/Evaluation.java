package eval;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class Evaluation {

	final static Set<String> ALGORITHMS = Set.of("dred", "bf");
	final static Set<String> TEST_CASES = Set.of("random", "random-large", "batch", "overlap", "scale-update",
			"scale-data", "real");
	final static Set<String> KNOWLEDGE_BASES = Set.of("path", "sequence", "claros", "dbpedia", "family", "lubm",
			"relations", "ways");

	public static void main(String[] args) throws Exception {

		String algorithm = "dred";
		String testCase = "random";
		String knowledgeBase = "path";
		int testRun = 0;

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

		System.out.println("Algorithm: " + algorithm + "  --  Test case: " + testCase + "  --  Knowledge base: "
				+ knowledgeBase + "  --  Test run: " + testRun);

		int repetitions = 5;
		// less repetitions for "scale" cases due to longer processing times
		if (testCase.startsWith("scale")) {
			repetitions = 3;
		}

		// load predefined update streams from files
		String streamFoldersFile = "src/main/resources/updates/" + testCase + "/" + knowledgeBase + "/" + testRun + "/";
		String[] streamFolders = new File(streamFoldersFile).list();
		for (String streamFolder : streamFolders) {
			if (testCase == "real") {
				System.out.println(streamFolder);
			} else {
				System.out.println("Initial dataset size - update size - data pool size: " + streamFolder);
			}

			// prepare directories to store statistics
			String statsDirectory = "results/" + algorithm + "/" + testCase + "/" + knowledgeBase + "/" + testRun;

			// perform evaluation
			processAlgorithms(algorithm, knowledgeBase, statsDirectory, streamFoldersFile + streamFolder, repetitions);

		}

	}

	private static void processAlgorithms(String algorithm, String knowledgeBase, String statisticsDirectory,
			String updateFolder, int repetitions) {
		for (String approach : List.of("no_mark", "mark")) {
			// get CHR code with algorithm
			String chrFile = "src/main/prolog/" + algorithm + "/" + algorithm + "_" + knowledgeBase + "_" + approach
					+ ".pl";
			// get file name of update stream
			String streamFileName = updateFolder.substring(updateFolder.lastIndexOf("/") + 1);

			// process update stream
			System.out.println();
			System.out.println("Approach: " + approach);
			List<Statistics> stats = new LinkedList<>();
			for (int round = 1; round <= repetitions; round++) {
				System.out.println("Round: " + round);
				UpdateStreamRun usr = new UpdateStreamRun(chrFile, updateFolder);
				usr.execute(false, false, false);
				stats.add(usr.statistics);
			}
			// store statistics in files
			storeStatistics(statisticsDirectory + "/" + streamFileName + "/" + approach, stats);
		}
	}

	private static void storeStatistics(String directory, List<Statistics> stats) {
		try {
			Files.createDirectories(Paths.get(directory));
			PrintWriter writer;
			String line;

			// update times
			writer = new PrintWriter(directory + "/update_times" + ".csv", "UTF-8");
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

}
