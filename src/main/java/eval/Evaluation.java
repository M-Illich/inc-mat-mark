package eval;

import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Set;

import data.Fact;

public class Evaluation {

	/**
	 * number of repeated runs to compute average runtime
	 */
	final static int REPETITIONS = 5;

	/**
	 * "dred" or "bf" tests are possible
	 */
	static String TEST_ALGO = "dred"; // "bf"; //

	/**
	 * "ways" or TODO tests are possible
	 */
	static String TEST_TYPE = "ways";

	/**
	 * for "ways": 0 (GPS track0), 1 (GPS track1), or 2 (GPS track2)
	 */
	static int TEST_CASE = 1;

	public static void main(String[] args) throws Exception {

		if (args.length >= 3) {
			TEST_ALGO = args[0];
			TEST_TYPE = args[1];
			TEST_CASE = Integer.parseInt(args[2]);
		}

		if (TEST_ALGO != "dred" && TEST_ALGO != "bf") {
			throw new Exception("Invalid test algorithm. Only \"dred\" or \"bf\" are possible");
		}

		System.out.println("test type: " + TEST_TYPE + "  --  test case: " + TEST_CASE);

		if (TEST_TYPE.contentEquals("ways")) {
			if (TEST_CASE == 0 || TEST_CASE == 1 || TEST_CASE == 2) {
				String updateFolder = "src/main/resources/updates/ways/updates_track" + TEST_CASE;
				List<String> filesWays;
				if (TEST_ALGO == "dred") {
					filesWays = List.of("dred/dred_ways_no_mark.pl", "dred/dred_ways_mark.pl");
				} else {
					filesWays = List.of("bf/bf_ways_no_mark.pl", "bf/bf_ways_mark.pl");
				}
				for (String file : filesWays) {
					performEvaluation(file, updateFolder);
				}
			} else {
				throw new Exception("Invalid test case. Only 0, 1, or 2 are allowed for \"ways\" test");
			}

		}
		// TODO add further test cases
//		else if (TEST_TYPE.contentEquals("cross")) {
//			
//		}

		// invalid test type
		else {
			throw new Exception("Invalid test type. Only \"ways\" or TODO are allowed.");
		}

	}

	/**
	 * Use the materialization maintenance approach implemented in {@code file} to
	 * process a stream of updates based on provided updates. A csv-file is created,
	 * which shows the cpu runtime, the number of applied rules for the algorithm's
	 * phases, as well as the number of marked facts.
	 * 
	 * @param file         {@code String} name of file containing SWI-Prolog code to
	 *                     be executed
	 * @param updateFolder {@code String} name of folder where each stream update is
	 *                     stored as file
	 */
	public static void performEvaluation(String file, String updateFolder) {

		String approach = file.substring(file.indexOf("/") + 1, file.length() - 3);
		String updatesName = updateFolder.substring(updateFolder.lastIndexOf("/") + 1);
		System.out.println(approach);

		PrintWriter writer;

		try {
			Files.createDirectories(Paths.get("results"));
			// store results as table in a file
			writer = new PrintWriter("results/results-" + approach + "-map_stream-" + updatesName + ".csv", "UTF-8");
			// different statistics (used as columns for table in file)
			String categories = "cpuTime,appliedRules(del),appliedRules(red),appliedRules(ins),markedFacts(ex),markedFacts(im)";
			// backward/forward uses different statistics
			if (TEST_ALGO == "bf") {
				categories = categories.replace("appliedRules(red)", "appliedRules(bwd),appliedRules(fwd)");
			}
			writer.println(categories);

			// create update stream
			RealUpdateStreamRun usr = new RealUpdateStreamRun(file, updateFolder);

			float avgCpuTime = 0;
			for (int i = 0; i < REPETITIONS; i++) {
				// process update stream
				usr.execute(false, false, false);
				avgCpuTime += usr.statistics.cpuTime;
			}

			// get materialization sizes
			int avgMatSize = 0;
			int maxMatSize = 0;
			for (Set<Fact> s : usr.queryAnswers) {
				avgMatSize += s.size();
				if (s.size() > maxMatSize) {
					maxMatSize = s.size();
				}
			}
			System.out.print("materialization sizes: " + (avgMatSize / usr.queryAnswers.size()) + " (avg), "
					+ maxMatSize + " (max) facts");

			// compute average runtime
			avgCpuTime = avgCpuTime / REPETITIONS;
			System.out.println("");
			System.out.println("average cpu time: " + avgCpuTime + " seconds");
			System.out.println("");

			// get measured values from statistics
			String measures = avgCpuTime + "," + usr.statistics.appliedRules.get("del") + ","
					+ (TEST_ALGO == "dred" ? usr.statistics.appliedRules.get("red")
							: (usr.statistics.appliedRules.get("bwd") + "," + usr.statistics.appliedRules.get("fwd")))
					+ "," + usr.statistics.appliedRules.get("ins") + "," + usr.statistics.markedFacts.get("ex") + ","
					+ usr.statistics.markedFacts.get("im");

			// write statistics to file
			writer.println(measures);

			writer.close();

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
