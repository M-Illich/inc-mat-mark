package eval;

import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import data.Fact;

public class Evaluation {

	/**
	 * number of repeated runs to compute average runtime
	 */
	final static int REPETITIONS = 1; // TODO 5;

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
				if (TEST_ALGO == "dred") {	// TODO "dred/dred_ways_no_mark.pl", 
					filesWays = List.of("dred/dred_ways_mark_new.pl");
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
			// store evaluation results as table in a file
			writer = new PrintWriter("results/results-" + approach + "-" + updatesName + ".csv", "UTF-8");

			// create update stream
			UpdateStreamRun usr = new UpdateStreamRun(file, updateFolder);

			float avgStreamCpuTime = 0;
			List<Long> avgUpdateCpuTimes = new LinkedList<>();
			for (int i = 0; i < REPETITIONS; i++) {
				// process update stream
				usr.execute(false, false, false);
				avgStreamCpuTime += usr.statistics.cpuTime;

				// collect processing time for each update
				if (i == 0) {
					avgUpdateCpuTimes = usr.statistics.updateTimes;
				} else {
					for (int j = 0; j < usr.statistics.updateTimes.size(); j++) {
						avgUpdateCpuTimes.set(j, avgUpdateCpuTimes.get(j) + usr.statistics.updateTimes.get(j));
					}
				}
			}

			// initialize table
			writer.print("updates");
			for (int i = 1; i <= avgUpdateCpuTimes.size(); i++) {
				writer.print("," + i);
			}
			writer.println();
			writer.print("CPU time [ms]");

			// compute average processing time for each update
			for (int i = 0; i < avgUpdateCpuTimes.size(); i++) {
				avgUpdateCpuTimes.set(i, avgUpdateCpuTimes.get(i) / REPETITIONS);
				writer.print("," + avgUpdateCpuTimes.get(i));
			}
			writer.println();
			writer.print("materialization size");

			// get materialization sizes
			int avgMatSize = 0;
			int maxMatSize = 0;
			for (Set<Fact> mat : usr.queryAnswers) {
				avgMatSize += mat.size();
				if (mat.size() > maxMatSize) {
					maxMatSize = mat.size();
				}
				writer.print("," + mat.size());
			}
			writer.println();
			System.out.print("materialization sizes: " + (avgMatSize / usr.queryAnswers.size()) + " (avg), "
					+ maxMatSize + " (max) facts");

			// compute average runtime of whole stream
			avgStreamCpuTime = avgStreamCpuTime / REPETITIONS;
			System.out.println("");
			System.out.println("average cpu time: " + avgStreamCpuTime + " seconds");
			System.out.println("");

			// get measured values from statistics
			usr.statistics.appliedRules
					.forEach((k, v) -> writer.println("applied rules (" + k + ")," + v.substring(1, v.length() - 1).replaceAll(" ", "")));
			usr.statistics.markedFacts
					.forEach((k, v) -> writer.println("marked facts (" + k + ")," + v.substring(1, v.length() - 1).replaceAll(" ", "")));

			writer.close();

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
