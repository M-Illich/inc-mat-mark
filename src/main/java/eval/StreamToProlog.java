package eval;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import data.Fact;

public class StreamToProlog {

	/**
	 * Use command shell to execute the specified SWI-Prolog file, which
	 * communicates over the provided local port
	 * 
	 * @param localPort {@code int} local port used by server for update stream
	 * @param file      {@code String} name of SWI-Prolog file stored in
	 *                  {@code src/main/resources}
	 * @return {@link Process} object for executed command
	 */
	public Process callProlog(int localPort, String file) {

		// prolog goal to initialize process, connect to specified local port, and
		// measure runtime
		String goal = "time(init(localhost:" + localPort + "))";

		// call SWI-Prolog for specified file and goal
		String[] command = { "swipl", "--stack-limit=4G", "-g", goal, "-t", "halt", "src/main/prolog/" + file };
		ProcessBuilder pb = new ProcessBuilder(command);

		Process process = null;
		try {
			process = pb.start();
		} catch (IOException e) {
			e.printStackTrace();
		}

		return process;

	}

	/**
	 * Read answers (materialized dataset) for each update in stream.
	 * 
	 * @param in            {@link BufferedReader} providing answers as stream
	 * @param printAnswers  {@code boolean} stating if answers are printed to
	 *                      standard output
	 * @param printUpdateNr {@code boolean} stating if number of finished updates is
	 *                      printed to standard output during processing
	 * @return a list of sets of facts where the first set contains the answers to
	 *         the first update, the second set the answers to the second update ...
	 */
	public List<Set<Fact>> readAnswers(BufferedReader in, boolean printAnswers, boolean printUpdateNr) {

		List<Set<Fact>> answers = new LinkedList<>();
		HashSet<Fact> facts = new HashSet<>();

		String line;
		int count = 1;

		// show which update is currently processed as alternative to printing answers
		if (printUpdateNr && !printAnswers) {
			System.out.print("finished update: ");
		}

		try {
			while ((line = in.readLine()) != null) {
				// add fact to set
				if (line.startsWith("[")) {
					facts.add(new Fact(line));
				}
				// collect answers for next update
				else if (line.isBlank()) {
					answers.add(facts);
					facts = new HashSet<>();
					// show which update is processed next
					if (printUpdateNr && !printAnswers) {
						System.out.print(count + " ");
						count++;
					}
				}

				if (printAnswers) {
					System.out.println(line);
				}

			}
		} catch (Exception e) {
			e.printStackTrace();
		}

		if (printAnswers || printUpdateNr) {
			System.out.println("");
		}

		return answers;

	}

	/**
	 * Read lines from provided input stream until {@code null} occurs
	 * 
	 * @param in    {@link BufferedReader} for input stream
	 * @param print {@code boolean} stating if read lines are printed to standard
	 *              output
	 */
	public List<String> readOutput(BufferedReader in, boolean print) {
		List<String> lines = new LinkedList<>();

		String line;
		try {
			while ((line = in.readLine()) != null) {
				lines.add(line);
				if (print) {
					System.out.println(line);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

		return lines;
	}

}
