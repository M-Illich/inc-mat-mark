package eval;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import data.Fact;
import data.Update;

public class UpdateStreamRun extends StreamToProlog {

	/**
	 * name of file containing SWI-Prolog code to be executed
	 */
	String algorithmFile;

	/**
	 * list of answer sets for each stated query
	 */
	public List<Set<Fact>> queryAnswers;

	/**
	 * list of datasets created by sequence of updates
	 */
	public List<Set<Fact>> datasets;

	/**
	 * name of folder where each stream update is stored as file
	 */
	public String updateFolder;

	/**
	 * list of updates to be processed
	 */
	public List<Update> updateList;

	/**
	 * Process a stream of updates that adapt a graph by adding and deleting edges.
	 * The updates are created randomly based on the caller's attributes. The Prolog
	 * code in {@code file} incrementally maintains the materialization of the
	 * graph.
	 * 
	 * @param printUpdates         {@code boolean} states if updates and their
	 *                             overlap with direct predecessor are printed to
	 *                             standard output
	 * 
	 * @param printMaterialization {@code boolean} states if materialization
	 *                             obtained after each update is printed to standard
	 *                             output
	 * 
	 * @param printStatistics      {@code boolean} states if number of applied rules
	 *                             and runtime is printed to standard output
	 * 
	 */
	public void execute(boolean printUpdates, boolean printMaterialization, boolean printStatistics) {

		try {
			// open server
			ServerSocket serverSocket = new ServerSocket(0);

			// execute prolog file
			Process prologCall = callProlog(serverSocket.getLocalPort(), algorithmFile);

			// accept connection from prolog file
			Socket clientSocket = serverSocket.accept();

			PrintWriter out = new PrintWriter(clientSocket.getOutputStream(), true);
			BufferedReader in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));

			// create stream of random updates each followed by a query
			datasets = createUpdateStream(out, printUpdates);

			// read answers for each query
			queryAnswers = readAnswers(in, printMaterialization, true);

			in.close();
			out.close();
			clientSocket.close();
			serverSocket.close();

			// read output from executed commands
			BufferedReader cmdReader = new BufferedReader(new InputStreamReader(prologCall.getInputStream()));
			if (printStatistics) {
				System.out.println("-- command output --");
			}
			statistics.integrateData(readOutput(cmdReader, printStatistics));
			cmdReader.close();
			// get additional messages, like execution time if available
			BufferedReader cmdError = new BufferedReader(new InputStreamReader(prologCall.getErrorStream()));
			statistics.integrateData(readOutput(cmdError, printStatistics));
			cmdError.close();

		} catch (IOException e) {
			e.printStackTrace();
		}

	}

	/**
	 * 
	 * @param algorithmFile {@code String} name of file containing SWI-Prolog code
	 *                      to be executed
	 * @param updateFolder  {@code String} name of folder where each stream update
	 *                      is stored as file
	 */
	public UpdateStreamRun(String algorithmFile, String updateFolder) {
		this.algorithmFile = algorithmFile;
		this.updateFolder = updateFolder;
		this.updateList = loadUpdates(updateFolder);
		this.statistics = new Statistics();

	}

	/**
	 * 
	 * @param algorithmFile {@code String} name of file containing SWI-Prolog code
	 *                      to be executed
	 * @param updateList    {@link List} of {@link Update} objects that will be
	 *                      processed
	 */
	public UpdateStreamRun(String file, List<Update> updateList) {
		this.algorithmFile = file;
		this.updateList = updateList;
		this.statistics = new Statistics();

	}

	/**
	 * Create a stream based on the predefined updates in {@code updateFolder}. A
	 * query asking for every fact is stated after each update.
	 * 
	 * 
	 * @param out          {@link PrintWriter} to write updates to stream
	 * @param printUpdates {@code boolean} states if updates and their overlap with
	 *                     direct predecessor are printed to standard output
	 * @return a list of sets of facts representing the sequence of datasets created
	 *         by the update stream
	 */
	List<Set<Fact>> createUpdateStream(PrintWriter out, boolean printUpdates) {

		List<Set<Fact>> datasets = new LinkedList<>();
		Set<Fact> dataset = new HashSet<>();

		// store previous update to compute overlap
		Update pre = new Update(new HashSet<>(), new HashSet<>());
		HashSet<Fact> replaced_del = new HashSet<>();
		HashSet<Fact> replaced_add = new HashSet<>();
		Update u;

		// collect statistics about number of changed facts
		int maxAdd = 0;
		int maxDel = 0;
		int sumAdd = 0;
		int sumDel = 0;
		int noNull = 0;

		// go through updates
		for (int i = 1; i <= updateList.size(); i++) {
			u = updateList.get(i - 1);

			// store updated explicit dataset
			dataset.addAll(u.added);
			dataset.removeAll(u.deleted);
			datasets.add(new HashSet<Fact>(dataset));

			if (printUpdates) {
				replaced_del.clear();
				replaced_add.clear();
				// determine overlap with previous update
				for (Fact fact : u.added) {
					if (pre.deleted.contains(fact)) {
						replaced_del.add(fact);
					}
				}
				for (Fact fact : u.deleted) {
					if (pre.added.contains(fact)) {
						replaced_add.add(fact);
					}
				}
				// store current update for next overlap
				pre = u;

				// print update
				System.out.println("");
				String[] us = u.toString().split("]:");
				System.out.println(i + ": " + us[0] + "]");
				System.out.println("    " + us[1]);
				// print size of overlap with previous update
				System.out.println(" Overlap with previous: replaced del = " + replaced_del.size()
						+ " - replaced add = " + replaced_add.size());
			}

			// write update to stream (if not empty)
			if (!(u.added.isEmpty() && u.deleted.isEmpty())) {
				out.println(u.added.toString());
				out.println(u.deleted.toString());

				// collect statistics about number of changed facts
				noNull++;
				sumAdd += u.added.size();
				sumDel += u.deleted.size();
				if (u.added.size() > maxAdd) {
					maxAdd = u.added.size();
				}
				if (u.deleted.size() > maxDel) {
					maxDel = u.deleted.size();
				}

			}

//			System.out.println(i + " add: " + u.added.size() + "  --  del: " + u.deleted.size());

			if (printUpdates) {
				// there is a query directly after each update (asking for every fact)
				System.out.println("query " + i);
			}
		}

		// indicate end of stream
		out.println("[]");
		out.println("[]");

		System.out.println("maxAdd: " + maxAdd + "  --  maxDel: " + maxDel + "  --  avgAdd: " + (sumAdd / noNull)
				+ "  --  avgDel: " + (sumDel / noNull) + "  --  updates: " + noNull);

		return datasets;

	}

	/**
	 * Create an update based on a file that explicitly states which facts have to
	 * be added and deleted.
	 * 
	 * @param file {@link File} containing in each line either
	 *             {@code add(p(a1, a2))} or {@code delete(p(a1, a2))} for any
	 *             Datalog fact {@code p(a2, a2)}
	 * @return {@link Update} with {@code add} and {@code delete} sets based on file
	 */
	Update readUpdate(File file) {

		Set<Fact> addFacts = new HashSet<>();
		Set<Fact> deleteFacts = new HashSet<>();

		BufferedReader reader;
		try {
			reader = new BufferedReader(new FileReader(file));
			String line = reader.readLine();

			while (line != null) {
				if (line.startsWith("add(")) {
					addFacts.add(new Fact(line.substring(4, line.length() - 2)));
				} else if (line.startsWith("delete(")) {
					deleteFacts.add(new Fact(line.substring(7, line.length() - 2)));
				}
				line = reader.readLine();
			}

			reader.close();

		} catch (Exception e) {
			e.printStackTrace();
		}

		return new Update(addFacts, deleteFacts);

	}

	/**
	 * Load updates stored as files in given folder, where each file defines updates
	 * based on {@code add(...).} and {@code delete(...).} statements in each line.
	 * 
	 * @param updateFolder {@code String} name of folder where each stream update is
	 *                     stored as file
	 * @return {@link List} of {@link Update} objects
	 */
	public List<Update> loadUpdates(String updateFolder) {
		List<Update> updates = new LinkedList<>();
		// load updates from files
		File[] updateFiles = new File(updateFolder).listFiles();
		for (int i = 1; i <= updateFiles.length; i++) {
			updates.add(readUpdate(updateFiles[i - 1]));
		}

		return updates;
	}

}