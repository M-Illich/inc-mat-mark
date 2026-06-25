package eval;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

public class Statistics {

	/**
	 * number of applied rules for each DRed phase
	 */
	public HashMap<String, String> appliedRules;

	/**
	 * number of marked facts for each type
	 */
	public HashMap<String, String> markedFacts;

	/**
	 * measured execution time needed to complete processing of update stream
	 */
	public float executionTime;
	
	/**
	 * measured processing time [milliseconds] for each update
	 */
	public List<Long> updateTimes;

	/**
	 * measured CPU time needed to complete processing of update stream
	 */
	float cpuTime;

	public Statistics() {
		appliedRules = new HashMap<>();
		markedFacts = new HashMap<>();
		executionTime = 0;
		updateTimes = new LinkedList<>();
	}

	public void integrateData(Collection<String> data) {
		for (String string : data) {
			integrateData(string);
		}
	}

	public void integrateData(String data) {
		// check for applied rules
		if (data.startsWith("applied_rules")) {
			// format = applied_rules(red,[13,8,42,...])
			appliedRules.putIfAbsent(data.substring(14,17), data.substring(18,data.length()-1));
		}
		// check for marked facts
		else if (data.startsWith("marked_facts")) {
			// format = marked_facts(negEx,[5,0,21,...])
			markedFacts.putIfAbsent(data.substring(13,18), data.substring(19,data.length()-1));
		}
		// check for runtime
		else if (data.startsWith("%")) {
			// format = % 252,760,468 inferences, 22.625 CPU in 47.675 seconds
			// extract CPU time
			cpuTime = Float.parseFloat(data.substring(data.indexOf("s, ") + 3, data.indexOf(" CPU")));
			// extract execution time
			executionTime = Float.parseFloat(data.substring(data.indexOf("in ") + 3, data.indexOf(" sec")));

		}

	}

}
