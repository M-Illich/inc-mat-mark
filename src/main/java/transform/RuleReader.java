package transform;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import data.Rule;

/**
 * Read Datalog rules in the form of {@code head :- body1, body2, ..., .} from a
 * file and convert them into {@link Rule} objects. 
 * Note: We assume that rules do not contain any constraints, like comparisons (=, <, ...)
 */
public class RuleReader {

	public File srcFile;
	public List<Rule> rules;

	/**
	 * store how many rules exist (value) with certain number of body atoms (key)
	 */
	public Map<Integer, Integer> ruleSizes;

	public RuleReader(File fileName) {
		srcFile = fileName;
		ruleSizes = new HashMap<>();
		rules = readRules(srcFile);
	}

	private List<Rule> readRules(File file) {

		List<Rule> ruleList = new LinkedList<>();

		BufferedReader reader;
		try {
			reader = new BufferedReader(new FileReader(file));
			String line;
			String rule = "";

			while ((line = reader.readLine()) != null) {
				if (!(line.startsWith("@") || line.startsWith("#") || line.startsWith("%")
						|| line.startsWith("PREFIX"))) {
					// write whole rule into single String
					rule += line;
					// line contains end of rule
					if (line.trim().endsWith(".")) {
						// transform String into Rule object
						Rule r = new Rule(rule);
						ruleList.add(r);
						// reset String for next rule
						rule = "";
						// memorize body size of rule
						ruleSizes.putIfAbsent(r.body.size(), 0);
						ruleSizes.compute(r.body.size(), (_, v) -> v + 1);

					}
				}
			}

			reader.close();

		} catch (Exception e) {
			e.printStackTrace();
		}

		return ruleList;
	}

}
