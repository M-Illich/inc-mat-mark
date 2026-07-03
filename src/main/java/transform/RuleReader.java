package transform;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.LinkedList;
import java.util.List;

import data.Rule;

/**
 * read Datalog rules in the form of {@code head :- body1, body2, ..., .} from a
 * file and convert them into {@link Rule} objects
 */
public class RuleReader {

	public File srcFile;
	List<Rule> rules;

	public RuleReader(File fileName) {
		srcFile = fileName;
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
				if (!(line.startsWith("@") || line.startsWith("#") || line.startsWith("%") || line.startsWith("PREFIX"))) {
					// write whole rule into single String
					rule += line;
					// line contains end of rule
					if (line.trim().endsWith(".")) {
						// transform String into Rule object
						ruleList.add(new Rule(rule));
						// reset String for next rule
						rule = "";
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
