package transform;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.List;
import data.Constraint;
import data.Rule;

/**
 * Class to transform Datalog rules into an appropriate CHR program that
 * reflects the Backward/Forward algorithm.
 */
public class BFTransformer extends Transformer {

	/**
	 * 
	 * @param ruleSet {@link List} of {@link Rule} objects representing (positive)
	 *                Datalog rules
	 */
	public BFTransformer(List<Rule> ruleSet) {
		this.ruleSet = ruleSet;
		this.explicitPredicates = getExplicitPredicates(ruleSet);
	}

	/**
	 * 
	 * @param ruleset
	 * @param name    {@link String} as name for CHR program
	 * @param mark    {@code boolean} which states whether the algorithm should
	 *                include marking or not
	 * @return {@link String} address of file that contains CHR program
	 */
	public String createCHRProgram(String name, boolean mark) {

		// initialize CHR file
		String fileName = "src/main/prolog/bf/bf_" + name + (mark ? "" : "_no") + "_mark.pl";
		File chrFile = new File(fileName);
		try {
			// initialize CHR program
			BufferedWriter writer = new BufferedWriter(new FileWriter(chrFile));
			BufferedReader reader = new BufferedReader(
					new FileReader(new File("src/main/resources/chr/bf/bf_" + (mark ? "" : "no_") + "mark_0.pl")));
			String line;
			while ((line = reader.readLine()) != null) {
				writer.write(line);
				writer.newLine();
			}
			reader.close();

			// add deletion rules
			for (Rule rule : ruleSet) {
				writer.write(createDeleteRule(rule, mark));
				writer.newLine();
			}

			// load next part
			reader = new BufferedReader(
					new FileReader(new File("src/main/resources/chr/bf/bf_" + (mark ? "" : "no_") + "mark_1.pl")));
			while ((line = reader.readLine()) != null) {
				writer.write(line);
				writer.newLine();
			}
			reader.close();

			// add forward rules
			writer.write("% - forward -");
			writer.newLine();
			for (Rule rule : ruleSet) {
				writer.write(createForwardRule(rule, mark));
				writer.newLine();
			}
			writer.write("");
			writer.newLine();
			writer.write("");
			writer.newLine();

			// add backward rules
			writer.write("% - backward -");
			writer.newLine();
			for (Rule rule : ruleSet) {
				writer.write(createBackwardRule(rule, mark));
				writer.newLine();
			}
			writer.write("");
			writer.newLine();

			// add part before insertion phase
			reader = new BufferedReader(
					new FileReader(new File("src/main/resources/chr/bf/bf_" + (mark ? "" : "no_") + "mark_2.pl")));
			while ((line = reader.readLine()) != null) {
				writer.write(line);
				writer.newLine();
			}
			reader.close();

			// add insertion rules
			for (Rule rule : ruleSet) {
				writer.write(createInsertRule(rule, mark));
				writer.newLine();
			}

			// end CHR file
			reader = new BufferedReader(
					new FileReader(new File("src/main/resources/chr/bf/bf_" + (mark ? "" : "no_") + "mark_3.pl")));
			while ((line = reader.readLine()) != null) {
				writer.write(line);
				writer.newLine();
			}

			// indicate which predicates belong to explicit facts
			for (String predicate : explicitPredicates) {
				writer.write("explicit(" + predicate + ").");
				writer.newLine();

			}

			reader.close();
			writer.close();

		} catch (Exception e) {
			e.printStackTrace();
		}

		return fileName;

	}

	public String createBackwardRule(Rule rule, boolean withMark) {
		// initialize transformed rule with changing head atom
		String chr = "fact(" + rule.head.toString() + ",chk1" + (withMark ? ",_" : "") + ",_)";

		// add changing body atoms
		for (int i = 0; i < rule.body.size(); i++) {
			chr += ", fact(" + rule.body.get(i).toString() + ",O" + (i + 1) + (withMark ? ",M" + (i + 1) : "") + ",U"
					+ (i + 1) + ")";
		}
		chr += " ==> ";

		// add guard conditions
		for (Constraint con : rule.constraints) {
			chr += con.toString() + ", ";
		}
		chr += "\\+member(del,[O1";
		for (int i = 1; i < rule.body.size(); i++) {
			chr += ",O" + (i + 1);
		}
		chr += "]) | ";

		// add transformed body atoms
		for (int i = 0; i < rule.body.size(); i++) {
			chr += "fact(" + rule.body.get(i).toString() + ",chk1" + (withMark ? ",M" + (i + 1) : "") + ",U" + (i + 1)
					+ "), ";
		}
		chr += "applied_rules(1,bwd).";

		return chr;
	}

	public String createForwardRule(Rule rule, boolean withMark) {

		// only compute marking if at least one explicit body fact given
		String markPart = "";
		boolean noExplicit = true;
		if (withMark) {
			for (int i = 0; i < rule.body.size(); i++) {
				if (explicitPredicates.contains(rule.body.get(i).predicate)) {
					noExplicit = false;
					break;
				}
			}
			if (noExplicit) {
				markPart = ",_";
			} else {
				markPart = ",M";
			}
		}

		// initialize transformed rule
		String chr = "fact(" + rule.body.get(0).toString() + ",prv" + markPart + (withMark ? "1" : "") + ",_)";

		// add transformed body atoms
		for (int i = 1; i < rule.body.size(); i++) {
			chr += ", fact(" + rule.body.get(i).toString() + ",prv" + markPart + (withMark ? (i + 1) : "") + ",_)";
		}
		// add changing head atom
		chr += " \\ fact(" + rule.head.toString() + ",O" + (withMark ? ",_" : "") + ",U) <=> ";
		// add guard conditions
		for (Constraint con : rule.constraints) {
			chr += con.toString() + ", ";
		}
		chr += "member(O,[chk,chk1]) | ";

		// only compute marking if at least one explicit body fact given
		if (!noExplicit) {
			chr += "check_neg_mark([(" + rule.body.get(0).predicate + ",M1)";
			for (int i = 1; i < rule.body.size(); i++) {
				chr += ",(" + rule.body.get(i).predicate + ",M" + (i + 1) + ")";
			}
			chr += "],M), ";
		}

		// add new head
		chr += "fact(" + rule.head.toString() + ",prv" + markPart + ",U), applied_rules(1,fwd).";

		return chr;
	}

	/**
	 * Create the CHR rule for the deletion phase of BF based on the given Datalog
	 * rule.
	 * 
	 * @param rule     A {@link Rule}
	 * @param withMark States whether or not the rule should include fact marking
	 * @return A {@code String} with the transformed CHR rule
	 */
	public String createDeleteRule(Rule rule, boolean withMark) {
		// initialize transformed rule
		String chr = "phase(1)";

		// add transformed body atoms
		for (int i = 0; i < rule.body.size(); i++) {
			chr += ", fact(" + rule.body.get(i).toString() + ",O" + (i + 1) + (withMark ? ",_" : "") + ",_)";
		}
		// add changing head atom
		chr += " \\ fact(" + rule.head.toString() + ",add" + (withMark ? ",_" : "") + ",U) <=> ";
		// add guard conditions
		for (Constraint con : rule.constraints) {
			chr += con.toString() + ", ";
		}
		chr += "member(del,[O1";
		for (int i = 1; i < rule.body.size(); i++) {
			chr += ",O" + (i + 1);
		}
		chr += "]) | ";
		// add new head
		chr += "fact(" + rule.head.toString() + ",chk" + (withMark ? ",_" : "") + ",U), applied_rules(1,del).";

		return chr;
	}

}
