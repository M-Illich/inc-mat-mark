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
 * reflects the Delete/Rederive algorithm.
 */
public class DRedTransformer extends Transformer {

	/**
	 * 
	 * @param ruleSet {@link List} of {@link Rule} objects representing (positive)
	 *                Datalog rules
	 */
	public DRedTransformer(List<Rule> ruleSet) {
		this.ruleSet = ruleSet;
		this.explicitPredicates = getExplicitPredicates(ruleSet);
	}

	
	public String createCHRProgram(String name, boolean withMark) {

		// initialize CHR file
		String fileName = "src/main/prolog/dred/dred_" + name + (withMark ? "" : "_no") + "_mark.pl";
		File chrFile = new File(fileName);
		try {
			// initialize CHR program
			BufferedWriter writer = new BufferedWriter(new FileWriter(chrFile));
			BufferedReader reader = new BufferedReader(new FileReader(
					new File("src/main/resources/chr/dred/dred_" + (withMark ? "" : "no_") + "mark_0.pl")));
			String line;
			while ((line = reader.readLine()) != null) {
				writer.write(line);
				writer.newLine();
			}
			reader.close();

			// add deletion rules
			for (Rule rule : ruleSet) {
				writer.write(createDeleteRule(rule, withMark));
				writer.newLine();
			}
			writer.write("phase(1) <=> phase(2).");
			writer.newLine();
			writer.write("");
			writer.newLine();

			// add rederivation rules
			writer.write("% -- re-add deleted facts that still have some alternative derivation --");
			writer.newLine();
			for (Rule rule : ruleSet) {
				writer.write(createRederiveRule(rule, withMark));
				writer.newLine();
			}
			writer.write("");
			writer.newLine();

			// add part between rederivation and insertion phase
			reader = new BufferedReader(new FileReader(
					new File("src/main/resources/chr/dred/dred_" + (withMark ? "" : "no_") + "mark_1.pl")));
			while ((line = reader.readLine()) != null) {
				writer.write(line);
				writer.newLine();
			}
			reader.close();

			// add insertion rules
			for (Rule rule : ruleSet) {
				writer.write(createInsertRule(rule, withMark));
				writer.newLine();
			}

			// end CHR file
			reader = new BufferedReader(new FileReader(
					new File("src/main/resources/chr/dred/dred_" + (withMark ? "" : "no_") + "mark_2.pl")));
			while ((line = reader.readLine()) != null) {
				writer.write(line);
				writer.newLine();
			}

			// for marking, indicate which predicates belong to explicit facts
			if (withMark) {
				for (String predicate : explicitPredicates) {
					writer.write("explicit(" + predicate + ").");
					writer.newLine();
				}
			}

			reader.close();
			writer.close();

		} catch (Exception e) {
			e.printStackTrace();
		}

		return fileName;

	}

	/**
	 * Create the CHR rule for the overdeletion phase of DRed based on the given
	 * Datalog rule.
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
			chr += ", fact(" + rule.body.get(i).toString() + ",O" + (i + 1) + (withMark ? ",M" + (i + 1) : "") + ",_)";
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

		if (rule.body.size() == 1) {
			// directly use marking variable of body atom for head
			chr += "fact(" + rule.head.toString() + ",del" + (withMark ? ",M1" : "") + ",U), applied_rules(1,del).";
		} else {
			// add marking if needed
			if (withMark) {
				chr += "check_pos_mark([(" + rule.body.get(0).predicate + ",O1,M1)";
				for (int i = 1; i < rule.body.size(); i++) {
					chr += ",(" + rule.body.get(i).predicate + ",O" + (i + 1) + ",M" + (i + 1) + ")";
				}
				chr += "],M), ";
			}
			// add new head
			chr += "fact(" + rule.head.toString() + ",del" + (withMark ? ",M" : "") + ",U), applied_rules(1,del).";
		}

		return chr;
	}

	/**
	 * Create the CHR rule for the rederivation phase of DRed based on the given
	 * Datalog rule.
	 * 
	 * @param rule     A {@link Rule}
	 * @param withMark States whether or not the rule should include fact marking
	 * @return A {@code String} with the transformed CHR rule
	 */
	public String createRederiveRule(Rule rule, boolean withMark) {

		// initialize transformed rule
		String chr = "phase(2)";
		// add transformed body atoms
		for (int i = 0; i < rule.body.size(); i++) {
			chr += ", fact(" + rule.body.get(i).toString() + ",add" + (withMark ? ",M" + (i + 1) : "") + ",_)";
		}
		// add changing head atom
		chr += " \\ fact(" + rule.head.toString() + ",del" + (withMark ? ",_" : "") + ",U) <=> ";
		// add guard conditions
		for (Constraint con : rule.constraints) {
			chr += con.toString() + ", ";
		}
		chr += "true | ";

		if (rule.body.size() == 1) {
			// directly use marking variable of body atom for head
			chr += "fact(" + rule.head.toString() + ",add" + (withMark ? ",M1" : "") + ",U), applied_rules(1,red).";
		} else {
			// add marking if needed
			if (withMark) {
				chr += "check_neg_mark([M1";
				for (int i = 1; i < rule.body.size(); i++) {
					chr += ",M" + (i + 1);
				}
				chr += "],M), ";
			}
			// add new head
			chr += "fact(" + rule.head.toString() + ",add" + (withMark ? ",M" : "") + ",U), applied_rules(1,red).";
		}

		return chr;
	}

	/**
	 * Create the CHR rule for the insertion phase of algorithm based on the given
	 * Datalog rule.
	 * 
	 * @param rule     A {@link Rule}
	 * @param withMark {@code boolean} States whether or not the rule should include
	 *                 fact marking
	 * @return A {@code String} with the transformed CHR rule
	 */
	public String createInsertRule(Rule rule, boolean withMark) {

		// initialize transformed rule
		String chr = "phase(5)";
		// add transformed body atoms
		for (int i = 0; i < rule.body.size(); i++) {
			chr += ", fact(" + rule.body.get(i).toString() + ",add" + (withMark ? ",M" + (i + 1) : "") + ",U" + (i + 1)
					+ ")";
		}
		// add guard conditions
		chr += " ==> ";
		for (Constraint con : rule.constraints) {
			chr += con.toString() + ", ";
		}
		chr += "member(U,[U1";
		for (int i = 1; i < rule.body.size(); i++) {
			chr += ",U" + (i + 1);
		}
		chr += "]) | ";

		if (rule.body.size() == 1) {
			// directly use marking variable of body atom for head
			chr += "fact(" + rule.head.toString() + ",add" + (withMark ? ",M1" : "") + ",U), applied_rules(1,ins).";
		} else {
			// add marking if needed
			if (withMark) {
				chr += "check_neg_mark([M1";
				for (int i = 1; i < rule.body.size(); i++) {
					chr += ",M" + (i + 1);
				}
				chr += "],M), ";
			}
			// add new head
			chr += "fact(" + rule.head.toString() + ",add" + (withMark ? ",M" : "") + ",U), applied_rules(1,ins).";
		}

		return chr;
	}

}
