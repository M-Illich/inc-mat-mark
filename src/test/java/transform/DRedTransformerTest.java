package transform;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import data.Atom;
import data.Constraint;
import data.Rule;
import prolog.PrologTest;

public class DRedTransformerTest {

	@Test
	public void testCreateCHRProgram() {
		List<Rule> rules = new LinkedList<>();

		rules.add(new Rule("p(X,Y) :- e(X,Y)."));
		rules.add(new Rule("p(X,Z) :- e(X,Y), p(Y,Z)."));

		DRedTransformer dt = new DRedTransformer(rules);

		String fileNoMark = dt.createCHRProgram("ep", false);
		String fileMark = dt.createCHRProgram("ep", true);

		new PrologTest().testProlog(fileNoMark, fileMark, "src/test/resources/edge_path.pl",
				"src/test/resources/updates_ep");

		rules = new LinkedList<>();
		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(X1,Y1,Z1)"), new Atom("nextInWay(X2,Y2,Z2)")),
				List.of(new Constraint("Z1 \\== Z2"), new Constraint("(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2)"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"),
//				List.of(new Atom("nextInWay(X,_,Z1)"), new Atom("nextInWay(_,X,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"),
//				List.of(new Atom("nextInWay(_,X,Z1)"), new Atom("nextInWay(X,_,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"),
//				List.of(new Atom("nextInWay(_,X,Z1)"), new Atom("nextInWay(_,X,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
		rules.add(
				new Rule(new Atom("connection(X,Z)"), List.of(new Atom("connection(X,Y)"), new Atom("connection(Y,Z)")),
						List.of(new Constraint("X \\== Y"))));

		dt = new DRedTransformer(rules);

		fileNoMark = dt.createCHRProgram("test", false);
		fileMark = dt.createCHRProgram("test", true);

		new PrologTest().testProlog(fileNoMark, fileMark, "src/main/prolog/materialize_ways.pl",
				"src/test/resources/updates_ways");

	}

	@Test
	public void testCreateDeleteRule() {
		Rule rule = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "phase(1), fact([e, X, Y],O1,M1,_), fact([p, Y, Z],O2,M2,_) \\ fact([p, X, Z],add,_,U) <=> X < Y, member(del,[O1,O2]) | check_pos_mark([(e,O1,M1),(p,O2,M2)],M), fact([p, X, Z],del,M,U), applied_rules(1,del).";
		String exp2 = "phase(1), fact([e, X, Y],O1,_), fact([p, Y, Z],O2,_) \\ fact([p, X, Z],add,U) <=> X < Y, member(del,[O1,O2]) | fact([p, X, Z],del,U), applied_rules(1,del).";

		DRedTransformer dt = new DRedTransformer(List.of(rule));

		assertEquals(exp1, dt.createDeleteRule(rule, true));
		assertEquals(exp2, dt.createDeleteRule(rule, false));
	}

	@Test
	public void testCreateRederiveRule() {
		Rule rule = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "phase(2), fact([e, X, Y],add,M1,_), fact([p, Y, Z],add,M2,_) \\ fact([p, X, Z],del,_,U) <=> X < Y, true | check_neg_mark([M1,M2],M), fact([p, X, Z],add,M,U), applied_rules(1,red).";
		String exp2 = "phase(2), fact([e, X, Y],add,_), fact([p, Y, Z],add,_) \\ fact([p, X, Z],del,U) <=> X < Y, true | fact([p, X, Z],add,U), applied_rules(1,red).";

		DRedTransformer dt = new DRedTransformer(List.of(rule));

		assertEquals(exp1, dt.createRederiveRule(rule, true));
		assertEquals(exp2, dt.createRederiveRule(rule, false));
	}
	
	@Test
	public void testCreateInsertRule() {
		Rule rule = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "phase(5), fact([e, X, Y],add,M1,U1), fact([p, Y, Z],add,M2,U2) ==> X < Y, member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact([p, X, Z],add,M,U), applied_rules(1,ins).";
		String exp2 = "phase(5), fact([e, X, Y],add,U1), fact([p, Y, Z],add,U2) ==> X < Y, member(U,[U1,U2]) | fact([p, X, Z],add,U), applied_rules(1,ins).";

		DRedTransformer dt = new DRedTransformer(List.of(rule));
		
		assertEquals(exp1, dt.createInsertRule(rule, true));
		assertEquals(exp2, dt.createInsertRule(rule, false));
	}

}
