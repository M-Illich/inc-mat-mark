package transform;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import data.Atom;
import data.Constraint;
import data.Rule;
import prolog.PrologTest;

public class DRedTransformerTest {

	DRedTransformer dt = new DRedTransformer();

	@Test
	public void testCreateCHRProgram() {
		List<Rule> rules = new LinkedList<>();
		rules.add(new Rule("p(X,Y) :- e(X,Y)."));
		rules.add(new Rule("p(X,Z) :- e(X,Y), p(Y,Z)."));

		String fileNoMark = dt.createCHRProgram(rules, "ep", false);
		String fileMark = dt.createCHRProgram(rules, "ep", true);

		new PrologTest().testProlog(fileNoMark, fileMark, "src/test/resources/edge_path.pl",
				"src/test/resources/updates_ep");

//		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(X,_,Z1)"), new Atom("nextInWay(X,_,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(X,_,Z1)"), new Atom("nextInWay(_,X,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(_,X,Z1)"), new Atom("nextInWay(X,_,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(_,X,Z1)"), new Atom("nextInWay(_,X,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
//		rules.add(new Rule(new Atom("connection(X,Z)"), List.of(new Atom("connection(X,Y)"), new Atom("connection(Y,Z)")),
//				List.of(new Constraint("X \\== Y"))));
//				
//		String fileNoMark = dt.createCHRProgram(rules, "test", false);
//		String fileMark = dt.createCHRProgram(rules, "test", true);
//		
//		new PrologTest().testProlog(fileNoMark, fileMark, "src/main/prolog/materialize_ways.pl", "src/test/resources/updates_ways");

	}

	@Test
	public void testGetExplicitPredicates() {
		List<Rule> rules = new LinkedList<>();
		rules.add(new Rule("p(X) :- e1(X)."));
		rules.add(new Rule("q(X) :- p(X)."));
		rules.add(new Rule("r(X) :- e2(X)."));

		List<String> predicates = dt.getExplicitPredicates(rules);
		assertEquals(2, predicates.size());
		assertTrue(predicates.contains("e1"));
		assertTrue(predicates.contains("e2"));

	}

	@Test
	public void testCreateDeleteRule() {
		Rule r = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "phase(1), fact([e, X, Y],O1,M1,_), fact([p, Y, Z],O2,M2,_) \\ fact([p, X, Z],add,_,U) <=> X < Y, member(del,[O1,O2]) | check_pos_mark([(e,O1,M1),(p,O2,M2)],M), fact([p, X, Z],del,M,U), applied_rules(1,del).";
		String exp2 = "phase(1), fact([e, X, Y],O1,_), fact([p, Y, Z],O2,_) \\ fact([p, X, Z],add,U) <=> X < Y, member(del,[O1,O2]) | fact([p, X, Z],del,U), applied_rules(1,del).";

		assertEquals(exp1, dt.createDeleteRule(r, true));
		assertEquals(exp2, dt.createDeleteRule(r, false));
	}

	@Test
	public void testCreateRederiveRule() {
		Rule r = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "phase(2), fact([e, X, Y],add,M1,_), fact([p, Y, Z],add,M2,_) \\ fact([p, X, Z],del,_,U) <=> X < Y, true | check_neg_mark([M1,M2],M), fact([p, X, Z],add,M,U), applied_rules(1,red).";
		String exp2 = "phase(2), fact([e, X, Y],add,_), fact([p, Y, Z],add,_) \\ fact([p, X, Z],del,U) <=> X < Y, true | fact([p, X, Z],add,U), applied_rules(1,red).";

		assertEquals(exp1, dt.createRederiveRule(r, true));
		assertEquals(exp2, dt.createRederiveRule(r, false));
	}

	@Test
	public void testCreateInsertRule() {
		Rule r = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "phase(5), fact([e, X, Y],add,M1,U1), fact([p, Y, Z],add,M2,U2) ==> X < Y, member(U,[U1,U2]) | check_neg_mark([M1,M2],M), fact([p, X, Z],add,M,U), applied_rules(1,ins).";
		String exp2 = "phase(5), fact([e, X, Y],add,U1), fact([p, Y, Z],add,U2) ==> X < Y, member(U,[U1,U2]) | fact([p, X, Z],add,U), applied_rules(1,ins).";

		assertEquals(exp1, dt.createInsertRule(r, true));
		assertEquals(exp2, dt.createInsertRule(r, false));
	}

}
