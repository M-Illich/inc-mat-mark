package transform;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import data.Atom;
import data.Constraint;
import data.Rule;
import prolog.PrologTest;

public class BFTransformerTest {

	@Test
	public void testCreateCHRProgram() {
		List<Rule> rules = new LinkedList<>();
		
		rules.add(new Rule("p(X,Y) :- e(X,Y)."));
		rules.add(new Rule("p(X,Z) :- e(X,Y), p(Y,Z)."));

		BFTransformer bfTr = new BFTransformer(rules);

		String fileNoMark = bfTr.createCHRProgram("ep", false);
		String fileMark = bfTr.createCHRProgram("ep", true);

		new PrologTest().testProlog(fileNoMark, fileMark, "src/test/resources/edge_path.pl",
				"src/test/resources/updates_ep");

		rules = new LinkedList<>();
		
		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(X1,Y1,Z1)"), new Atom("nextInWay(X2,Y2,Z2)")),
				List.of(new Constraint("Z1 \\== Z2"), new Constraint("(X1 == X2 ; X1 == Y2 ; Y1 == X2 ; Y1 == Y2)"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(X,_,Z1)"), new Atom("nextInWay(_,X,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(_,X,Z1)"), new Atom("nextInWay(X,_,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
//		rules.add(new Rule(new Atom("connection(Z1,Z2)"), List.of(new Atom("nextInWay(_,X,Z1)"), new Atom("nextInWay(_,X,Z2)")),
//				List.of(new Constraint("Z1 \\== Z2"))));
		rules.add(new Rule(new Atom("connection(X,Z)"), List.of(new Atom("connection(X,Y)"), new Atom("connection(Y,Z)")),
				List.of(new Constraint("X \\== Y"))));
				
		bfTr = new BFTransformer(rules);
		
		fileNoMark = bfTr.createCHRProgram("test", false);
		fileMark = bfTr.createCHRProgram("test", true);
		
		new PrologTest().testProlog(fileNoMark, fileMark, "src/main/prolog/materialize_ways.pl", "src/test/resources/updates_ways");

	}

	@Test
	public void testCreateDeleteRule() {
		Rule rule = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "phase(1), fact([e, X, Y],O1,_,_), fact([p, Y, Z],O2,_,_) \\ fact([p, X, Z],add,_,U) <=> X < Y, member(del,[O1,O2]) | fact([p, X, Z],chk,_,U), applied_rules(1,del).";
		String exp2 = "phase(1), fact([e, X, Y],O1,_), fact([p, Y, Z],O2,_) \\ fact([p, X, Z],add,U) <=> X < Y, member(del,[O1,O2]) | fact([p, X, Z],chk,U), applied_rules(1,del).";

		BFTransformer bfTr = new BFTransformer(List.of(rule));

		assertEquals(exp1, bfTr.createDeleteRule(rule, true));
		assertEquals(exp2, bfTr.createDeleteRule(rule, false));
	}

	@Test
	public void testCreateForwardRule() {
		Rule rule = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "fact([e, X, Y],prv,M1,_), fact([p, Y, Z],prv,M2,_) \\ fact([p, X, Z],O,_,U) <=> X < Y, member(O,[chk,chk1]) | check_neg_mark([(e,M1),(p,M2)],M), fact([p, X, Z],prv,M,U), applied_rules(1,fwd).";
		String exp2 = "fact([e, X, Y],prv,_), fact([p, Y, Z],prv,_) \\ fact([p, X, Z],O,U) <=> X < Y, member(O,[chk,chk1]) | fact([p, X, Z],prv,U), applied_rules(1,fwd).";

		BFTransformer bfTr = new BFTransformer(List.of(rule));

		assertEquals(exp1, bfTr.createForwardRule(rule, true));
		assertEquals(exp2, bfTr.createForwardRule(rule, false));
	}

	@Test
	public void testCreateBackwardRule() {
		Rule rule = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "fact([p, X, Z],chk1,_,_), fact([e, X, Y],O1,M1,U1), fact([p, Y, Z],O2,M2,U2) ==> X < Y, \\+member(del,[O1,O2]) | fact([e, X, Y],chk1,M1,U1), fact([p, Y, Z],chk1,M2,U2), applied_rules(1,bwd).";
		String exp2 = "fact([p, X, Z],chk1,_), fact([e, X, Y],O1,U1), fact([p, Y, Z],O2,U2) ==> X < Y, \\+member(del,[O1,O2]) | fact([e, X, Y],chk1,U1), fact([p, Y, Z],chk1,U2), applied_rules(1,bwd).";

		BFTransformer bfTr = new BFTransformer(List.of(rule));

		assertEquals(exp1, bfTr.createBackwardRule(rule, true));
		assertEquals(exp2, bfTr.createBackwardRule(rule, false));
	}
	
	@Test
	public void testCreateInsertRule() {
		Rule rule = new Rule(new Atom("p(X,Z)"), List.of(new Atom("e(X,Y)"), new Atom("p(Y,Z)")),
				List.of(new Constraint("X < Y")));
		String exp1 = "phase(5), fact([e, X, Y],add,M1,U1), fact([p, Y, Z],add,M2,U2) ==> X < Y, member(U,[U1,U2]) | check_neg_mark([(e,M1),(p,M2)],M), fact([p, X, Z],add,M,U), applied_rules(1,ins).";
		String exp2 = "phase(5), fact([e, X, Y],add,U1), fact([p, Y, Z],add,U2) ==> X < Y, member(U,[U1,U2]) | fact([p, X, Z],add,U), applied_rules(1,ins).";

		BFTransformer dt = new BFTransformer(List.of(rule));
		
		assertEquals(exp1, dt.createInsertRule(rule, true));
		assertEquals(exp2, dt.createInsertRule(rule, false));
	}

}
