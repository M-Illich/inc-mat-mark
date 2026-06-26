package transform;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import data.Atom;
import data.Constraint;
import data.Rule;

public class TransformerTest {


	@Test
	public void testGetExplicitPredicates() {
		List<Rule> rules = new LinkedList<>();
		rules.add(new Rule("p(X) :- e1(X)."));
		rules.add(new Rule("q(X) :- p(X)."));
		rules.add(new Rule("r(X) :- e2(X)."));
		
		DRedTransformer dt = new DRedTransformer(rules);

		List<String> predicates = dt.getExplicitPredicates(rules);
		assertEquals(2, predicates.size());
		assertTrue(predicates.contains("e1"));
		assertTrue(predicates.contains("e2"));

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
