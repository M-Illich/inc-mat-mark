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

}
