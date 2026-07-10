package data;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class RuleTest {

	@Test
	public void testConstructor() {
		Rule r = new Rule("head[?X, ?Y] :- body1[?X, b], body2[b, ?Y] .");

		assertEquals(new Atom("head(X,Y)"), r.head);
		assertEquals(2, r.body.size());
		assertEquals(new Atom("body1(X,b)"), r.body.get(0));
		assertEquals(new Atom("body2(b,Y)"), r.body.get(1));
	}

	@Test
	public void testReplaceSingletonVariables() {
		Rule r1 = new Rule("h(X,Y) :- b2(Y,X), b1(X,Z) .");
		Rule rExp = new Rule("h(X,Y) :- b2(Y,X), b1(X,_) .");
		r1.replaceSingletonVariables();
		assertEquals(rExp.toString(), r1.toString());
	}

}
