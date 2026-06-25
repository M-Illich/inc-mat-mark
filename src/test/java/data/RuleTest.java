package data;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class RuleTest {
	
	@Test
	public void testConstructor() {
		Rule r = new Rule("head[?X, ?Y] :- body1[?X, b], body2[b, ?Y] .");
		
		assertEquals(new Atom("head(XX,XY)"),r.head);
		assertEquals(2, r.body.size());
		assertEquals(new Atom("body1(XX,b)"), r.body.get(0));
		assertEquals(new Atom("body2(b,XY)"), r.body.get(1));
	}

}
