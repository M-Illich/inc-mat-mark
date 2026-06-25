package transform;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import data.Atom;
import data.Rule;

public class RuleReaderTest {
	
	@Test
	public void testConstructor() {
		File file = new File("src/test/resources/rules.txt");		
		RuleReader rr = new RuleReader(file);
		
		Atom h1 = new Atom("h(?x,?y)");
		List<Atom> b1 = new LinkedList<>();
		b1.add(new Atom("b(?x,?y)"));		
		Rule r1 = new Rule(h1, b1);
		
		Atom h2 = new Atom("p[X,Y]");
		List<Atom> b2 = new LinkedList<>();
		b2.add(new Atom("q[X]"));		
		b2.add(new Atom("r[Y]"));		
		Rule r2 = new Rule(h2, b2);
		
		assertEquals(2, rr.rules.size());
		assertEquals(r1.head, rr.rules.get(0).head);
		assertEquals(r1.body, rr.rules.get(0).body);
		assertEquals(r2.head, rr.rules.get(1).head);
		assertEquals(r2.body, rr.rules.get(1).body);
		
	}

}
