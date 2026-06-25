package data;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

public class FactTest {

	@Test
	public void testConstructor() {
//		Fact fact =  new Fact("p", List.of("1","2"));
		Fact bracket = new Fact("[p, 1, 2]");
		Fact atom = new Fact("p(1, 2)");	
		
//		System.out.println(atom.predicate);
//		for (String s : atom.arguments) {
//			System.out.println(s);
//		}

		assertEquals("p", bracket.predicate);
		assertEquals("1", bracket.arguments.get(0));
		assertEquals("2", bracket.arguments.get(1));
		assertEquals(2, bracket.arguments.size());

		assertEquals("p", atom.predicate);
		assertEquals("1", atom.arguments.get(0));
		assertEquals("2", atom.arguments.get(1));
		assertEquals(2, atom.arguments.size());
		
		assertEquals(bracket, atom);
		
		Set<Fact> set = new HashSet<>(Set.of(atom));
		assertTrue(set.contains(bracket));
	}
	
	@Test
	public void testFactCheck() {
		Fact f1 = new Fact("p(1,2)");
		Fact f2 = new Fact("p(?x,2)");
		Fact f3 = new Fact("p(1,Y)");
		Fact f4 = new Fact("p(\"A\",2)");
		Fact f5 = new Fact("p(1,\"?\")");
		
		assertTrue(f1.isFact());
		assertFalse(f2.isFact());
		assertFalse(f3.isFact());
		assertTrue(f4.isFact());
		assertTrue(f5.isFact());
		
	}

}
