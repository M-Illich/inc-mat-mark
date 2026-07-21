package data;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Test;

public class AtomTest {

	@Test
	public void testConstructor() {
		Atom bracket = new Atom("[p, a:X, 2]");
		Atom atom = new Atom("p(a:X, 2)");
		Atom atomBracket = new Atom("q[?x, Y, z:t]");
		Atom atomList = new Atom("q", List.of("?x", "Y", "z:t"));

		assertEquals("p", bracket.predicate);
		assertEquals("'a:X'", bracket.arguments.get(0));
		assertEquals("2", bracket.arguments.get(1));
		assertEquals(2, bracket.arguments.size());

		assertEquals("p", atom.predicate);
		assertEquals("'a:X'", atom.arguments.get(0));
		assertEquals("2", atom.arguments.get(1));
		assertEquals(2, atom.arguments.size());

		assertEquals(bracket, atom);
		
		Set<Atom> set = new HashSet<>(Set.of(atom));
		assertTrue(set.contains(bracket));

		assertEquals("q", atomBracket.predicate);
		assertEquals("X", atomBracket.arguments.get(0));
		assertEquals("Y", atomBracket.arguments.get(1));
		assertEquals("'z:t'", atomBracket.arguments.get(2));
		assertEquals(3, atomBracket.arguments.size());
		
		assertEquals(atomBracket, atomList);
		
	}

	@Test
	public void testEnsureCorrectFormat() {
		Atom a = new Atom("p", List.of("?x", "?Ab", "a:Z"));
		assertEquals("X", a.ensureCorrectFormat("?x"));
		assertEquals("Y", a.ensureCorrectFormat("Y"));
		assertEquals("'a:B'", a.ensureCorrectFormat("a:B"));
	}
	
	@Test
	public void testStringFormats() {
		Atom a = new Atom("p", List.of("?x", "?Ab", "a:Z"));	
		assertEquals("p(X, Ab, 'a:Z')", a.toString());
		assertEquals("[p, X, Ab, 'a:Z']", a.toBracketString());
		

	}

}
