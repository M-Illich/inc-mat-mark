package eval;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;

import org.junit.Test;

public class StatisticsTest {

	@Test
	public void testIntegrateData() {
		// test input
		LinkedList<String> data = new LinkedList<>();
		data.add("applied_rules(ins,[5,8])");
		data.add("marked_facts(posEx,[2,0,4])");
		data.add("% 3,440,308 inferences, 0.313 CPU in 0.332 seconds (94% CPU, 11008986 Lips)");

		Statistics stats = new Statistics();
		stats.integrateData(data);

		// check stored data
		assertEquals("[5,8]", stats.appliedRules.get("ins"));
		assertEquals("[2,0,4]", stats.markedFacts.get("posEx"));
		assertEquals(0.313f, stats.cpuTime, 0.0001f);
		assertEquals(0.332f, stats.executionTime, 0.0001f);

	}

}
