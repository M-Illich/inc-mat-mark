package prolog;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import data.Fact;
import eval.RealUpdateStreamRun;
import eval.UpdateStreamRun;

public class PrologTest {

	@Test
	public void testProlog() {

		System.out.println("Ways test - DRed");
		String dir = "src/main/prolog/";

		testProlog(dir + "dred/dred_ways_no_mark_new.pl", dir + "dred/dred_ways_mark_new.pl",
				dir + "materialize_ways.pl", "src/main/resources/updates/ways/updates_track1"); // "src/test/resources/updates_ways";
																								
//		System.out.println("");
//		System.out.println("--------");
//		System.out.println("");
//		System.out.println("Ways test - B/F");			//TODO
//		testProlog(dir + "bf/bf_ways_no_mark.pl", dir + "bf/bf_ways_alt.pl", dir + "materialize_ways.pl");

	}

	public void testProlog(String file1, String file2, String fileExpected, String updateFolder) {

		int numberOfUpdates = new File(updateFolder).listFiles().length;

		// compute materialization without marking
		UpdateStreamRun usrNoMark = new RealUpdateStreamRun(file1, updateFolder);
		System.out.println(file1);
		usrNoMark.execute(false, false, true);
		System.out.println("");

		// compute materialization with marking approach
		UpdateStreamRun usrMark = new RealUpdateStreamRun(file2, updateFolder);
		System.out.println(file2);
		usrMark.execute(false, false, true);
		System.out.println("");

		// compute materialization with marking approach
		assertEquals(numberOfUpdates, usrNoMark.queryAnswers.size());
		assertEquals(numberOfUpdates, usrMark.queryAnswers.size());

		System.out.print("Non-incremental materialization: ");
		for (int i = 0; i < usrMark.datasets.size(); i++) {
			// compute materialization for dataset from scratch
			SimpleMaterialization sm = new SimpleMaterialization(fileExpected, usrMark.datasets.get(i));
			Set<Fact> mat = sm.execute();
			System.out.print(i + 1 + " ");

			// detect differences
			HashSet<Fact> diff = new HashSet<>();
			if (mat.size() < usrMark.queryAnswers.get(i).size()) {
				diff.addAll(usrMark.queryAnswers.get(i));
				diff.removeAll(mat);
			} else {
				diff.addAll(mat);
				diff.removeAll(usrMark.queryAnswers.get(i));
			}
			if (!diff.isEmpty()) {
				System.out.println("");
				for (Fact fact : diff) {
					System.out.println("diff: " + fact);
				}
			}

			// compare results with simple method
			assertEquals(mat.size(), usrMark.queryAnswers.get(i).size());
			assertTrue(mat.containsAll(usrMark.queryAnswers.get(i)));

			// compare between with and without marking
			assertEquals(usrNoMark.queryAnswers.get(i).size(), usrMark.queryAnswers.get(i).size());
			assertTrue(usrNoMark.queryAnswers.get(i).containsAll(usrMark.queryAnswers.get(i)));

		}
		System.out.println("");
	}

}
