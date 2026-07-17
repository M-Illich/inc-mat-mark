package transform;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import data.Fact;
import data.Update;

/**
 * Create sequence of random updates based on a given set of facts
 */
public class UpdatesCreator {

	/**
	 * set of every available fact that can potentially be part of updates
	 */
	public Set<Fact> dataPool;

	/**
	 * set of facts based on union of all (currently available) updates
	 */
	private Set<Fact> currentDataset;

	public UpdatesCreator(Set<Fact> dataPool) {
		this.dataPool = dataPool;
		this.currentDataset = new LinkedHashSet<>();
	}

	/**
	 * Create a sequence of random updates where each update adds and deletes the
	 * same number of facts, except for the first update
	 * 
	 * @param number      {@code int} Number of updates in sequence
	 * @param initialSize {@code int} Number of added facts for first update (has to
	 *                    be larger than {@code updateSize}
	 * @param updateSize  {@code int} Number of added and deleted facts for each
	 *                    update (except first one)
	 * @param overlapDel  {@code int} minimum number of facts that are added by one
	 *                    update and immediately deleted by the next one
	 * @param overlapAdd  {@code int} minimum number of facts that are deleted by
	 *                    one update and immediately (re)added by the next one
	 * @param randomSeed  {@code long} Seed for random number generator
	 * @return {@link List} of {@link Update} objects representing a sequence of
	 *         updates
	 */
	public List<Update> createRandomUpdates(int number, int initialSize, int updateSize, int overlapDel, int overlapAdd,
			boolean asBatch, long randomSeed) throws Exception {

		if (initialSize + updateSize > dataPool.size())
			throw new Exception("Initial update size (" + initialSize + ") is too big for used data pool ("
					+ dataPool.size() + ").");
		if (updateSize > initialSize)
			throw new Exception("Update size is too big for used initial size.");

		Random random = new Random(randomSeed);
		List<Update> updates = new LinkedList<>();

		// create first update that initializes dataset
		Update u0 = new Update(getRandomFacts(initialSize, new HashSet<>(), dataPool, currentDataset, asBatch, random),
				new HashSet<>());
		updates.add(u0);
		currentDataset.addAll(u0.added);

		// create remaining updates
		for (int i = 1; i < number; i++) {
			// add new facts from data pool
			Set<Fact> addFacts = new HashSet<>();
			addFacts = getRandomFacts(overlapAdd, addFacts, updates.get(i - 1).deleted, currentDataset, asBatch,
					random);
			addFacts = getRandomFacts(updateSize, addFacts, dataPool, currentDataset, asBatch, random);
			// delete facts from current dataset
			Set<Fact> delFacts = new HashSet<>();
			delFacts = getRandomFacts(overlapDel, delFacts, updates.get(i - 1).added, new HashSet<>(), asBatch, random);
			delFacts = getRandomFacts(updateSize, delFacts, currentDataset, new HashSet<>(), asBatch, random);

			updates.add(new Update(addFacts, delFacts));

			// adapt current dataset
			currentDataset.addAll(addFacts);
			currentDataset.removeAll(delFacts);

		}

		return updates;
	}

	/**
	 * Randomly select facts from {@code selection} and add them to {@code previous}
	 * if they do not occur in {@code exclusion} until {@code previous} contains
	 * {@code size}-many facts
	 * 
	 * @param size      {@code int} Desired number of returned facts
	 * @param previous  {@link Set} of {@link Fact} that will be extended with facts
	 * @param selection {@link Set} of {@link Fact} from which facts will be
	 *                  selected
	 * @param exclusion {@link Set} of {@link Fact} containing facts that must not
	 *                  be used for selection
	 * @param asBatch   {@code boolean} States if facts are selected as batch where
	 *                  the first fact is chosen randomly while the remaining facts
	 *                  are the ones that come after the first fact in
	 *                  {@code selection}. Note that this is only useful if
	 *                  {@code selection} is an ordered set.
	 * @param random    {@link Random} for randomized selection of facts
	 * @return {@link Set} of {@link Fact}
	 */
	private Set<Fact> getRandomFacts(int size, Set<Fact> previous, Set<Fact> selection, Set<Fact> exclusion,
			boolean asBatch, Random random) {
		Set<Fact> facts = new HashSet<>(previous);
		if (selection.size() > 0) {
			int index = random.nextInt(selection.size());
			while (facts.size() < size) {
				// get (random) fact from selection
				Fact fact = selection.toArray(new Fact[selection.size()])[index];
				// only add to previous if not in exclusion
				if (!exclusion.contains(fact)) {
					facts.add(fact);
				}

				// get next index
				if (asBatch) {
					// choose next fact according to order of selection
					if (index + 1 < selection.size()) {
						index++;
					} else {
						index = 0;
					}
				} else {
					index = random.nextInt(selection.size());
				}

			}
		}

		return facts;
	}

}
