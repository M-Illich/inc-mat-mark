package data;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.TreeSet;

public class Graph {

	public LinkedHashSet<Fact> edges;
	public int nodesNum;
	public int edgesNum;
	public long randomSeed;

	public Graph(int nodesNum, int edgesNum, long randomSeed) {
		this.nodesNum = nodesNum;
		this.edgesNum = edgesNum;
		this.randomSeed = randomSeed;
		edges = createEdges(nodesNum, edgesNum, randomSeed);
	}

	public LinkedHashSet<Fact> createEdges(int nodesNum, int edgesNum, long ranomSeed) {
		TreeSet<Fact> edges = new TreeSet<>();

		Random rnd = new Random(randomSeed);

		while (edges.size() < edgesNum) {
			String x = rnd.nextInt(nodesNum) + "";
			String y = rnd.nextInt(nodesNum) + "";

			edges.add(new Fact("edge", List.of(x, y)));
		}

		return new LinkedHashSet<>(edges);

	}

}
