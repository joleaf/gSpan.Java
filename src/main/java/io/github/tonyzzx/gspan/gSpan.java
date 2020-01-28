package io.github.tonyzzx.gspan;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import io.github.tonyzzx.gspan.model.DFSCode;
import io.github.tonyzzx.gspan.model.Edge;
import io.github.tonyzzx.gspan.model.EfficientHistory;
import io.github.tonyzzx.gspan.model.Graph;
import io.github.tonyzzx.gspan.model.PDFS;
import io.github.tonyzzx.gspan.model.Projected;
import io.github.tonyzzx.gspan.model.Vertex;
import smu.hongjin.CountingUtils;
import smu.hongjin.CountingUtils.UpperBoundReturnType;
import smu.hongjin.LoggingUtils;

import java.util.NavigableMap;
import java.util.Set;
import java.util.TreeMap;
import java.util.Vector;

import org.apache.commons.math3.stat.inference.ChiSquareTest;
import org.mskcc.cbio.portal.stats.FisherExact;

public class gSpan {
	private ArrayList<Graph> TRANS;
	private DFSCode DFS_CODE;
	private DFSCode DFS_CODE_IS_MIN;
	private Graph GRAPH_IS_MIN;

	private long ID;
	private long minSup;
	private long maxPat_min;
	private long maxPat_max;
	private boolean directed;
	private FileWriter os;

	// Singular vertex handling stuff [graph][vertexLabel] = count.
	private NavigableMap<Integer, NavigableMap<Integer, Integer>> singleVertex;
	private NavigableMap<Integer, Integer> singleVertexLabel;

	// HJ for counting coverage of dataset
	public int totalMisuses = 0;
	public int totalCorrectUses = 0;
	int totalUnlabeled = 0;
	public int minimumToLabel;

	// HJ: weights of the components
	// just a thought: we are likely to benefit from scaling the weight of each
	// (A/B/U)_(S0/S1) directly.
	// Do this based on the disproportionality of each count. For example, if we
	// have few minority class B
	double AWeight, BWeight, UWeight;

	public static double skewnessImportance = 50.0;

	int numberOfFeatures = 200;

	private final int maxGraphCount = 3; // prevent a single type of graph from domainating the quality landscape

	// a minimal quality q_s to beat
	double minimalQS;

	EnumMap<GRAPH_LABEL, Integer> countsOfLabels = new EnumMap<>(GRAPH_LABEL.class);

	// currently selected set of subgraph features
	// There is no efficient way to enumerate them all
	public Map<Long, Double> selectedSubgraphFeatures = new HashMap<>();

	public Set<Integer> misuses = new HashSet<>();
	public Set<Integer> correctUses = new HashSet<>();
	public Map<Integer, Integer> quantities = new HashMap<>();

	// Use these data structures to determine which examples we need more labels of
	public Set<Integer> uncoveredUnlabeledGraphs = new HashSet<>();
	public Set<Integer> uncoveredLabeledGraphs = new HashSet<>();
	public Map<Integer, Integer> usefulGeneralUnlabelledGraphs = new HashMap<>();
	public Map<Integer, Integer> usefulSpecificUnlabelledGraphs = new HashMap<>();
	public Map<Integer, Integer> subgraphForDoubleCheckingUnlabelledGraphs = new HashMap<>();
	public Set<Long> frequentUnlabelledSubgraphs = new HashSet<>(); // subgraphs infrequent in labeled set, but frequent
																	// in U

	public Map<Integer, Integer> graphsForSubgraphsNeedMoreEvidence = new HashMap<>();

	private double theta = 0.0;

	public enum GRAPH_LABEL {
		MISUSE, CORRECT_USE, UNLABELED
	}

	// coverage only tracks coverage of C and M
	public Map<Long, Set<Integer>> coverage = new HashMap<>(); // map of subgraph id -> set of graphs hit
	// unlabeledCoverage tracks coverage of U
	public Map<Long, Set<Integer>> unlabeledCoverage = new HashMap<>(); // map of subgraph id -> set of graphs hit

	public Set<Long> alreadyRequestForMoreLabels = new HashSet<>();

	// debug
	public static int wouldBeAcceptedWithoutSemiSupervisedFilters = 0;
	public static int wouldNotBePrunedWithoutSemiSupervisedFilters = 0;

	public gSpan() {
		TRANS = new ArrayList<>();
		DFS_CODE = new DFSCode();
		DFS_CODE_IS_MIN = new DFSCode();
		GRAPH_IS_MIN = new Graph();

		singleVertex = new TreeMap<>();
		singleVertexLabel = new TreeMap<>();

	}

	/**
	 * Run gSpan.
	 *
	 * @param reader     FileReader
	 * @param writers    FileWriter
	 * @param minSup     Minimum support
	 * @param maxNodeNum Maximum number of nodes
	 * @param minNodeNum Minimum number of nodes
	 * @throws IOException
	 */
	void run(FileReader reader, FileWriter writers, long minSup, long maxNodeNum, long minNodeNum) throws IOException {

		LoggingUtils.logTimingStatistics();

		os = writers;
		ID = 0;
		this.minSup = minSup;
		maxPat_min = minNodeNum;
		maxPat_max = maxNodeNum;
		directed = true;

		read(reader);

		// ste weights.
		// Expected: weight * amount = 100
		if (totalCorrectUses > totalMisuses) {
			// majority class is "C"
			AWeight = 100.0 / totalCorrectUses;
			BWeight = 100.0 / totalMisuses;
		} else {
			// majority class is "M"
			AWeight = 100.0 / totalMisuses;
			BWeight = 100.0 / totalCorrectUses;
		}

		UWeight = skewnessImportance / totalUnlabeled;

		System.out.println("totalCorrectUses=" + totalCorrectUses);
		System.out.println("totalMisuses=" + totalMisuses);
		System.out.println("totalUnlabeled=" + totalUnlabeled);
		System.out.println("weight are : AWeight=" + AWeight + ", BWeight=" + BWeight + ", UWeight=" + UWeight);

		minimalQS = 0.0;
		theta = minimalQS;

		minimumToLabel = CountingUtils.minimumCountForSignificanceMinority(totalCorrectUses, totalMisuses);

		runIntern();

		LoggingUtils.logTimingStatistics();

	}

	private void read(FileReader is) throws IOException {
		BufferedReader read = new BufferedReader(is);
		long id = 0;
		while (true) {
			Graph g = new Graph(directed);

			read = g.read(read);
			if (g.isEmpty())
				break;
			if (g.ID != id) {
				throw new RuntimeException("ID differs at " + g.ID + " (read from file) and " + id
						+ " (determined by increasing number). They have to be the same");
			}
			TRANS.add(g);
			if (g.label == 'M') {

				misuses.add(Math.toIntExact(id));
				int qty = Math.min(g.quantity, maxGraphCount);
				totalMisuses += qty;
				quantities.put(Math.toIntExact(id), qty);

				if (qty <= 0) {
					throw new RuntimeException("invalid qty " + qty);
				}
			} else if (g.label == 'C') {

				correctUses.add(Math.toIntExact(id));
				int qty = Math.min(g.quantity, maxGraphCount);
				totalCorrectUses += qty;
				quantities.put(Math.toIntExact(id), qty);
				if (qty <= 0) {
					throw new RuntimeException("invalid qty " + qty);
				}

			} else if (g.label == 'U') {

				totalUnlabeled += Math.min(g.quantity, maxGraphCount);

				uncoveredUnlabeledGraphs.add(Math.toIntExact(id)); // first, we add all unlabeled data to
																	// uncoveredUnlabeledGraphs
				// at the end of the mining process, we will go through it and remove covered
				// graphs
			} else {
				throw new RuntimeException(
						"huh? label (which should be 'M', 'C' or 'U') seems to be " + g.label + ", at id=" + id);
			}

			id++;
		}
		read.close();
		
		System.out.println("correct sz " + correctUses.size());
		System.out.println("misuses sz " + misuses.size());
	}

	private void runIntern() throws IOException {
		// In case 1 node sub-graphs should also be mined for, do this as pre-processing
		// step.
		if (maxPat_min <= 1) {
			/*
			 * Do single node handling, as the normal gSpan DFS code based processing cannot
			 * find sub-graphs of size |sub-g|==1. Hence, we find frequent node labels
			 * explicitly.
			 */
			for (int id = 0; id < TRANS.size(); ++id) {
				for (int nid = 0; nid < TRANS.get(id).size(); ++nid) {
					int key = TRANS.get(id).get(nid).label;
					singleVertex.computeIfAbsent(id, k -> new TreeMap<>());
					if (singleVertex.get(id).get(key) == null) {
						// number of graphs it appears in
						singleVertexLabel.put(key, Common.getValue(singleVertexLabel.get(key)) + 1);
					}

					singleVertex.get(id).put(key, Common.getValue(singleVertex.get(id).get(key)) + 1);
				}
			}
		}
		/*
		 * All minimum support node labels are frequent 'sub-graphs'.
		 * singleVertexLabel[nodeLabel] gives the number of graphs it appears in.
		 */
		for (Entry<Integer, Integer> it : singleVertexLabel.entrySet()) {
			if (it.getValue() < minSup)
				continue;

			int frequent_label = it.getKey();

			// Found a frequent node label, report it.
			Graph g = new Graph(directed);
			Vertex v = new Vertex();
			v.label = frequent_label;
			g.add(v);

			// [graph_id] = count for current substructure
			Vector<Integer> counts = new Vector<>();
			counts.setSize(TRANS.size());
			for (Entry<Integer, NavigableMap<Integer, Integer>> it2 : singleVertex.entrySet()) {
				counts.set(it2.getKey(), it2.getValue().get(frequent_label));
			}

			NavigableMap<Integer, Integer> gyCounts = new TreeMap<>();
			for (int n = 0; n < counts.size(); ++n)
				gyCounts.put(n, counts.get(n));

			reportSingle(g, gyCounts);
		}

		ArrayList<Edge> edges = new ArrayList<>();
		NavigableMap<Integer, NavigableMap<Integer, NavigableMap<Integer, Projected>>> root = new TreeMap<>();

		for (int id = 0; id < TRANS.size(); ++id) {
			Graph g = TRANS.get(id);
			for (int from = 0; from < g.size(); ++from) {
				if (Misc.getForwardRoot(g, g.get(from), edges)) {
					for (Edge it : edges) {
						int key_1 = g.get(from).label;
						NavigableMap<Integer, NavigableMap<Integer, Projected>> root_1 = root.computeIfAbsent(key_1,
								k -> new TreeMap<>());
						int key_2 = it.eLabel;
						NavigableMap<Integer, Projected> root_2 = root_1.computeIfAbsent(key_2, k -> new TreeMap<>());
						int key_3 = g.get(it.to).label;
						Projected root_3 = root_2.get(key_3);
						if (root_3 == null) {
							root_3 = new Projected();
							root_2.put(key_3, root_3);
						}
						root_3.push(id, it, null);
					}
				}
			}
		}

		for (Entry<Integer, NavigableMap<Integer, NavigableMap<Integer, Projected>>> fromLabel : root.entrySet()) {
			for (Entry<Integer, NavigableMap<Integer, Projected>> eLabel : fromLabel.getValue().entrySet()) {
				for (Entry<Integer, Projected> toLabel : eLabel.getValue().entrySet()) {
					// Build the initial two-node graph. It will be grown recursively within
					// `project`.
					DFS_CODE.push(0, 1, fromLabel.getKey(), eLabel.getKey(), toLabel.getKey());
					project(toLabel.getValue(), 0, false, -1);
					DFS_CODE.pop();
				}
			}
		}
	}

	/**
	 * Special report function for single node graphs.
	 *
	 * @param g
	 * @param nCount
	 * @throws IOException
	 */
	private void reportSingle(Graph g, NavigableMap<Integer, Integer> nCount) throws IOException {
		int sup = 0;
		resetCountsOfLabels();
		
		for (Entry<Integer, Integer> it : nCount.entrySet()) {
			sup += Common.getValue(it.getValue());
			
//			// now update the `counts` map
//			boolean isMisuse = misuses.contains(Common.getValue(it.getValue()));
//			boolean isCorrectUse = correctUses.contains(Common.getValue(it.getValue()));
//
//			if (isMisuse && isCorrectUse) {
//				throw new RuntimeException("invalid label!");
//			}
//			coverage.putIfAbsent(ID, new HashSet<>());
//			unlabeledCoverage.putIfAbsent(ID, new HashSet<>());
//
//			if (isMisuse) {
//				countsOfLabels.put(GRAPH_LABEL.MISUSE, countsOfLabels.get(GRAPH_LABEL.MISUSE)
////						+ 1); 
//						+ Math.min(TRANS.get(Common.getValue(it.getValue())).quantity, maxGraphCount));
//
//				if (countsOfLabels.get(GRAPH_LABEL.MISUSE) > totalMisuses) {
//					throw new RuntimeException("invalid MISUSE counts");
//				}
//
////				System.out.println("putting into coverage=" + ID);
//				coverage.get(ID).add(Common.getValue(it.getValue()));
//			} else if (isCorrectUse) {
//				countsOfLabels.put(GRAPH_LABEL.CORRECT_USE, countsOfLabels.get(GRAPH_LABEL.CORRECT_USE)
////						+ 1); 
//						+ Math.min(TRANS.get(Common.getValue(it.getValue())).quantity, maxGraphCount));
////				System.out.println("putting into coverage=" + ID);
//				if (countsOfLabels.get(GRAPH_LABEL.CORRECT_USE) > totalCorrectUses) {
//					throw new RuntimeException("invalid CORRECT_USE counts");
//				}
//
//				coverage.get(ID).add(Common.getValue(it.getValue()));
//			} else { // unlabeled
//				countsOfLabels.put(GRAPH_LABEL.UNLABELED, countsOfLabels.get(GRAPH_LABEL.UNLABELED) +
////						1);
//						Math.min(TRANS.get(Common.getValue(it.getValue())).quantity, maxGraphCount));
//
//				if (countsOfLabels.get(GRAPH_LABEL.UNLABELED) > totalUnlabeled) {
//					throw new RuntimeException("invalid UNLABELED counts");
//				}
//				unlabeledCoverage.get(ID).add(Common.getValue(it.getValue()));
//			}
		}

		if (maxPat_max > maxPat_min && g.size() > maxPat_max)
			return;
		if (maxPat_min > 0 && g.size() < maxPat_min)
			return;

		os.write("t # " + ID + " * " + sup + System.getProperty("line.separator"));
		g.write(os);
		
//		int A_S0, B_S0, U_S0, A_S1, B_S1, U_S1;
//
//		if (totalCorrectUses > totalMisuses) {
//			LoggingUtils.logOnce("Majority class is correct usage");
//			// correct uses are the majority case, so A is the "Correct use" (C) label
//			A_S0 = totalCorrectUses - countsOfLabels.get(GRAPH_LABEL.CORRECT_USE);
//			A_S1 = countsOfLabels.get(GRAPH_LABEL.CORRECT_USE);
//			B_S0 = totalMisuses - countsOfLabels.get(GRAPH_LABEL.MISUSE);
//			B_S1 = countsOfLabels.get(GRAPH_LABEL.MISUSE);
//			U_S0 = totalUnlabeled - countsOfLabels.get(GRAPH_LABEL.UNLABELED);
//			U_S1 = countsOfLabels.get(GRAPH_LABEL.UNLABELED);
//
//		} else {
//			LoggingUtils.logOnce("Majority class is misuse");
//			// misuses are the majority case, so A is the "Misuse" (M) label
//			A_S0 = totalMisuses - countsOfLabels.get(GRAPH_LABEL.MISUSE);
//			A_S1 = countsOfLabels.get(GRAPH_LABEL.MISUSE);
//			B_S0 = totalCorrectUses - countsOfLabels.get(GRAPH_LABEL.CORRECT_USE);
//			B_S1 = countsOfLabels.get(GRAPH_LABEL.CORRECT_USE);
//			U_S0 = totalUnlabeled - countsOfLabels.get(GRAPH_LABEL.UNLABELED);
//			U_S1 = countsOfLabels.get(GRAPH_LABEL.UNLABELED);
//
//		}
//		double q_s = computeQualityTODetermineIfSignificant(A_S0, B_S0, U_S0, A_S1, B_S1, U_S1, -1, -1,
//				0);

//		System.out.println("report single. ID=" + ID);
//		System.out.println("q_s=" + q_s + " , ");
		
		ID++;
	}

	private boolean report(int sup) throws IOException {
		// Filter to small/too large graphs.
		if (maxPat_max > maxPat_min && DFS_CODE.countNode() > maxPat_max)
			return false;
		if (maxPat_min > 0 && DFS_CODE.countNode() < maxPat_min)
			return false;

		Graph g = new Graph(directed);
		DFS_CODE.toGraph(g);
		os.write("t # " + ID + " * " + sup + System.getProperty("line.separator"));
		g.write(os);

//		System.out.println("--\tdebug:size of subgraph = " + g.size());
//		System.out.println("\t: # of edges= " + g.edge_size);

		return true;
	}

	/**
	 * Recursive sub-graph mining function (similar to sub-procedure 1
	 * Sub-graph_Mining in [Yan2002]).
	 *
	 * @param projected
	 * @throws IOException
	 */
	private void project(Projected projected, double currentBranchScore, boolean wasSubgraphNearBoundary,
			int subgraphIDNearBoundary) throws IOException {
		// Check if the pattern is frequent enough.
		resetCountsOfLabels();
		int sup = support(projected);
		if (sup < minSup) {
			coverage.remove(ID);
			return;
		}

		/*
		 * The minimal DFS code check is more expensive than the support check, hence it
		 * is done now, after checking the support.
		 */
		if (!isMin()) {
			coverage.remove(ID);
			return;
		}

		// Output the frequent substructure
		boolean isReported = report(sup);

		if (isReported) { // isReported == true means that its a frequent subgraph.
			// if it's a valid frequent subgraph, then check if its a valid significant
			// subgraph

			int A_S0, B_S0, U_S0, A_S1, B_S1, U_S1;

			if (totalCorrectUses > totalMisuses) {
				LoggingUtils.logOnce("Majority class is correct usage");
				// correct uses are the majority case, so A is the "Correct use" (C) label
				A_S0 = totalCorrectUses - countsOfLabels.get(GRAPH_LABEL.CORRECT_USE);
				A_S1 = countsOfLabels.get(GRAPH_LABEL.CORRECT_USE);
				B_S0 = totalMisuses - countsOfLabels.get(GRAPH_LABEL.MISUSE);
				B_S1 = countsOfLabels.get(GRAPH_LABEL.MISUSE);
				U_S0 = totalUnlabeled - countsOfLabels.get(GRAPH_LABEL.UNLABELED);
				U_S1 = countsOfLabels.get(GRAPH_LABEL.UNLABELED);

			} else {
				LoggingUtils.logOnce("Majority class is misuse");
				// misuses are the majority case, so A is the "Misuse" (M) label
				A_S0 = totalMisuses - countsOfLabels.get(GRAPH_LABEL.MISUSE);
				A_S1 = countsOfLabels.get(GRAPH_LABEL.MISUSE);
				B_S0 = totalCorrectUses - countsOfLabels.get(GRAPH_LABEL.CORRECT_USE);
				B_S1 = countsOfLabels.get(GRAPH_LABEL.CORRECT_USE);
				U_S0 = totalUnlabeled - countsOfLabels.get(GRAPH_LABEL.UNLABELED);
				U_S1 = countsOfLabels.get(GRAPH_LABEL.UNLABELED);

			}

			boolean isDebug = detectGraphsForDebugging(A_S0, B_S0, U_S0, A_S1, B_S1, U_S1);

			double q_s = computeQualityTODetermineIfSignificant(A_S0, B_S0, U_S0, A_S1, B_S1, U_S1, -1, -1,
					currentBranchScore);

			if (isDebug) {
				System.out.println("\tq_s for debug is:" + q_s);
			}
			currentBranchScore = Math.max(q_s, currentBranchScore);

			// low frequency in labeled graphs, but appears frequently in U: might be
			// important!
			// these subgraphs have high generality, but we don't know about them yet. Thus,
			// the user need to label more
			LoggingUtils.logOnce("Boundary of general-unlabelled: ");
			if (A_S1 + B_S1 < 15 && U_S1 >= 0.1 * totalUnlabeled) {
				frequentUnlabelledSubgraphs.add(ID);

				for (Integer unlabeled : unlabeledCoverage.get(ID)) {
					usefulGeneralUnlabelledGraphs.putIfAbsent(unlabeled, 0);
					usefulGeneralUnlabelledGraphs.put(unlabeled, usefulGeneralUnlabelledGraphs.get(unlabeled) + 1);
				}
			}

			// low frequency in labeled graphs, but appears just sufficient in U: might be
			// important!
			// these subgraphs are significant and have high specificity, but we don't know
			// about them yet.
			// Thus, the user need to label more
			LoggingUtils.logOnce("Boundary of specific-unlabelled: " + 0.01 * totalUnlabeled);
			if (A_S1 + B_S1 < 15 && U_S1 >= 5 && U_S1 < 0.1 * totalUnlabeled) { // 10%
				frequentUnlabelledSubgraphs.add(ID);

				int selected = 0;
				if (isDebug) {
					System.out.println("Request for more labels of debugged subgraph");
				}
				for (Integer unlabeled : unlabeledCoverage.get(ID)) {
					if (selected > 9) {
						break;
					}

					usefulSpecificUnlabelledGraphs.putIfAbsent(unlabeled, 0);
					usefulSpecificUnlabelledGraphs.put(unlabeled, usefulSpecificUnlabelledGraphs.get(unlabeled) + 1);

					selected += 1;
				}
			}
			// if quantity already significant! Try to check if overfitting by comparing
			// against unlabelled data.
			// especially on the majority class
			if (A_S1 > 30) {
				float expectedUProportion = (float) U_S1 / (U_S1 + U_S0);
				float majorityProportion = (float) A_S1 / (A_S1 + A_S0);

				int selected = 0;
				if (Math.abs(majorityProportion - expectedUProportion) > 0.1) { // more than 10%
					for (Integer unlabeled : unlabeledCoverage.get(ID)) {

						if (selected > 5) {
							break;
						}

						subgraphForDoubleCheckingUnlabelledGraphs.putIfAbsent(unlabeled, 0);
						subgraphForDoubleCheckingUnlabelledGraphs.put(unlabeled,
								subgraphForDoubleCheckingUnlabelledGraphs.get(unlabeled) + 1);

						selected += 1;
					}

				}
			}
			
			// subgraph that is frequent in U, not in labeled data, but already covered
			// TODO 

			UpperBoundReturnType upperBound = CountingUtils.upperBound(q_s, A_S0, A_S1, B_S0, B_S1, U_S0, U_S1, AWeight,
					BWeight, UWeight, isDebug);
			// debug; never prune
//			upperBound = UpperBoundReturnType.GOOD;
//			q_s = Math.max(q_s, 1);

			if (isDebug) {
				System.out.println("\tupperBound for debug is:" + (upperBound));
			}

			if (upperBound == UpperBoundReturnType.BAD_EXPLORE) {
				// maybe getting more data can help?

				int selected = 0;
				for (Integer unlabeled : unlabeledCoverage.get(ID)) {
					if (selected > minimumToLabel / 2) {
						break;
					}

					graphsForSubgraphsNeedMoreEvidence.putIfAbsent(unlabeled, 0);
					graphsForSubgraphsNeedMoreEvidence.put(unlabeled,
							graphsForSubgraphsNeedMoreEvidence.get(unlabeled) + 1);

					selected += 1;
				}

			} else if (upperBound == UpperBoundReturnType.BAD && wasSubgraphNearBoundary) {
				// maybe getting more data can help?

				int selected = 0;
				if (!alreadyRequestForMoreLabels.contains((long) subgraphIDNearBoundary)) {

					for (Integer unlabeled : unlabeledCoverage.get((long) subgraphIDNearBoundary)) {
						if (selected > minimumToLabel / 2) {
							break;
						}
						System.out.println("\trequest more labels for:" + subgraphIDNearBoundary);
						graphsForSubgraphsNeedMoreEvidence.putIfAbsent(unlabeled, 0);
						graphsForSubgraphsNeedMoreEvidence.put(unlabeled,
								graphsForSubgraphsNeedMoreEvidence.get(unlabeled) + 1);

						selected += 1;
					}
					alreadyRequestForMoreLabels.add((long) subgraphIDNearBoundary);
				}
			}

			if (!wasSubgraphNearBoundary && upperBound == UpperBoundReturnType.GOOD_EXPLORE) {
				wasSubgraphNearBoundary = true;
				subgraphIDNearBoundary = (int) ID;
			}

			++ID; // must increase since this ID was used for `report` and is included in the
			// subgraphs output

			if (upperBound == UpperBoundReturnType.BAD) {
				System.out.println("\tPruning");
//				coverage.remove(ID - 1);
				return; // if we can do no better than the worst feature in the top-`numberOfFeatures`,
						// prune the branch
			}
		} else {
			coverage.remove(ID); // ID didn't get reported, it may be reused for another subgraph
		}

		/*
		 * In case we have a valid upper bound and our graph already exceeds it, return.
		 * Note: we do not check for equality as the DFS exploration may still add edges
		 * within an existing sub-graph, without increasing the number of nodes.
		 */
		if (maxPat_max > maxPat_min && DFS_CODE.countNode() > maxPat_max) {
			coverage.remove(ID); // ID didn't get reported, it may be reused for another subgraph
			return;
		}

		if (DFS_CODE.countNode() == maxPat_max) {
			return;
		}

		/*
		 * We just outputted a frequent sub-graph. As it is frequent enough, so might be
		 * its (n+1)-extension-graphs, hence we enumerate them all.
		 */
		ArrayList<Integer> rmPath = DFS_CODE.buildRMPath();
		int minLabel = DFS_CODE.get(0).fromLabel;
		int maxToc = DFS_CODE.get(rmPath.get(0)).to;

		NavigableMap<Integer, NavigableMap<Integer, NavigableMap<Integer, Projected>>> new_fwd_root = new TreeMap<>();
		NavigableMap<Integer, NavigableMap<Integer, Projected>> new_bck_root = new TreeMap<>();
		ArrayList<Edge> edges = new ArrayList<>();

		// Enumerate all possible one edge extensions of the current substructure.
//		System.out.println("\titerating over projected which is len= " + projected.size());
		for (PDFS aProjected : projected) {

			int id = aProjected.id;
			EfficientHistory history = new EfficientHistory(TRANS.get(id), aProjected);

			// XXX: do we have to change something here for directed edges?

			// backward
			for (int i = rmPath.size() - 1; i >= 1; --i) {
				// HJ notes: rmPath.get(0) must be the right-most vertex
				// see paper; only the right-most vertex can be extended with backwards edge.
				Edge e = Misc.getBackward(TRANS.get(id), history.ordering.get(rmPath.get(i)),
						history.ordering.get(rmPath.get(0)), history, singleVertexLabel, minSup);
				if (e != null) {
					int key_1 = DFS_CODE.get(rmPath.get(i)).from;
					NavigableMap<Integer, Projected> root_1 = new_bck_root.computeIfAbsent(key_1, k -> new TreeMap<>());
					int key_2 = e.eLabel;
					Projected root_2 = root_1.get(key_2);
					if (root_2 == null) {
						root_2 = new Projected();
						root_1.put(key_2, root_2);
					}
					root_2.push(id, e, aProjected);
				}
			}

			// pure forward
			// FIXME: here we pass a too large e.to (== history[rmPath[0]].to
			// into getForwardPure, such that the assertion fails.
			//
			// The problem is:
			// history[rmPath[0]].to > TRANS[id].size()
			if (Misc.getForwardPure(TRANS.get(id), history.ordering.get(rmPath.get(0)), minLabel, history, edges,
					singleVertexLabel, minSup))
				for (Edge it : edges) {
					NavigableMap<Integer, NavigableMap<Integer, Projected>> root_1 = new_fwd_root
							.computeIfAbsent(maxToc, k -> new TreeMap<>());
					int key_2 = it.eLabel;
					NavigableMap<Integer, Projected> root_2 = root_1.computeIfAbsent(key_2, k -> new TreeMap<>());
					int key_3 = TRANS.get(id).get(it.to).label;
					Projected root_3 = root_2.get(key_3);
					if (root_3 == null) {
						root_3 = new Projected();
						root_2.put(key_3, root_3);
					}
					root_3.push(id, it, aProjected);
				}
			// backtracked forward
			for (Integer aRmPath : rmPath)
				if (Misc.getForwardRmPath(TRANS.get(id), history.ordering.get(aRmPath), minLabel, history, edges,
						singleVertexLabel, minSup))
					for (Edge it : edges) {
						int key_1 = DFS_CODE.get(aRmPath).from;
						NavigableMap<Integer, NavigableMap<Integer, Projected>> root_1 = new_fwd_root
								.computeIfAbsent(key_1, k -> new TreeMap<>());
						int key_2 = it.eLabel;
						NavigableMap<Integer, Projected> root_2 = root_1.computeIfAbsent(key_2, k -> new TreeMap<>());
						int key_3 = TRANS.get(id).get(it.to).label;
						Projected root_3 = root_2.get(key_3);
						if (root_3 == null) {
							root_3 = new Projected();
							root_2.put(key_3, root_3);
						}
						root_3.push(id, it, aProjected);
					}
		}

		// Test all extended substructures.
		// backward
		for (Entry<Integer, NavigableMap<Integer, Projected>> to : new_bck_root.entrySet()) {
			for (Entry<Integer, Projected> eLabel : to.getValue().entrySet()) {
				DFS_CODE.push(maxToc, to.getKey(), -1, eLabel.getKey(), -1);
				project(eLabel.getValue(), currentBranchScore, wasSubgraphNearBoundary, subgraphIDNearBoundary);
				DFS_CODE.pop();
			}
		}

		// forward
		for (Entry<Integer, NavigableMap<Integer, NavigableMap<Integer, Projected>>> from : new_fwd_root.descendingMap()
				.entrySet()) {
			for (Entry<Integer, NavigableMap<Integer, Projected>> eLabel : from.getValue().entrySet()) {
				for (Entry<Integer, Projected> toLabel : eLabel.getValue().entrySet()) {
					DFS_CODE.push(from.getKey(), maxToc + 1, -1, eLabel.getKey(), toLabel.getKey());
					project(toLabel.getValue(), currentBranchScore, wasSubgraphNearBoundary, subgraphIDNearBoundary);
					DFS_CODE.pop();
				}
			}
		}
	}

	// used to check if the graph contains interesting stuff. More logs will be printed if so
	private boolean detectGraphsForDebugging(int A_S0, int B_S0, int U_S0, int A_S1, int B_S1, int U_S1) {
		boolean isDebug = false;
		for (Vertex debugnode : GRAPH_IS_MIN) {
//				if (debugnode.label == 37) { // String:AES
//					System.out.println("=====Found debug node: " + 37);
//					System.out.println("\tCounts are:");
//					System.out.println("\t" + A_S0 + "," + B_S0 + "," + U_S0 + "," + A_S1 + "," + B_S1 + "," + U_S1);
//					System.out.println("\t\t Proportion: " + ((float) U_S1 / (U_S0 + U_S1)));
//					isDebug = true;
//				}
//				if (debugnode.label == 6) { // String:DES,6
//					System.out.println("=====Found debug node: " + 6);
//					System.out.println("\tCounts are:");
//					System.out.println("\t" + A_S0 + "," + B_S0 + "," + U_S0 + "," + A_S1 + "," + B_S1 + "," + U_S1);
//					System.out.println("\t\t Proportion: " + ((float) U_S1 / (U_S0 + U_S1)));
//					isDebug = true;
//				}
//				if (debugnode.label == 238) { // String:AES/ECB/NoPadding,238
//					System.out.println("=====Found debug node: " + 238);
//					System.out.println("\tCounts are:");
//					System.out.println("\t" + A_S0 + "," + B_S0 + "," + U_S0 + "," + A_S1 + "," + B_S1 + "," + U_S1);
//					System.out.println("\t\t Proportion: " + ((float) U_S1 / (U_S0 + U_S1)));
//					isDebug = true;
//				}
//
//				if (debugnode.label == 7) { // Cipher.getInstance(),7
//					System.out.println("=====Found debug node: " + 7);
//					System.out.println("\tCounts are:");
//					System.out.println("\t" + A_S0 + "," + B_S0 + "," + U_S0 + "," + A_S1 + "," + B_S1 + "," + U_S1);
//					System.out.println("\t\t Proportion: " + ((float) U_S1 / (U_S0 + U_S1)));
//					isDebug = true;
//				}
		
			if (debugnode.label == 206) { // interface_Enumeration,206
				System.out.println("=====Found debug node: " + 206);
				System.out.println("\tCounts are:");
				System.out.println("\t" + A_S0 + "," + B_S0 + "," + U_S0 + "," + A_S1 + "," + B_S1 + "," + U_S1);
				System.out.println("\t\t Proportion: " + ((float) U_S1 / (U_S0 + U_S1)));
				isDebug = true;
			}
			

		}
		return isDebug;
	}

	private double computeQualityTODetermineIfSignificant(int A_S0, int B_S0, int U_S0, int A_S1, int B_S1, int U_S1,
			int A_N, int B_N, double currentBranchScore) {

		int originalSize = selectedSubgraphFeatures.size();

		boolean isRelevant = true;
		double q_s = -1;

		// 1st filter: early return if obviously not useful
		if (A_S1 == 0 && B_S1 == 0) {
			// early reject.
			// but this indicates that there are subgraphs in U that cannot be labeled
//			System.out.println("\tearly reject due to absense in labeled sets. ID=" + ID);
			isRelevant = false;
			q_s = -10;
		}
		// 2nd filter: statistical test for significance
		if (isRelevant) {
			if (A_S1 < 3 && B_S1 < 3) { // early return. Minority class can reach significance with too few items.
				isRelevant = false;
				q_s = -5;
			} else {

				long[][] currentCounts = { { A_S1, A_S0 }, { B_S1, B_S0 } };
				ChiSquareTest test = new ChiSquareTest();

				double pValue = test.chiSquareTest(currentCounts);
				if (pValue > 0.05) {
					isRelevant = false;
					q_s = -5;
				}

			}
		}

		// 3nd filter
		if (isRelevant) {
			q_s = CountingUtils.initialFeatureScore(A_S0, A_S1, B_S0, B_S1, U_S0, U_S1, A_N, B_N, AWeight, BWeight,
					UWeight, ID);

			System.out.println("\t\tq_s is " + q_s + " while theta is " + theta + ", and currentBranchScore="
					+ currentBranchScore);
			isRelevant = q_s > theta && q_s > currentBranchScore; // only if we beat the more general, smaller, subgraph
																	// of this particular subgraph, then we add it.

			if (q_s > theta && q_s <= currentBranchScore) {
				System.out.println("Reject due to similar score as subgraph");
			}
		}

		if (isRelevant) {

			// if adding the new feature will cause this to be bigger
			if (selectedSubgraphFeatures.size() == numberOfFeatures) {
				// drop weakest feature
				long toDrop = -100;
				double toDropValue = Integer.MAX_VALUE;
				for (Entry<Long, Double> subgraphEntry : selectedSubgraphFeatures.entrySet()) {
					if (subgraphEntry.getValue() < toDropValue) {
						toDrop = subgraphEntry.getKey();
						toDropValue = subgraphEntry.getValue();
						continue;
					}
				}
				if (toDrop == -100) {
					throw new RuntimeException("can't find toDrop=" + toDrop + " and currently theta=" + theta);
				}
				selectedSubgraphFeatures.remove(toDrop);
				// also clean up the coverage. Don't need information about this subgraph
				// anymore
				if (!coverage.containsKey(toDrop)) {
					throw new RuntimeException("missing toDrop in coverage=" + toDrop);
				}
				coverage.remove(toDrop);

				if (!(selectedSubgraphFeatures.size() == numberOfFeatures - 1)) {
					throw new RuntimeException("Unexpected size");
				}
			}

			// set new value of theta, which is the minimal quality value among the selected
			// (so far) subgraphs
			if (selectedSubgraphFeatures.size() == numberOfFeatures - 1) {
				theta = q_s;
				for (Entry<Long, Double> subgraphEntry : selectedSubgraphFeatures.entrySet()) {
					theta = Math.min(theta, subgraphEntry.getValue());
				}
			} else {
				theta = 0;
			}

			// set theta is equals to 0 if we want all the good subgraphs.

			if (selectedSubgraphFeatures.containsKey(ID)) {
				throw new RuntimeException(
						"iterating into the same subgraph ID again!/Reusing an existing subgraph ID " + ID);
			}

			selectedSubgraphFeatures.put(ID, q_s);

			if (selectedSubgraphFeatures.size() != coverage.size()) {
				System.out.println("Just inserted " + ID);
				System.out.println("selectedSubgraphFeatures.size()= " + selectedSubgraphFeatures.size());
				System.out.println("coverage.size()= " + coverage.size());

				Set<Long> missing = selectedSubgraphFeatures.keySet();
				missing.removeAll(coverage.keySet());
				System.out.println("missing= " + missing);

				throw new RuntimeException("Unexpected coverage vs selectedSubgraphFeatures size");
			}

			System.out.println("\t..: ID=" + ID + " , q_s=" + q_s);
			System.out.print("\t.... A_S0=" + A_S0 + " , A_S1=" + A_S1);
			System.out
					.println("\t.... " + "B_S0=" + B_S0 + " , B_S1=" + B_S1 + " ,..  U_S0=" + U_S0 + " , U_S1=" + U_S1);
			System.out.println("=");
		} else {
			// not interesting enough. No need to keep coverage info
			coverage.remove(ID);
		}

		if (originalSize > selectedSubgraphFeatures.size()) {
			throw new RuntimeException("the subgraph vector shrank!");
		}
		return q_s;
	}

	private void resetCountsOfLabels() {
		countsOfLabels.put(GRAPH_LABEL.MISUSE, 0);
		countsOfLabels.put(GRAPH_LABEL.CORRECT_USE, 0);
		countsOfLabels.put(GRAPH_LABEL.UNLABELED, 0);
	}

	// HJ: "support" isn't exaclty the number of graphs anymore, but now its the
	// number of projects
	private int support(Projected projected) {
		int oid = 0xffffffff;
		int size = 0;

		for (PDFS cur : projected) {
			if (oid != cur.id) {
				// increase freq
				++size;

				// now update the `counts` map
				boolean isMisuse = misuses.contains(cur.id);
				boolean isCorrectUse = correctUses.contains(cur.id);

				if (isMisuse && isCorrectUse) {
					throw new RuntimeException("invalid label!");
				}
				coverage.putIfAbsent(ID, new HashSet<>());
				unlabeledCoverage.putIfAbsent(ID, new HashSet<>());

				if (isMisuse) {
					countsOfLabels.put(GRAPH_LABEL.MISUSE, countsOfLabels.get(GRAPH_LABEL.MISUSE)
//							+ 1); 
							+ Math.min(TRANS.get(cur.id).quantity, maxGraphCount));

					if (countsOfLabels.get(GRAPH_LABEL.MISUSE) > totalMisuses) {
						throw new RuntimeException("invalid MISUSE counts");
					}

//					System.out.println("putting into coverage=" + ID);
					coverage.get(ID).add(cur.id);
				} else if (isCorrectUse) {
					countsOfLabels.put(GRAPH_LABEL.CORRECT_USE, countsOfLabels.get(GRAPH_LABEL.CORRECT_USE)
//							+ 1); 
							+ Math.min(TRANS.get(cur.id).quantity, maxGraphCount));
//					System.out.println("putting into coverage=" + ID);
					if (countsOfLabels.get(GRAPH_LABEL.CORRECT_USE) > totalCorrectUses) {
						throw new RuntimeException("invalid CORRECT_USE counts");
					}

					coverage.get(ID).add(cur.id);
				} else { // unlabeled
					countsOfLabels.put(GRAPH_LABEL.UNLABELED, countsOfLabels.get(GRAPH_LABEL.UNLABELED) +
//							1);
							Math.min(TRANS.get(cur.id).quantity, maxGraphCount));

					if (countsOfLabels.get(GRAPH_LABEL.UNLABELED) > totalUnlabeled) {
						throw new RuntimeException("invalid UNLABELED counts");
					}
					unlabeledCoverage.get(ID).add(cur.id);
				}

			}
			oid = cur.id;
		}

		return size;
	}

	private boolean isMin() {
		if (DFS_CODE.size() == 1)
			return (true);

		DFS_CODE.toGraph(GRAPH_IS_MIN);
		DFS_CODE_IS_MIN.clear();

		NavigableMap<Integer, NavigableMap<Integer, NavigableMap<Integer, Projected>>> root = new TreeMap<>();
		ArrayList<Edge> edges = new ArrayList<>();

		// HJ: I think this constructs all possible graphs from the vertices in the
		// current dfs code.
		// i.e. all possible `Projected`s goes into root_3
		for (int from = 0; from < GRAPH_IS_MIN.size(); ++from)
			if (Misc.getForwardRoot(GRAPH_IS_MIN, GRAPH_IS_MIN.get(from), edges))
				for (Edge it : edges) {
					int key_1 = GRAPH_IS_MIN.get(from).label;
					NavigableMap<Integer, NavigableMap<Integer, Projected>> root_1 = root.computeIfAbsent(key_1,
							k -> new TreeMap<>());
					int key_2 = it.eLabel;
					NavigableMap<Integer, Projected> root_2 = root_1.computeIfAbsent(key_2, k -> new TreeMap<>());
					int key_3 = GRAPH_IS_MIN.get(it.to).label;
					Projected root_3 = root_2.get(key_3);
					if (root_3 == null) {
						root_3 = new Projected();
						root_2.put(key_3, root_3);
					}
					root_3.push(0, it, null);
				}

		Entry<Integer, NavigableMap<Integer, NavigableMap<Integer, Projected>>> fromLabel = root.firstEntry();
		Entry<Integer, NavigableMap<Integer, Projected>> eLabel = fromLabel.getValue().firstEntry();
		Entry<Integer, Projected> toLabel = eLabel.getValue().firstEntry();

		DFS_CODE_IS_MIN.push(0, 1, fromLabel.getKey(), eLabel.getKey(), toLabel.getKey());

		return isMinProject(toLabel.getValue());
	}

	private boolean isMinProject(Projected projected) {
		// the idea here is to compare is DFS_CODE compares to DFS_CODE_IS_MIN, which is
		// the canonical path
		// that we recursely construct
		ArrayList<Integer> rmPath = DFS_CODE_IS_MIN.buildRMPath();
		int minLabel = DFS_CODE_IS_MIN.get(0).fromLabel;
		int maxToc = DFS_CODE_IS_MIN.get(rmPath.get(0)).to; // right-most vertex

		{
			NavigableMap<Integer, Projected> root = new TreeMap<>();
			boolean flg = false;
			int newTo = 0;

			for (int i = rmPath.size() - 1; !flg && i >= 1; --i) {
				for (PDFS cur : projected) {
					EfficientHistory history = new EfficientHistory(GRAPH_IS_MIN, cur); // history allows us to easily
																						// determine if a
					// vertex or edge is already part of the
					// projected graph
					Edge e = Misc.getBackward(GRAPH_IS_MIN, history.ordering.get(rmPath.get(i)),
							history.ordering.get(rmPath.get(0)), history, singleVertexLabel, minSup);
					if (e != null) {
						int key_1 = e.eLabel;
						Projected root_1 = root.get(key_1);
						if (root_1 == null) {
							root_1 = new Projected();
							root.put(key_1, root_1);
						}
						root_1.push(0, e, cur);
						newTo = DFS_CODE_IS_MIN.get(rmPath.get(i)).from;
						flg = true;
					}
				}
			}

			if (flg) {
				Entry<Integer, Projected> eLabel = root.firstEntry();
				DFS_CODE_IS_MIN.push(maxToc, newTo, -1, eLabel.getKey(), -1);
				if (DFS_CODE.get(DFS_CODE_IS_MIN.size() - 1).notEqual(DFS_CODE_IS_MIN.get(DFS_CODE_IS_MIN.size() - 1)))
					return false;
				return isMinProject(eLabel.getValue());
			}
		}

		{
			boolean flg = false;
			int newFrom = 0;
			NavigableMap<Integer, NavigableMap<Integer, Projected>> root = new TreeMap<>();
			ArrayList<Edge> edges = new ArrayList<>();

			for (PDFS cur : projected) {
				EfficientHistory history = new EfficientHistory(GRAPH_IS_MIN, cur);
				if (Misc.getForwardPure(GRAPH_IS_MIN, history.ordering.get(rmPath.get(0)), minLabel, history, edges,
						singleVertexLabel, minSup)) {
					flg = true;
					newFrom = maxToc;
					for (Edge it : edges) {
						int key_1 = it.eLabel;
						NavigableMap<Integer, Projected> root_1 = root.computeIfAbsent(key_1, k -> new TreeMap<>());
						int key_2 = GRAPH_IS_MIN.get(it.to).label;
						Projected root_2 = root_1.get(key_2);
						if (root_2 == null) {
							root_2 = new Projected();
							root_1.put(key_2, root_2);
						}
						root_2.push(0, it, cur);
					}
				}
			}

			for (int i = 0; !flg && i < rmPath.size(); ++i) {
				for (PDFS cur : projected) {
					EfficientHistory history = new EfficientHistory(GRAPH_IS_MIN, cur);
					if (Misc.getForwardRmPath(GRAPH_IS_MIN, history.ordering.get(rmPath.get(i)), minLabel, history,
							edges, singleVertexLabel, minSup)) {
						flg = true;
						newFrom = DFS_CODE_IS_MIN.get(rmPath.get(i)).from;
						for (Edge it : edges) {
							int key_1 = it.eLabel;
							NavigableMap<Integer, Projected> root_1 = root.computeIfAbsent(key_1, k -> new TreeMap<>());
							int key_2 = GRAPH_IS_MIN.get(it.to).label;
							Projected root_2 = root_1.get(key_2);
							if (root_2 == null) {
								root_2 = new Projected();
								root_1.put(key_2, root_2);
							}
							root_2.push(0, it, cur);
						}
					}
				}
			}

			if (flg) {
				Entry<Integer, NavigableMap<Integer, Projected>> eLabel = root.firstEntry();
				Entry<Integer, Projected> toLabel = eLabel.getValue().firstEntry();
				DFS_CODE_IS_MIN.push(newFrom, maxToc + 1, -1, eLabel.getKey(), toLabel.getKey());
				if (DFS_CODE.get(DFS_CODE_IS_MIN.size() - 1).notEqual(DFS_CODE_IS_MIN.get(DFS_CODE_IS_MIN.size() - 1)))
					return false;
				return isMinProject(toLabel.getValue());
			}
		}

		return true;
	}
}
