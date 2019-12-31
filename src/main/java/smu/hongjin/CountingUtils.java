package smu.hongjin;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import io.github.tonyzzx.gspan.gSpan;

public class CountingUtils {

	public static double initialFeatureScore(int A_S0, int A_S1, int B_S0, int B_S1, int U_S0, int U_S1, double AWeight,
			double BWeight, double UWeight) {
		// first component: from original CORK paper
		// ("Near-optimal supervised feature selection among frequent subgraphs" by
		// Thoma et al.)
		// SIAM International Conference on Data Mining. 2009
		// SIAM is a rank A conference.
		double correspondanceBetweenLabels = -1 * (AWeight * A_S0 * BWeight * B_S0 + AWeight * A_S1 * BWeight * B_S1);

		// second component: incentize skewedness. The more the unlabeled data shifts to
		// the majority class, the better
		// i.e. incentize correspondense between U and A
		double skewedness = UWeight * U_S1 * AWeight * A_S1;
		
		// some U and many of B
		skewedness += UWeight * U_S0 * BWeight * B_S1;
		
		// third component: penalty for unlabeled data that is still unlabeled;
//		double lackOfLabels = -1 * UWeight * U_S0 * UWeight * U_S0;		// 

		return correspondanceBetweenLabels; // + skewedness;
		
		// a feature is good w.r.t. to the misuse distribution if
		// 		1. unlabeled distribution is skewed
		// 		2.  
	}

	public static double upperBound(double q_s, int A_S0, int A_S1, int B_S0, int B_S1, int U_S0, int U_S1,  double AWeight,
			double BWeight, double UWeight) {
		// first component upper bound: from original CORK paper
		// "Near-optimal supervised feature selection among frequent subgraphs" by Thoma
		// et al.
		double maxCorrespondanceIncrease = Math.max(
				Math.max(
						AWeight * A_S1 * (BWeight * (B_S1 - B_S0)), BWeight * B_S1 * (AWeight * (A_S1 - A_S0))), 0);

		// second component upper bound: 
		// both U_S1 and A_S1 cannot increase
		// but the penalty for U and B can decrease.
		// U_S0 can increase, although B_S1 cannot. Thus, the best case is that all of U_S1 becomes U_S0
		double maxSkewIncrease = 0 ;// UWeight * (U_S1) * BWeight * B_S1;
				

		return q_s + maxCorrespondanceIncrease + maxSkewIncrease;
	}

	// actually we don't have to do this for all subgraphs.
	public static Map<Long, Double> findClosestLabelledPointForKUnLabelled2(int k, Set<Long> subgraphIds,
			Map<Long, Set<Long>> misuseSubgraphCoverage, Map<Long, Set<Long>> correctUseSubgraphCoverage,
			Map<Long, Set<Long>> unlabeledGraphsCoverage, Set<Long> allMisuses, Set<Long> allCorrect,
			Set<Long> allUnlabeled) {

		Map<Long, Map<Long, Double>> unlabeledToLabeledDistance = new HashMap<>();
		// OR:
		// for all unlabeled points
		for (long unlabeled : allUnlabeled) {
			if (!unlabeledToLabeledDistance.containsKey(unlabeled)) {
				unlabeledToLabeledDistance.put(unlabeled, new HashMap<>());
			}
			Map<Long, Double> map = unlabeledToLabeledDistance.get(unlabeled);

			iterateLabeledAndCountDistance(subgraphIds, misuseSubgraphCoverage, unlabeledGraphsCoverage, allMisuses,
					unlabeled, map);
			iterateLabeledAndCountDistance(subgraphIds, correctUseSubgraphCoverage, unlabeledGraphsCoverage, allCorrect,
					unlabeled, map);
		}
		// now,
		// unlabeledGraphToLabeledGraphDistance contains a mapping of all unlabeled ->
		// labeled -> value proportional to distance

		List<Map.Entry<Long, Double>> shortest = new ArrayList<>();
		for (Entry<Long, Map<Long, Double>> entry : unlabeledToLabeledDistance.entrySet()) {
			Long unlabelledId = entry.getKey();

			double minDistance = 9999; // for this unlabeled point, the smallest distance to a labeled point
			for (Entry<Long, Double> value : entry.getValue().entrySet()) {
				if (value.getValue() < minDistance) {
					minDistance = value.getValue();
				}
			}

			if (minDistance > shortest.get(k - 1).getValue())
				continue;

			// insert into sorted list
			for (int i = 0; i < k; i++) {
				if (minDistance <= shortest.get(i).getValue()) {
					shortest.add(i, new AbstractMap.SimpleEntry<Long, Double>(unlabelledId, minDistance));

					shortest.remove(shortest.size() - 1);
					break;
				}
			}
		}

		assert shortest.size() == k;
		Map<Long, Double> result = new HashMap<>();
		for (Entry<Long, Double> entry : shortest) {
			result.put(entry.getKey(), Math.sqrt(entry.getValue()));
		}

		return result;
	}

	private static void iterateLabeledAndCountDistance(Set<Long> subgraphIds // the features
			, Map<Long, Set<Long>> labeledSubgraphCoverage // subgraphId -> which graph IDs contain the subgraph
			, Map<Long, Set<Long>> unlabeledGraphsCoverage // subgraphId -> which graph IDs contain the subgraph
			, Set<Long> labeledGraphIds // labeled graph IDS
			, long unlabeled, Map<Long, Double> map) {

		for (long labeled : labeledGraphIds) {
			if (!map.containsKey(labeled))
				map.put(labeled, 0.0);

			for (long subgraphId : subgraphIds) {
				boolean isSubgraphInUnlabelled = unlabeledGraphsCoverage.get(subgraphId).contains(unlabeled);
				boolean isSubgraphInLabelled = labeledSubgraphCoverage.get(subgraphId).contains(labeled);
				if (isSubgraphInUnlabelled != isSubgraphInLabelled) {
					// increase distance,
					map.put(labeled, map.get(labeled) + 1.0);
				}
			}
		}
	}

	public static Map<Long, Double> findClosestLabelledPointForKUnLabelled(int k, Set<Long> subgraphIds,
			Map<Long, Set<Long>> misuseSubgraphCoverage, Map<Long, Set<Long>> correctUseSubgraphCoverage,
			Map<Long, Set<Long>> unlabeledGraphsCoverage) {

		Map<Long, Map<Long, Double>> unlabeledGraphToLabeledGraphDistance = new HashMap<>();
		for (long subgraphId : subgraphIds) {
			// iterate all unlabeledGraphs
			for (long unlabeledGraph : unlabeledGraphsCoverage.get(subgraphId)) {
				// in each unlabeled graph
				// find distance to all misuseGraphs and correctUsageGraphs

				if (!unlabeledGraphToLabeledGraphDistance.containsKey(unlabeledGraph)) {
					unlabeledGraphToLabeledGraphDistance.put(unlabeledGraph, new HashMap<>());
				}
				for (long labeledGraph : misuseSubgraphCoverage.get(subgraphId)) {
					Map<Long, Double> map = unlabeledGraphToLabeledGraphDistance.get(unlabeledGraph);
					if (!map.containsKey(labeledGraph)) {
						map.put(labeledGraph, 0.0);
					}
					map.put(labeledGraph, map.get(labeledGraph) + 1.0); // TODO not correct
				}

				for (long labeledGraph : correctUseSubgraphCoverage.get(subgraphId)) {
					Map<Long, Double> map = unlabeledGraphToLabeledGraphDistance.get(unlabeledGraph);
					if (!map.containsKey(labeledGraph)) {
						map.put(labeledGraph, 0.0);
					}
					map.put(labeledGraph, map.get(labeledGraph) + 1.0); // TODO not correct
				}
			}
		}

		List<Map.Entry<Long, Double>> shortest = new ArrayList<>();
		for (Entry<Long, Map<Long, Double>> entry : unlabeledGraphToLabeledGraphDistance.entrySet()) {
			Long unlabelledId = entry.getKey();
			double minDistance = 9999;
			for (Entry<Long, Double> value : entry.getValue().entrySet()) {
				if (value.getValue() < minDistance) {
					minDistance = value.getValue();
				}
			}

			if (minDistance > shortest.get(k - 1).getValue())
				continue;

			// insert into sorted list
			for (int i = 0; i < k; i++) {
				if (minDistance <= shortest.get(i).getValue()) {
					shortest.add(i, new AbstractMap.SimpleEntry<Long, Double>(unlabelledId, minDistance));

					shortest.remove(shortest.size() - 1);
					break;
				}
			}
		}

		assert shortest.size() == k;
		Map<Long, Double> result = new HashMap<>();
		for (Entry<Long, Double> entry : shortest) {
			result.put(entry.getKey(), entry.getValue());
		}

		return result;
	}

	public static void writeGraphFeatures(gSpan gSpan, Map<Long, Set<Integer>> coverage, BufferedWriter writer) throws IOException {
		System.out.println("\tConsolidating and writing graph and their subgraph features");
		
		if (coverage.size() != gSpan.selectedSubgraphFeatures.size()) {
			throw new RuntimeException("wrong size!");
		}
		
		List<Integer> graphs = new ArrayList<>();
		for (Entry<Long, Set<Integer>> entry : coverage.entrySet()) {
			graphs.addAll(entry.getValue());
		}
		List<Long> features = coverage.keySet().stream().sorted().collect(Collectors.toList());

		writer.write("graph_id,is_correct");
		for (Long feature : features) {
			writer.write(",feature_" + feature);
		}
		writer.write("\n");
		
		// <graph id>, feature_1, feature_2, feature_3, ... \n
		for (Integer graph : graphs) {
			writer.write(graph + ",");
			
			if (gSpan.correctUses.contains(graph)) {
				writer.write("1");
			} else if (gSpan.misuses.contains(graph)) {
				writer.write("0");
			} else {
				throw new RuntimeException("graph label is incorrect somehow " + graph);
			}
			
			for (Long feature : features) {
				if (coverage.get(feature).contains(graph)) {
					writer.write(",1");
				} else {
					writer.write(",0");
				}
			}
			writer.write("\n");
		}

		System.out.println("\tCompleted consolidation and writing");
	}

}
