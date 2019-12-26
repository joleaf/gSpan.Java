package smu.hongjin;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Collectors;

public class CountingUtils {

	public static int initialFeatureScore(int A_S0, int A_S1, int B_S0, int B_S1, int U_S0, int U_S1) {
		// first component: from original CORK paper
		// ("Near-optimal supervised feature selection among frequent subgraphs" by
		// Thoma et al.)
		// SIAM International Conference on Data Mining. 2009
		// SIAM is a rank A conference.
		int correspondanceBetweenLabels = -1 * (A_S0 * B_S0 + A_S1 * B_S1);

		// second component: incentize skewedness. The more the unlabeled data shifts to
		// the majority class, the better
		int skewedness = U_S1 * A_S1;

		// third component: penalize unlabeled data that is still unlabeled;
		int lackOfLabels = -1 * U_S0 * U_S0;

		return correspondanceBetweenLabels + skewedness + lackOfLabels;
	}

	public static double upperBound(int q_s, int A_S0, int A_S1, int B_S0, int B_S1, int U_S0, int U_S1) {
		// first component upper bound: from original CORK paper
		// "Near-optimal supervised feature selection among frequent subgraphs" by Thoma
		// et al.
		int maxCorrespondanceIncrease = Math.max(Math.max(A_S1 * (B_S1 - B_S0), B_S1 * (A_S1 - A_S0)), 0);
		
		// second component upper bound: 0
		// both U_S1 and A_S1 cannot increase
		
		// third component upper bound: 0
		// the best case is that U_S0 does not increase. i.e U_S1 does not decrease
		
		// Therefore, in the end, it's the same upper bound computation from the CORK paper
		return q_s + maxCorrespondanceIncrease;
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
}
