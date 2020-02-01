package io.github.tonyzzx.gspan;

import org.apache.commons.cli.*;

import smu.hongjin.CountingUtils;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.Scanner;
import java.util.Set;

public class Main {

	public static void main(String[] args) throws IOException {
		Arguments arguments = Arguments.getInstance(args);
		System.out.println("args: " + Arrays.toString(args));

		File inFile = new File(arguments.inFilePath);
		File outFile = new File(arguments.outFilePath);
		try (FileReader reader = new FileReader(inFile)) {
			try (FileWriter writer = new FileWriter(outFile)) {
				gSpan gSpan = new gSpan();
				System.out.println("gSpan is mining...");
				gSpan.run(reader, writer, arguments.minSup, arguments.maxNodeNum, arguments.minNodeNum);

				System.out.println("It's done! The result is in  " + arguments.outFilePath + " .");

				postprocess(arguments, gSpan);
			}
		}

	}

	private static void postprocess(Arguments arguments, gSpan gSpan) throws IOException {
		
		List<Integer> graphs = new ArrayList<>();
//		for (Entry<Long, Set<Integer>> entry : gSpan.coverage.entrySet()) {
//			graphs.addAll(entry.getValue());
//		}
		graphs.addAll(gSpan.correctUses);
		graphs.addAll(gSpan.misuses);
		
		Map<Integer, Set<Long>> graphsToFeaturesContained = new HashMap<>();
		
		for (int graph : graphs) {
			graphsToFeaturesContained.putIfAbsent(graph, new HashSet<>());
		}
		
		System.out.println("graphs sz " + graphs.size()); // graphs are different!!

		Map<Long, Double> sortedSubgraphFeatures = gSpan.selectedSubgraphFeatures.entrySet().stream()
				.sorted(Entry.comparingByValue(Comparator.reverseOrder()))
//				.sorted(Entry.comparingByValue())
				.collect(Collectors.toMap(Entry::getKey, Entry::getValue, (e1, e2) -> e1, LinkedHashMap::new));



		
		Set<Long> weakSubgraphFeatures = new HashSet<>();
		
		int previousCorkScore = Integer.MAX_VALUE;
		for (Map.Entry<Long, Double> entry : sortedSubgraphFeatures.entrySet()) {
			Long featureId = entry.getKey();

			Set<Integer> subgraphCovers = new HashSet<>(gSpan.coverage.get(featureId));
			
			for (Integer graph : subgraphCovers) {
				graphsToFeaturesContained.get(graph).add(featureId);
			}
			
			// see if the number of graphs that cannot be disambiguated has decreased?
			// if so, the subgraph is not weak
			// otherwise, drop this subgraph
			
			int corkScore = 0;
			
			
			for (int i = 0; i < graphs.size(); i++) {
				int graph1 = graphs.get(i);
				Set<Long> features1 = graphsToFeaturesContained.get(graph1);
				boolean isMisuse1 = gSpan.misuses.contains(graph1);

				for (int j = i + 1; j < graphs.size(); j++) {
					int graph2 = graphs.get(j);
					
					boolean isMisuse2 = gSpan.misuses.contains(graph2);
					
					if (isMisuse1 == isMisuse2) {
						continue;
					}
					
					Set<Long> intersection = new HashSet<>(graphsToFeaturesContained.get(graph2));
					intersection.retainAll(features1);
					
					if (intersection.size() == features1.size()) { // cannot disambiguate
						corkScore += 1;
					}
				}
			}
			
			boolean isWeak = true;
			if (corkScore < previousCorkScore) {
				isWeak = false;
			}
			previousCorkScore = corkScore;

			System.out.println(featureId + " - CORK score now=" + corkScore);
			if (isWeak) {
				System.out.println("\t" + featureId + " is getting dropped");
				weakSubgraphFeatures.add(featureId);
				
				for (Integer graph : subgraphCovers) {
					graphsToFeaturesContained.get(graph).remove(featureId); // shouldn't matter, but let's remove anyway
				}
			}
		}

		// remove the lame features
		for (long weakFeature : weakSubgraphFeatures) {
			gSpan.selectedSubgraphFeatures.remove(weakFeature);
			gSpan.coverage.remove(weakFeature);
		}

		try (BufferedWriter selectedSubGraphWriter = new BufferedWriter(
				new FileWriter(arguments.outFilePath + "_best_subgraphs.txt"))) {
			for (Map.Entry<Long, Double> subgraphFeature : sortedSubgraphFeatures.entrySet()) {
				if (!gSpan.coverage.containsKey(subgraphFeature.getKey())) {
					if (!weakSubgraphFeatures.contains(subgraphFeature.getKey())) {
						throw new RuntimeException("huhhh");
					}
					continue; // we have removed this weak feature
				}
				selectedSubGraphWriter.write(subgraphFeature.getKey() + "," + subgraphFeature.getValue());
				selectedSubGraphWriter.write("\n");
			}
		}

		// print subgraph features
		System.out.println(
				"The identified discriminative subgraphs are in  " + arguments.outFilePath + "_best_subgraphs.txt");
		try (BufferedWriter featuresWriter = new BufferedWriter(
				new FileWriter(arguments.outFilePath + "_features.txt"))) {
			CountingUtils.writeGraphFeatures(gSpan, gSpan.coverage, sortedSubgraphFeatures, featuresWriter);
		}
		System.out.println("The feature vectors of labeled graphs are in " + arguments.outFilePath + "_features.txt");

//		try (BufferedWriter featuresWriter = new BufferedWriter(
//				new FileWriter(arguments.outFilePath + "_unlabelled_features.txt"))) {
//			CountingUtils.writeUnlabelledGraphFeatures(gSpan, gSpan.coverage, gSpan.unlabeledCoverage, featuresWriter);
//		}
//		System.out.println(
//				"The feature vectors of unlabeled graphs are in " + arguments.outFilePath + "_unlabelled_features.txt");

		// find new examples to label
		System.out.println("Computing which unlabeled graphs were not covered");
		System.out.println("\tand which labeled graphs were not covered");
		gSpan.uncoveredLabeledGraphs = new HashSet<>(gSpan.misuses); // init with all labeled graphs
		gSpan.uncoveredLabeledGraphs.addAll(gSpan.correctUses);
		for (Long feature : gSpan.selectedSubgraphFeatures.keySet()) {
			Set<Integer> coveredGraphs = gSpan.unlabeledCoverage.get(feature);
			gSpan.uncoveredUnlabeledGraphs.removeAll(coveredGraphs);

			gSpan.uncoveredLabeledGraphs.removeAll(gSpan.coverage.get(feature));
		}

		int countAlreadyLabeledVanillas = gSpan.uncoveredLabeledGraphs.size();

		Set<Integer> vanillaGraphs = new HashSet<>();
		if (countAlreadyLabeledVanillas < 15) {

			// set of graphs that not covered, even by the frequent subgraphs in U
			vanillaGraphs.addAll(gSpan.uncoveredUnlabeledGraphs); // first init to graphs in U that are
																	// uncovered by the chosen subgraph features

			// remove from vanillaGraphs, the other graphs that are covered by
			// frequentUnlabelledSubgraphs
			for (long frequentInUSubgraph : gSpan.frequentUnlabelledSubgraphs) {
				Set<Integer> coveredGraphs = gSpan.unlabeledCoverage.get(frequentInUSubgraph);
				vanillaGraphs.removeAll(coveredGraphs);
			}
		} else {
			System.out.println("no need for vanillas");
		}

		int minimumToLabel = Math.max(3,
				CountingUtils.minimumCountForSignificanceMinority(gSpan.totalCorrectUses, gSpan.totalMisuses));
		try (BufferedWriter unlabeledNeedsLabelsWriter = new BufferedWriter(
				new FileWriter(arguments.outFilePath + "_interesting_unlabeled.txt"))) {
//            		int totalExamples = gSpan.totalCorrectUses + gSpan.totalMisuses + gSpan.totalUnlabeled;
//            		int onePercent = Math.floorDiv(totalExamples, 100);
//            		int pointFivePercent = onePercent / 2;
//            		int pointTwoFivepercent = pointFivePercent / 2;

			System.out.println("\t" + "# uncoveredUnlabeledGraphs: " + gSpan.uncoveredUnlabeledGraphs.size());

			List<Integer> top = gSpan.usefulGeneralUnlabelledGraphs.values().stream()
					.filter(item -> !gSpan.uncoveredUnlabeledGraphs.contains(item)).sorted(Collections.reverseOrder())
					.collect(Collectors.toList());

			System.out.println("\t" + "hits on U - usefulGeneralUnlabelledGraphs");
			System.out.println("\t" + "# usefulGeneralUnlabelledGraphs: " + gSpan.usefulGeneralUnlabelledGraphs.size());
			System.out.println("\t\t" + top.subList(0, Math.min(top.size(), 50)));

			int writingCount = 0;
			for (Entry<Integer, Integer> entry : gSpan.usefulGeneralUnlabelledGraphs.entrySet()) {
				Integer graphId = entry.getKey();
				if (!gSpan.uncoveredUnlabeledGraphs.contains(graphId)) {
					continue;
				}

				// giving us the intersection of
				// 1. graphs that the current set of labels do not cover
				// 2. graphs containing many motifs
//				if (top.size() <= 50 || entry.getValue() > top.get(50)) {
//					unlabeledNeedsLabelsWriter.write(entry.getKey() + "\n");
//					writingCount += 1;
//				}
				if (writingCount > 50) {
					break;
				}
			}
			System.out.println("\t\t\tWritten " + writingCount + " for general unlabelled subgraphs");

			top = gSpan.usefulSpecificUnlabelledGraphs.values().stream()
//        					.filter(item -> !gSpan.uncoveredUnlabeledGraphs.contains(item))
					.sorted(Collections.reverseOrder()).collect(Collectors.toList());
			System.out.println("\thits on U - usefulSpecificUnlabelledGraphs");
			System.out
					.println("\t" + "# usefulSpecificUnlabelledGraphs: " + gSpan.usefulSpecificUnlabelledGraphs.size());
			System.out.println("\t\t" + top.subList(0, Math.min(top.size(), 100)));
			for (Entry<Integer, Integer> entry : gSpan.usefulSpecificUnlabelledGraphs.entrySet()) {
				Integer graphId = entry.getKey();
//        				if (!gSpan.uncoveredUnlabeledGraphs.contains(graphId)) {
//        					continue;
//        				}
//        				
				// giving us the intersection of
				// 1. graphs that the current set of labels do not cover
				// 2. graphs containing many motifs
//				if ((top.size() <= minimumToLabel || entry.getValue() > top.get(minimumToLabel))) {
//					unlabeledNeedsLabelsWriter.write(entry.getKey() + "\n");
//					writingCount += 1;
//				} else if (entry.getValue() < top.get(Math.max(0, top.size() - minimumToLabel))) {
//					unlabeledNeedsLabelsWriter.write(entry.getKey() + "\n");
//					writingCount += 1;
//				}
			}
			System.out.println(
					"\t\t\tWritten " + writingCount + " (accumulative count) for specific unlabelled subgraphs");

			for (Entry<Integer, Integer> entry : gSpan.subgraphForDoubleCheckingUnlabelledGraphs.entrySet()) {
				Integer graphId = entry.getKey();
//        				if (!gSpan.uncoveredUnlabeledGraphs.contains(graphId)) {
//        					continue;
//        				}
//        				
				
//				unlabeledNeedsLabelsWriter.write(entry.getKey() + "\n");
//				writingCount += 1;

			}

			System.out.println(
					"\t\t\tWritten " + writingCount + " (accumulative count) for graph-for-double-checking subgraphs");

			Map<Integer, Integer> graphsForSubgraphsNeedMoreEvidence = gSpan.graphsForSubgraphsNeedMoreEvidence
					.entrySet().stream().sorted(Entry.comparingByValue())
					.collect(Collectors.toMap(Entry::getKey, Entry::getValue, (e1, e2) -> e1, LinkedHashMap::new));
			int needMoreEvidenceCount = 0;
			for (int needMoreEvidenceGraph : graphsForSubgraphsNeedMoreEvidence.keySet()) {
				if (needMoreEvidenceCount > 30) {
					break;
				}
//				unlabeledNeedsLabelsWriter.write(needMoreEvidenceGraph + "\n");
//				writingCount += 1;
				needMoreEvidenceCount += 1;
			}
			System.out.println("\t\t\tWritten " + writingCount
					+ " (accumulative count) for subgraphs that may benefit from more evidence");

			int vanillaGraphCount = 0;
			for (int needMoreEvidenceGraph : vanillaGraphs) {
				unlabeledNeedsLabelsWriter.write(needMoreEvidenceGraph + "\n");
				writingCount += 1;
				vanillaGraphCount += 1;
				if (vanillaGraphCount > 10) {
					break;
				}
			}
			System.out.println("\t\t\tWritten " + writingCount + " (accumulative count) for vanilla graphs");

		}
		
		writeClingo(arguments, gSpan);

		

		System.out.println("The IDs of the uncovered methods have been written to " + arguments.outFilePath
				+ "_interesting_unlabeled.txt");
		System.out.println("The prefixes of the files we care about are " + arguments.outFilePath);
	}

	private static void writeClingo(Arguments arguments, gSpan gSpan) throws IOException {
		System.out.println("writing clingo to " + arguments.outFilePath + "_interesting_subgraphs_coverage.txt");
		try (BufferedWriter selectedSubGraphWriter = new BufferedWriter(
				new FileWriter(arguments.outFilePath + "_interesting_subgraphs_coverage.txt"))) {
			
			selectedSubGraphWriter.write("#const n=" + gSpan.minimumToLabel + ".\n");
			selectedSubGraphWriter.write("#const s=" + (gSpan.totalCorrectUses + gSpan.totalMisuses + gSpan.totalUnlabeled) / 200 + ".\n");
			
			Set<Integer> graphs = new HashSet<>();
			
			
			for (Set<Integer> graphs1 : gSpan.unlabeledCoverage.values()) {
				graphs.addAll(graphs1);
			}
			graphs.retainAll(gSpan.uncoveredUnlabeledGraphs);
			
			for (int graph : graphs) {
				selectedSubGraphWriter.write("graph(" + graph + ")" + ".\n");
			}
			for (long subgraph: gSpan.unlabeledCoverage.keySet()) {
				selectedSubGraphWriter.write("subgraph(" + subgraph + ")" + ".\n");
			}
			
			Map<Long, Integer> countsOfSubgraphs = new HashMap<>();
			for (long interestingSubgraph : gSpan.interestingSubgraphs ) {
				if (gSpan.unlabeledCoverage.get(interestingSubgraph).size() < gSpan.minimumToLabel) {
					continue;
				}
				countsOfSubgraphs.put(interestingSubgraph, gSpan.unlabeledCoverage.get(interestingSubgraph).size());			
			}
			List<Long> top = countsOfSubgraphs.entrySet().stream()
				.sorted(Entry.comparingByValue(Comparator.reverseOrder()))
//				.limit(countsOfSubgraphs.entrySet().size() / 2) 	// 
				.map(entry -> entry.getKey())
				.collect(Collectors.toList());
			
			
			for (long interestingSubgraph : top) {
				
				for (int graph : gSpan.unlabeledCoverage.get(interestingSubgraph)) {
					if (graphs.contains(graph )) {
						selectedSubGraphWriter.write("covers(" + graph + "," + interestingSubgraph + ")" + ".\n");
					}
				}
				
			}
			
			selectedSubGraphWriter.write("{ selected(G) : graph(G) } <= 1 :- graph(G).\n");


			selectedSubGraphWriter.write("sufficiently_covered(SG) :- #count { G : selected(G), covers(G, SG), graph(G) } >= n, subgraph(SG).\n");

			selectedSubGraphWriter.write(":- { selected(G)} > s .\n");

			selectedSubGraphWriter.write("covered_count(X) :- X = #count {SG : sufficiently_covered(SG), subgraph(SG)}.\n");
			selectedSubGraphWriter.write("num_selected(Y) :- Y =  #count{G : selected(G)}.\n");

			selectedSubGraphWriter.write("#minimize {Y@1 : num_selected(Y)}.\n");
			selectedSubGraphWriter.write("#maximize {X@2 : covered_count(X) }.\n");

			selectedSubGraphWriter.write("#show selected/1.\n");
			selectedSubGraphWriter.write("#show covered_count/1.\n");
			selectedSubGraphWriter.write("#show num_selected/1.\n");
			
		}
	}

	private static class Arguments {
		private static Arguments arguments;

		private String[] args;

		String inFilePath;
		long minSup;
		long minNodeNum = 0;
		long maxNodeNum = Long.MAX_VALUE;
		String outFilePath;

		private Arguments(String[] args) {
			this.args = args;
		}

		static Arguments getInstance(String[] args) {
			arguments = new Arguments(args);
			if (args.length > 0) {
				arguments.initFromCmd();
			} else {
				arguments.initFromRun();
			}
			return arguments;
		}

		/***
		 * User inputs args.
		 */
		private void initFromCmd() {
			Options options = new Options();
			options.addRequiredOption("d", "data", true, "(Required) File path of data set");
			options.addRequiredOption("s", "sup", true, "(Required) Minimum support");
			options.addOption("i", "min-node", true, "Minimum number of nodes for each sub-graph");
			options.addOption("a", "max-node", true, "Maximum number of nodes for each sub-graph");
			options.addOption("r", "result", true, "File path of result");
			options.addOption("h", "help", false, "Help");

			CommandLineParser parser = new DefaultParser();
			HelpFormatter formatter = new HelpFormatter();
			CommandLine cmd = null;
			try {
				cmd = parser.parse(options, args);
				if (cmd.hasOption("h")) {
					formatter.printHelp("gSpan", options);
					System.exit(0);
				}
			} catch (ParseException e) {
				formatter.printHelp("gSpan", options);
				System.exit(1);
			}

			inFilePath = cmd.getOptionValue("d");
			minSup = Long.parseLong(cmd.getOptionValue("s"));
			minNodeNum = Long.parseLong(cmd.getOptionValue("i", "0"));
			maxNodeNum = Long.parseLong(cmd.getOptionValue("a", String.valueOf(Long.MAX_VALUE)));
			outFilePath = cmd.getOptionValue("r", inFilePath.replace(".txt", "") + "_result");
		}

		/***
		 * User runs it directly.
		 */
		private void initFromRun() {
			try (Scanner sc = new Scanner(System.in)) {
				System.out.println("Please input the file path of data set: ");
				inFilePath = sc.nextLine();
				System.out.println("Please set the minimum support: ");
				minSup = sc.nextLong();
				outFilePath = inFilePath + "_result";

				maxNodeNum = 6;
			}
		}
	}
}
