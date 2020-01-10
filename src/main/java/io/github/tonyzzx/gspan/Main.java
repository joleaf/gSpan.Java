package io.github.tonyzzx.gspan;

import org.apache.commons.cli.*;

import smu.hongjin.CountingUtils;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
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
                
                try (BufferedWriter selectedSubGraphWriter = new BufferedWriter(new FileWriter(arguments.outFilePath + "_best_subgraphs.txt"))) {
        			for (Map.Entry<Long, Double> subgraphFeature : gSpan.selectedSubgraphFeatures.entrySet()) {
        				selectedSubGraphWriter.write(subgraphFeature.getKey() + "," + subgraphFeature.getValue());
        				selectedSubGraphWriter.write("\n");
        			}
        		}
                System.out.println("The identified discriminative subgraphs are in  " + arguments.outFilePath + "_best_subgraphs.txt");
            	try(BufferedWriter featuresWriter = new BufferedWriter(new FileWriter(arguments.outFilePath + "_features.txt" ))) {
        			CountingUtils.writeGraphFeatures(gSpan, gSpan.coverage, featuresWriter);
        		}
            	System.out.println("The feature vectors of labeled graphs are in " + arguments.outFilePath + "_features.txt");
            	
            	System.out.println("Computing which unlabeled graphs were not covered");
            	for (Long feature : gSpan.selectedSubgraphFeatures.keySet()) {
            		Set<Integer> coveredGraphs = gSpan.unlabeledCoverage.get(feature);
            		gSpan.uncoveredUnlabeledGraphs.removeAll(coveredGraphs);	
            	}
            	
            	Set<Integer> vanillaGraphs = new HashSet<>(); 			// set of graphs that not covered, even by the frequent subgraphs in U
            	vanillaGraphs.addAll(gSpan.uncoveredUnlabeledGraphs); 	// first init to graphs in U that are uncovered by the chosen subgraph features
            	
            	// remove from vanillaGraphs, the other graphs that are covered by frequentUnlabelledSubgraphs
            	for (long frequentInUSubgraph : gSpan.frequentUnlabelledSubgraphs) {
            		Set<Integer> coveredGraphs = gSpan.unlabeledCoverage.get(frequentInUSubgraph);
            		vanillaGraphs.removeAll(coveredGraphs);
            	}
            	
            	
            	try(BufferedWriter unlabeledNeedsLabelsWriter = new BufferedWriter(new FileWriter(arguments.outFilePath + "_interesting_unlabeled.txt" ))) {
            		int totalExamples = gSpan.totalCorrectUses + gSpan.totalMisuses + gSpan.totalUnlabeled;
            		int onePercent = Math.floorDiv(totalExamples, 100);
            		int pointFivePercent = onePercent / 2;
            		int pointTwoFivepercent = pointFivePercent / 2;
            		
            		System.out.println("\t" + "# uncoveredUnlabeledGraphs: " + gSpan.uncoveredUnlabeledGraphs.size());
            		
            		List<Integer> top = gSpan.usefulGeneralUnlabelledGraphs.values().stream()
            				.filter(item -> !gSpan.uncoveredUnlabeledGraphs.contains(item))
            				.sorted(Collections.reverseOrder()).collect(Collectors.toList());
            		
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
        				if (top.size() <= 50 || entry.getValue() > top.get(50)) {
        					unlabeledNeedsLabelsWriter.write(entry.getKey() + "\n");
        					writingCount += 1;
        				}
        			}
        			System.out.println("\t\t\tWritten " + writingCount + " for general unlabelled subgraphs");
        			
        			top = gSpan.usefulSpecificUnlabelledGraphs.values().stream()
//        					.filter(item -> !gSpan.uncoveredUnlabeledGraphs.contains(item))
        					.sorted(Collections.reverseOrder())
        					.collect(Collectors.toList());
        			System.out.println("\thits on U - usefulSpecificUnlabelledGraphs");
        			System.out.println("\t" + "# usefulSpecificUnlabelledGraphs: " + gSpan.usefulSpecificUnlabelledGraphs.size());
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
        				if ((top.size() <= pointTwoFivepercent || entry.getValue() > top.get(pointTwoFivepercent))) {
        					unlabeledNeedsLabelsWriter.write(entry.getKey() + "\n");
        					writingCount += 1;
        				} 
        				else if (entry.getValue() < top.get(Math.max(0, top.size() - pointTwoFivepercent))) {
        					unlabeledNeedsLabelsWriter.write(entry.getKey() + "\n");
        					writingCount += 1;
        				}
        			}
        			System.out.println("\t\t\tWritten " + writingCount + " (accumulative count) for specific unlabelled subgraphs");
        			
        			
        			for (int needMoreEvidenceGraph : gSpan.graphsForSubgraphsNeedMoreEvidence) {
        				unlabeledNeedsLabelsWriter.write(needMoreEvidenceGraph + "\n");
        				writingCount += 1;
        			}
        			System.out.println("\t\t\tWritten " + writingCount + " (accumulative count) for subgraphs that may benefit from more evidence");
        			
        			
        			
        			for (int needMoreEvidenceGraph : vanillaGraphs) {
        				unlabeledNeedsLabelsWriter.write(needMoreEvidenceGraph + "\n");
        				writingCount += 1;
        			}
        			System.out.println("\t\t\tWritten " + writingCount + " (accumulative count) for vanilla graphs");
        			
        		}
            	
            	System.out.println("The IDs of the uncovered methods have been written to " + arguments.outFilePath + "_interesting_unlabeled.txt");
            }
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
