package io.github.tonyzzx.gspan.model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

public class EfficientHistory extends ArrayList<Edge> {
    private static final long serialVersionUID = 1L;
    private Set<Integer> edge;
    private Set<Integer> vertex;

    public EfficientHistory(Graph g, PDFS p) {
//    	System.out.println("\t\tConstructing EfficientHistory : " + g.edge_size + ", " + g.size());
        edge = new HashSet<>(g.edge_size + 1, 1.0f);
        vertex = new HashSet<>(g.size() + 1, 1.0f);
        build(g, p);
    }

    private void build(Graph graph, PDFS e) {
        // first build history
        clear();
        edge.clear();
//        edge.setSize(graph.edge_size);
        vertex.clear();
//        vertex.setSize(graph.size());

        int howDeepDoesEGo = 0;
        
        if (e != null) {
            add(e.edge);
            edge.add(e.edge.id);
            howDeepDoesEGo += 1;
            if (howDeepDoesEGo >= graph.edge_size * 0.8) {
            	System.out.println("\t\thowDeepDoesEGo:" + howDeepDoesEGo);
            }
            
            vertex.add(e.edge.from);
            vertex.add(e.edge.to);

            for (PDFS p = e.prev; p != null; p = p.prev) {
                add(p.edge); // this line eats 8% of overall instructions(!)
                edge.add(p.edge.id);
                howDeepDoesEGo += 1;
                if (howDeepDoesEGo >= graph.edge_size * 0.8) {
                	System.out.println("\t\thowDeepDoesEGo:" + howDeepDoesEGo);
                }
                
                
                vertex.add(p.edge.from);
                vertex.add(p.edge.to);
            }
            Collections.reverse(this);
        }
    }

    public boolean hasEdge(int id) {
        return edge.contains(id);
    }

    public boolean hasVertex(int id) {
        return vertex.contains(id);
    }
}
