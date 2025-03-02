package io.github.tonyzzx.gspan.model;

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

public class Graph extends ArrayList<Vertex> {
    private static final long serialVersionUID = 1L;
    int edge_size = 0;
    boolean directed = false;

    public Graph() {
    }

    public Graph(boolean directed) {
        this.directed = directed;
    }

    public void buildEdge() {
        String buf;
        NavigableMap<String, Integer> tmp = new TreeMap<>();

        int id = 0;
        for (int from = 0; from < size(); ++from) {
            for (Edge it : this.get(from).edge) {
                if (directed || from <= it.to)
                    buf = from + " " + it.to + " " + it.eLabel;
                else
                    buf = it.to + " " + from + " " + it.eLabel;

                // Assign unique id's for the edges.
                if (tmp.get(buf) == null) {
                    it.id = id;
                    tmp.put(buf, id);
                    ++id;
                } else {
                    it.id = tmp.get(buf);
                }
            }
        }

        edge_size = id;
    }

    public void write(FileWriter os) throws IOException {
        String buf;
        // Sort the result of edges.
        NavigableSet<String> tmp = new TreeSet<>((o1, o2) -> {
            String[] split1 = o1.split(" ");
            String[] split2 = o2.split(" ");
            if (Integer.parseInt(split1[0]) == Integer.parseInt(split2[0])) {
                if (Integer.parseInt(split1[1]) == Integer.parseInt(split2[1])) {
                    return Integer.parseInt(split1[2]) - Integer.parseInt(split2[2]);
                } else {
                    return Integer.parseInt(split1[1]) - Integer.parseInt(split2[1]);
                }
            } else {
                return Integer.parseInt(split1[0]) - Integer.parseInt(split2[0]);
            }
        });

        for (int from = 0; from < size(); ++from) {
            os.write("v " + from + " " + this.get(from).label + System.getProperty("line.separator"));

            for (Edge it : this.get(from).edge) {
                if (directed || from <= it.to) {
                    buf = from + " " + it.to + " " + it.eLabel;
                } else {
                    buf = it.to + " " + from + " " + it.eLabel;
                }
                tmp.add(buf);
            }
        }

        for (String it : tmp) {
            os.write("e " + it + System.getProperty("line.separator"));
        }

        os.flush();
    }

    public void check() {
        /*
         * Check all indices
         */
        for (int from = 0; from < size(); ++from) {
            System.out.println(
                    "check vertex " + from + ", label " + this.get(from).label + System.getProperty("line.separator"));

            for (Edge it : this.get(from).edge) {
                System.out.println("   check edge from " + it.from + " to " + it.to + ", label " + it.eLabel
                        + System.getProperty("line.separator"));
                assert (it.from >= 0 && it.from < size());
                assert (it.to >= 0 && it.to < size());
            }
        }
    }

    void resize(int size) {
        while (this.size() < size) {
            this.add(new Vertex());
        }
    }
}
