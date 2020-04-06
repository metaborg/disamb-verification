package com.github.metaborg.disamb_verification;

public class Main {

    public static void main(String[] args) {
	    TreeGenerator treeGenerator = new TreeGenerator(5);
	    while (treeGenerator.hasNext()) {
            System.out.println(treeGenerator.next());
        }
    }
}
