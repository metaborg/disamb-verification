package com.github.metaborg.disamb_verification;

import java.util.ArrayList;
import java.util.Set;

public class Main {

    public static void main(String[] args) {
        final int opCount = 4;

        ConflictGenerator conflictGenerator = new ConflictGenerator();
        ArrayList<Set<ConflictPattern>> conflictCombinations =
                new ArrayList<>(conflictGenerator.generateConflicts(opCount));

        ArrayList<Tree> trees = new ArrayList<>();
	    TreeGenerator treeGenerator = new TreeGenerator(opCount);
	    while (treeGenerator.hasNext()) {
            trees.add(treeGenerator.next());
        }

        for (var conflicts : conflictCombinations) {
            System.out.println(conflicts);
            var result = Tree.keepRewritingEverything(trees, conflicts);
            System.out.println(result);
            if (result.size() == 0) {
                System.out.println("INTERESTING TREE!");
                break;
            }
            System.out.println();
        }


    }
}
