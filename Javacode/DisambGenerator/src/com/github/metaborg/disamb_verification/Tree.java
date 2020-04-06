package com.github.metaborg.disamb_verification;

import java.util.Collection;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

import static com.github.metaborg.disamb_verification.ConflictType.*;

public class Tree {

    private int op;
    private Tree left;
    private Tree right;

    public Tree(int op, Tree left, Tree right) {
        this.op = op;
        this.left = left;
        this.right = right;
    }

    public static Collection<Tree> keepRewritingEverything(Collection<Tree> trees, Set<ConflictPattern> conflictPatterns) {
        HashSet<Tree> normalForms = new HashSet<>();
        HashSet<Tree> rewrites = new HashSet<>(trees);

        while (!rewrites.isEmpty()) {
            HashSet<Tree> newTrees = new HashSet<>();
            for (Tree tree : rewrites) {
                var possibleSteps = tree.step(conflictPatterns);
                if (possibleSteps.isEmpty()) {
                    normalForms.add(tree);
                }
                newTrees.addAll(possibleSteps);
            }
            newTrees.removeAll(normalForms);
            rewrites = newTrees;
        }

        return normalForms;
    }

    public Collection<Tree> step(Set<ConflictPattern> conflictPatterns) {
        HashSet<Tree> result = new HashSet<>();

        if (left != null) {
            if (conflictPatterns.contains(new ConflictPattern(R2L, op, left.op))) {
                Tree rewrittenTree = leftToRightRewrite();
                result.add(rewrittenTree);
            }
            for (Tree rewrittenTree : left.step(conflictPatterns)) {
                result.add(new Tree(op, rewrittenTree, right));
            }
        }

        if (right != null) {
            if (conflictPatterns.contains(new ConflictPattern(L2R, op, right.op))) {
                Tree rewrittenTree = rightToLeftRewrite();
                result.add(rewrittenTree);
            }
            for (Tree rewrittenTree : right.step(conflictPatterns)) {
                result.add(new Tree(op, left, rewrittenTree));
            }
        }
        return result;
    }

    private Tree leftToRightRewrite() {
        return new Tree(left.op, left.left, new Tree(op, left.right, right));
    }

    private Tree rightToLeftRewrite() {
        return new Tree(right.op, new Tree(op, left, right.left), right.right);
    }

//    public int getOp() {
//        return op;
//    }
//
//    public Tree getLeft() {
//        return left;
//    }
//
//    public Tree getRight() {
//        return right;
//    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Tree tree = (Tree) o;
        return op == tree.op &&
                Objects.equals(left, tree.left) &&
                Objects.equals(right, tree.right);
    }

    @Override
    public int hashCode() {
        return Objects.hash(op, left, right);
    }

    @Override
    public String toString() {
        String leftString = left == null ? "." : left.toString();
        String rightString = right == null ? "." : right.toString();
        return "(" + leftString + " o" + op + " " + rightString + ")";
    }
}
