package com.github.metaborg.disamb_verification;

import java.util.Objects;

public class Tree {

    private int op;
    private Tree left;
    private Tree right;

    public Tree(int op, Tree left, Tree right) {
        this.op = op;
        this.left = left;
        this.right = right;
    }

    public int getOp() {
        return op;
    }

    public Tree getLeft() {
        return left;
    }

    public Tree getRight() {
        return right;
    }

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
        return "[" + leftString + " o" + op + " " + rightString + "]";
    }
}
