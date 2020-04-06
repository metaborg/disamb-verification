package com.github.metaborg.disamb_verification;

import java.util.Iterator;

public class TreeGenerator implements Iterator<Tree> {

    private int leftmostOp;
    private int rightmostOp;

    private boolean isLeaf;
    private boolean isLeafAndDone;

    private int currentOp;
    private TreeGenerator leftGenerator;
    private TreeGenerator rightGenerator;
    private Tree currentLeftTree;
    private Tree currentRightTree;

    public TreeGenerator(int opCount) {
        this(1, opCount);
    }

    private TreeGenerator(int leftmostOp, int rightmostOp) {
        this.leftmostOp = leftmostOp;
        this.rightmostOp = rightmostOp;

        this.isLeaf = leftmostOp > rightmostOp;
        this.isLeafAndDone = false;

        if (!isLeaf) {
            this.currentOp = leftmostOp;
            resetLeftGenerator();
            resetRightGenerator();
        }

    }

    private void resetLeftGenerator() {
        leftGenerator = new TreeGenerator(leftmostOp, currentOp - 1);
        this.currentLeftTree = leftGenerator.next();
    }

    private void resetRightGenerator() {
        rightGenerator = new TreeGenerator(currentOp + 1, rightmostOp);
        this.currentRightTree = rightGenerator.next();
    }

    @Override
    public boolean hasNext() {
        if (isLeafAndDone) {
            return false;
        } else if (isLeaf) {
            return true;
        } else {
            return currentOp <= rightmostOp;
        }
    }

    @Override
    public Tree next() {
        if (isLeaf) {
            isLeafAndDone = true;
            return null;
        }

        Tree result = new Tree(currentOp, currentLeftTree, currentRightTree);
        if (leftGenerator.hasNext()) {
            currentLeftTree = leftGenerator.next();
        } else {
            if (rightGenerator.hasNext()) {
                currentRightTree = rightGenerator.next();
            } else {
                currentOp++;
                if (hasNext()) {
                    resetRightGenerator();
                }
            }
            if (hasNext()) {
                resetLeftGenerator();
            }
        }

        return result;
    }
}
