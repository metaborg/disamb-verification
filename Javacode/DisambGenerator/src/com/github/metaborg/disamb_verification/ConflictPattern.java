package com.github.metaborg.disamb_verification;

import java.util.Objects;

public class ConflictPattern {

    private ConflictType relation;
    private int o1;
    private int o2;

    public ConflictPattern(ConflictType relation, int o1, int o2) {
        this.relation = relation;
        this.o1 = o1;
        this.o2 = o2;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ConflictPattern that = (ConflictPattern) o;
        return o1 == that.o1 &&
                o2 == that.o2 &&
                relation == that.relation;
    }

    @Override
    public int hashCode() {
        return Objects.hash(relation, o1, o2);
    }

    @Override
    public String toString() {
        return "o" + o1 + " " + relation + " o" + o2;
    }
}
