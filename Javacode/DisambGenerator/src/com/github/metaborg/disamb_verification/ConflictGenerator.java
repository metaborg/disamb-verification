package com.github.metaborg.disamb_verification;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import static com.github.metaborg.disamb_verification.ConflictType.*;

public class ConflictGenerator {

    public Collection<Set<ConflictPattern>> generateConflicts(int opCount) {
        HashSet<Set<ConflictPattern>> result = new HashSet<>();

        ArrayList<int[]> pairs = new ArrayList<>((opCount * (opCount - 1)) / 2);

        for (int o1 = 1; o1 <= opCount; o1++) {
            for (int o2 = o1 + 1; o2 <= opCount; o2++) {
                pairs.add(new int[] {o1, o2});
            }
        }

        assignConflictTypes(result, new HashSet<>(), pairs, 0);
        return result;
    }

    private void assignConflictTypes(
            Collection<Set<ConflictPattern>> result,
            Set<ConflictPattern> current,
            ArrayList<int[]> pairs,
            int currentIndex
    ) {
        if (currentIndex >= pairs.size()) {
            result.add(current);
            return;
        }

        int[] pair = pairs.get(currentIndex);
        int o1 = pair[0];
        int o2 = pair[1];
        currentIndex++;

        HashSet<ConflictPattern> leftAssoc = new HashSet<>(current);
        leftAssoc.add(new ConflictPattern(L2R, o1, o2));
        leftAssoc.add(new ConflictPattern(L2R, o2, o1));
        assignConflictTypes(result, leftAssoc, pairs, currentIndex);

        HashSet<ConflictPattern> rightAssoc = new HashSet<>(current);
        rightAssoc.add(new ConflictPattern(R2L, o1, o2));
        rightAssoc.add(new ConflictPattern(R2L, o2, o1));
        assignConflictTypes(result, rightAssoc, pairs, currentIndex);

        HashSet<ConflictPattern> priority1 = new HashSet<>(current);
        priority1.add(new ConflictPattern(L2R, o1, o2));
        priority1.add(new ConflictPattern(R2L, o1, o2));
        assignConflictTypes(result, priority1, pairs, currentIndex);

        HashSet<ConflictPattern> priority2 = new HashSet<>(current);
        priority2.add(new ConflictPattern(L2R, o2, o1));
        priority2.add(new ConflictPattern(R2L, o2, o1));
        assignConflictTypes(result, priority2, pairs, currentIndex);
    }

}
