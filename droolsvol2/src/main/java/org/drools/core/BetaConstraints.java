package org.drools.core;

import org.drools.base.rule.constraint.BetaConstraint;

import java.util.Collections;
import java.util.List;

/**
 * Vol2 BetaConstraints — wraps the cross-pattern constraints evaluated at a JoinNode.
 */
public interface BetaConstraints {
    default List<BetaConstraint> getConstraints() {
        return Collections.emptyList();
    }
}
