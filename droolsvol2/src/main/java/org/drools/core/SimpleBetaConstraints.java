package org.drools.core;

import org.drools.base.rule.constraint.BetaConstraint;

import java.util.List;

/**
 * Vol2 beta constraints — wraps a list of cross-pattern constraints for a JoinNode.
 */
public class SimpleBetaConstraints implements BetaConstraints {

    private final List<BetaConstraint> constraints;

    public SimpleBetaConstraints(List<BetaConstraint> constraints) {
        this.constraints = constraints;
    }

    @Override
    public List<BetaConstraint> getConstraints() {
        return constraints;
    }
}
