package org.drools.core;

import org.drools.base.definitions.rule.impl.RuleImpl;

public class TerminalNode extends BaseNode{

    public TerminalNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    public TerminalNode(int id, int pathIndex, int objectIndex, int size, int walkBack) {
        super(id, pathIndex, objectIndex, size, walkBack);
    }

    public RuleImpl getRule() {
        return null;
    }
}
