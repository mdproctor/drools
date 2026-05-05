package org.drools.core;

import org.drools.core.function.Predicate2;

import java.util.ArrayList;
import java.util.List;

public class FilterNode<CTX, T> extends BaseNode {
    private BaseNode                parent;
    private Predicate2<Context<CTX>, T> predicate;
    private List<NetworkNode>          children;

    @Override public int getType() { return Vol2NodeTypeEnums.FilterNode; }

    public FilterNode(int id) {
        super(id, 0, -1);
    }

    @Override
    public BaseNode getParent() {
        return parent;
    }

    public void setParent(BaseNode parent) {
        this.parent = parent;
    }

    public Predicate2<Context<CTX>, T> getPredicate() {
        return predicate;
    }

    public List<NetworkNode> getChildren() {
        return children;
    }

    public void setChildren(ArrayList<NetworkNode> children) {
        this.children = children;
    }
}
