package org.drools.core;

import org.drools.base.common.RuleBasePartitionId;
import org.drools.base.reteoo.BaseTerminalNode;
import org.drools.core.rete.builder.BuildContext;
import org.kie.api.definition.rule.Rule;

import java.util.Map;
import java.util.Set;

public abstract class BaseNode implements NetworkNode {
    protected int id;
    protected int pathIndex;
    protected int size;
    protected int objectIndex;
    protected int walkBack;
    protected int biLinearRightOffset;

    protected RuleBasePartitionId partitionId;

    protected Set<Rule>           associations;

    private Map<Integer, TerminalNode> associatedTerminals;

    private boolean                    streamMode;

    protected int                        hashcode;

    protected BaseNode leftInput;

    public BaseNode() {
        this(0, 0, 0);
    }

    public BaseNode(int id, int pathIndex, int objectIndex) {
        this.id          = id;
        this.pathIndex   = pathIndex;
        this.objectIndex = objectIndex;
    }

    public BaseNode(int id, int pathIndex, int objectIndex, int size, int walkBack) {
        this.id          = id;
        this.pathIndex   = pathIndex;
        this.objectIndex = objectIndex;
        this.size        = size;
        this.walkBack    = walkBack;
    }

    public int getWalkBack() {
        return walkBack;
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public int getPathIndex() {
        return pathIndex;
    }

    @Override
    public int getSize() {
        return size;
    }

    @Override
    public int getObjectIndex() {
        return objectIndex;
    }

    public BaseNode getLeftInput() {
        return leftInput;
    }

    public void setLeftInput(BaseNode leftInput) {
        this.leftInput = leftInput;
    }

    public int getObjectCount() {
        return objectIndex;
    }

    public void initMemoryId(org.drools.core.rete.builder.BuildContext context) {
        // Memory ID initialisation — TBD in vol2 evaluation engine
    }

    public int getType() {
        return 0;
    }

    @Override
    public org.drools.base.common.NetworkNode[] getSinks() {
        // Vol2 uses outputs arrays, not linked-list sinks — return null for compatibility
        return null;
    }

    /**
     * Returns true in case the current node is in use (is referenced by any other node)
     */
    public boolean isInUse() {
        // TODO
        throw new UnsupportedOperationException();
    }

    public ObjectTypeNode getObjectTypeNode() {
        // TODO
        throw new UnsupportedOperationException();
    }

    public String toString() {
        return "[" + this.getClass().getSimpleName() + "(" + this.id + ")]";
    }

    /**
     * Returns the partition ID for which this node belongs to
     */
    public RuleBasePartitionId getPartitionId() {
        return this.partitionId;
    }

    /**
     * Sets the partition this node belongs to
     */
    public void setPartitionId(BuildContext context, RuleBasePartitionId partitionId) {
        this.partitionId = partitionId;
    }

    /**
     * Associates this node with the give rule
     */
    public void addAssociation(Rule rule, BuildContext context) {
        this.associations.add( rule );
    }

    /**
     * Removes the association to the given rule from the
     * associations map.
     */
    public boolean removeAssociation( Rule rule, RuleRemovalContext context) {
        return this.associations.remove(rule);
    }

    public int getAssociationsSize() {
        return this.associations.size();
    }

    public Rule[] getAssociatedRules() {
        return this.associations.toArray( new Rule[this.associations.size()] );
    }

    public boolean isAssociatedWith( Rule rule ) {
        return this.associations.contains( rule );
    }

    public void addAssociatedTerminal(BaseTerminalNode terminalNode) {
        associatedTerminals.put(terminalNode.getId(),(TerminalNode) terminalNode);
    }

    public void removeAssociatedTerminal(BaseTerminalNode terminalNode) {
        associatedTerminals.remove(terminalNode.getId());
    }

    public int getAssociatedTerminalsSize() {
        return associatedTerminals.size();
    }

    public boolean hasAssociatedTerminal(BaseTerminalNode terminalNode) {
        return associatedTerminals.containsKey(terminalNode.getId());
    }

    @Override
    public final int hashCode() {
        return hashcode;
    }
}
