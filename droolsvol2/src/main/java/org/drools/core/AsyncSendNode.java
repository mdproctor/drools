package org.drools.core;
/** TODO #6650: Temporary stub class — async send node not yet implemented in vol2. */
public class AsyncSendNode extends BaseNode {
    @Override public int getType() { return Vol2NodeTypeEnums.AsyncSendNode; }

    public AsyncSendNode() { super(0, 0, 0); }
}
