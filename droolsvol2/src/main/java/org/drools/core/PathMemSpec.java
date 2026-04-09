package org.drools.core;
import java.io.Serializable;
/** TODO #6650: Temporary stub — PathMemSpec not yet implemented in vol2. */
public class PathMemSpec implements Serializable {
    public long allLinkedTestMask;
    public int smemCount;
    public PathMemSpec(long allLinkedTestMask, int smemCount) {
        this.allLinkedTestMask = allLinkedTestMask;
        this.smemCount = smemCount;
    }
    public long allLinkedTestMask() { return allLinkedTestMask; }
    public int smemCount() { return smemCount; }
}
