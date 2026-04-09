package org.drools.core;
/** TODO #6650: Temporary stub — vol2 component factory not yet implemented. */
public class CoreComponentFactory {
    private static final CoreComponentFactory INSTANCE = new CoreComponentFactory();
    public static CoreComponentFactory get() { return INSTANCE; }
    public NodeFactory getNodeFactoryService() { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
}
