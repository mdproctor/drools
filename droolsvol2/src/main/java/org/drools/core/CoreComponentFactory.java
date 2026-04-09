package org.drools.core;

import org.drools.core.rete.builder.DefaultNodeFactory;
import org.drools.core.rete.builder.NodeFactory;

/**
 * Vol2 component factory — provides the NodeFactory for Rete network construction.
 */
public class CoreComponentFactory {
    private static final CoreComponentFactory INSTANCE = new CoreComponentFactory();
    public static CoreComponentFactory get() { return INSTANCE; }
    public NodeFactory getNodeFactoryService() { return DefaultNodeFactory.INSTANCE; }
}
