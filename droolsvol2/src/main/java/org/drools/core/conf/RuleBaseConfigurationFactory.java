package org.drools.core.conf;

import org.drools.wiring.api.classloader.ProjectClassLoader;
import org.kie.api.KieBaseConfiguration;
import org.kie.internal.conf.CompositeBaseConfiguration;
import org.kie.internal.utils.ChainedProperties;

import java.util.Properties;

public class RuleBaseConfigurationFactory {
    /**
     * Create a KnowledgeBaseConfiguration on which properties can be set.
     * @return
     *     The KnowledgeBaseConfiguration.
     */
    public static KieBaseConfiguration newKnowledgeBaseConfiguration() {
        return newKnowledgeBaseConfiguration(null, null);
    }

    /**
     * Create a KnowledgeBaseConfiguration on which properties can be set. Use
     * the given properties file and ClassLoader - either of which can be null.
     * @return
     *     The KnowledgeBaseConfiguration.
     */
    public static KieBaseConfiguration newKnowledgeBaseConfiguration(Properties properties,
                                                                     ClassLoader... classLoaders) {
        if (classLoaders != null && (classLoaders.length > 1 || classLoaders[0] == null)) {
            throw new UnsupportedOperationException("Pass only a single, non null, classloader. As an array of Classloaders is no longer supported. ");
        }

        ClassLoader classLoader = classLoaders != null ? classLoaders[0] : null;
        ClassLoader projClassLoader = getClassLoader(classLoader);

        ChainedProperties chained = ChainedProperties.getChainedProperties(projClassLoader);

        if ( properties != null ) {
            chained.addProperties( properties );
        }

        return new CompositeBaseConfiguration(chained, projClassLoader,
                                              BaseConfigurationFactories.baseConf, BaseConfigurationFactories.ruleConf);
    }

    private static ClassLoader getClassLoader(ClassLoader classLoader) {
        ClassLoader projClassLoader = classLoader instanceof ProjectClassLoader ? classLoader : ProjectClassLoader.getClassLoader(classLoader, RuleBaseConfigurationFactory.class);
        return projClassLoader;
    }
}
