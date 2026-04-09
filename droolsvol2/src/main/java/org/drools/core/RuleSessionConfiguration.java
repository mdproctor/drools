package org.drools.core;
import org.drools.base.definitions.rule.impl.RuleImpl;
/** TODO #6650: Temporary stub — vol2 session configuration not yet implemented. */
public class RuleSessionConfiguration {
    public interface ActivationFilter {
        boolean accept(RuleImpl rule);
    }
    public ActivationFilter getForceEagerActivationFilter() {
        return rule -> false;
    }
}
