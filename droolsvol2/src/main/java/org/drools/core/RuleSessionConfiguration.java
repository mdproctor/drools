package org.drools.core;
/** TODO #6650: Temporary stub — vol2 session configuration not yet implemented. */
public class RuleSessionConfiguration {
    public interface ActivationFilter {
        boolean accept(RuleAgendaItem item);
    }
    public ActivationFilter getForceEagerActivationFilter() {
        return item -> false;
    }
}
