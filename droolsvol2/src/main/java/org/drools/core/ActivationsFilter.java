package org.drools.core;

/**
 * TODO #6650: Temporary interface — vol2 evaluation engine will replace this.
 */
public interface ActivationsFilter {
    boolean accept(RuleAgendaItem item);
}
