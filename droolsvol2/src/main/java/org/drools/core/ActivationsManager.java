package org.drools.core;

import org.drools.base.common.NetworkNode;

/**
 * TODO #6650: Temporary interface — vol2 evaluation engine will replace this.
 */
public interface ActivationsManager {
    ActivationsManager getPartitionedAgendaForNode(NetworkNode node);
    RuleAgendaItem createRuleAgendaItem(int salience, PathMemory pathMemory, TerminalNode rtn);
    ActivationsFilter getActivationsFilter();
    void addQueryAgendaItem(RuleAgendaItem item);
    void addEagerRuleAgendaItem(RuleAgendaItem item);
}
