package org.drools.core.rete.builder;

import org.drools.base.rule.GroupElement;
import org.drools.base.rule.RuleElement;

public interface ReteooComponentBuilder {

    boolean requiresLeftActivation(BuildUtils buildUtils, GroupElement subrule);

    void build(BuildContext ctx, BuildUtils buildUtils, RuleElement subrule);
}
