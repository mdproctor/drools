package org.drools.core;

import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.core.RuleBaseModifier.ChangeSet;
import org.drools.core.RuleBaseModifier.ChangeSetBuilder;
import org.drools.core.RuleBaseModifier.RulePackageChangeSet;
import org.drools.core.RuleBaseModifier.RuleUnitChangeSet;
import org.drools.core.conf.RuleBaseConfiguration;
import org.drools.core.conf.RuleBaseConfigurationFactory;
import org.drools.core.rete.builder.ReteBuilder;
import org.kie.api.KieBaseConfiguration;
import org.kie.api.definition.rule.Rule;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class RuleBase<DS> {

    private ReteBuilder reteBuilder;

    private Map<String, RulePackage> rulePackages;

    private KieBaseConfiguration baseConf;

    private RuleBaseConfiguration ruleBaseConf;

    //private

    public RuleBase() {
        this(RuleBaseConfigurationFactory.newKnowledgeBaseConfiguration());
    }

    public RuleBase(KieBaseConfiguration baseConf) {
        reteBuilder = new ReteBuilder(this);
        this.baseConf = baseConf;
        this.ruleBaseConf = baseConf.as(RuleBaseConfiguration.KEY);
    }

    public <DS> void apply(ChangeSetBuilder<DS> changeSetBuilder) {
        ChangeSet<DS> changeSet = changeSetBuilder.getChangeSet();

        // for each removed package, remove all the units and all the rules for those units.
        for(String removedRulePackages : changeSet.getRemoved()) {
            RulePackage rulePackage = rulePackages.remove(removedRulePackages);
            List<RuleUnit> removedRuleUnits = new ArrayList<>(rulePackage.getRuleUnits().size());
            for (RuleUnit ruleUnit : rulePackage.getRuleUnits().values()) {
                removedRuleUnits.add(ruleUnit);
                removeAllRules(ruleUnit);
            }
        }


        for(RulePackageChangeSet<DS> changedRulePackages : changeSet.getAdded().values()) {
            RulePackage rulePackage = null;
            for (String removedRuleUnit : changedRulePackages.getRemoved()) {
                RuleUnit ruleUnit = rulePackage.getRuleUnits().remove(removedRuleUnit);
                removeAllRules(ruleUnit);
            }

            for(RuleUnitChangeSet<DS> changedUnits : changedRulePackages.getAdded().values()) {
                RuleUnit ruleUnit = null;
                for(String removedRule : changedUnits.getRemoved()) {
                   Rule rule = ruleUnit.getRules().remove(removedRule);
                }

                for(Rule rule : changedUnits.getAdded().values()) {
                    // build rule
                    reteBuilder.addRule((RuleImpl) rule);
                }
            }
        }
    }

    private static void removeAllRules(RuleUnit ruleUnit) {
        List<Rule> removedRules = new ArrayList<>(ruleUnit.getRules().size());
        ruleUnit.getRules().values().stream().forEach(rule -> removedRules.add(rule));
        // @TODO actually remove the rule
    }


    public RuleBaseConfiguration getRuleBaseConfiguration() {
        return ruleBaseConf;
    }

    public ReteBuilder getReteBuilder() {
        return reteBuilder;
    }
}
