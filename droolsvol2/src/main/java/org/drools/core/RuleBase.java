package org.drools.core;

import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.core.RuleBaseModifier.ChangeSet;
import org.drools.core.RuleBaseModifier.ChangeSetBuilder;
import org.drools.core.RuleBaseModifier.RulePackageChangeSet;
import org.drools.core.RuleBaseModifier.RuleUnitChangeSet;
import org.drools.core.RuleBuilder.RuleDescriptor;
import org.drools.core.conf.RuleBaseConfiguration;
import org.drools.core.conf.RuleBaseConfigurationFactory;
import org.drools.core.rete.builder.ReteBuilder;
import org.kie.api.KieBaseConfiguration;
import org.kie.api.definition.rule.Rule;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class RuleBase<DS> {

    private ReteBuilder    reteBuilder;
    private EntryPointNode root;

    private Map<String, RulePackage>        rulePackages    = new HashMap<>();
    // keyed by fully-qualified "packageName.unitName"
    private Map<String, UnitDescriptor<?>> unitDescriptors = new HashMap<>();

    private KieBaseConfiguration    baseConf;
    private RuleBaseConfiguration   ruleBaseConf;

    public RuleBase() {
        this(RuleBaseConfigurationFactory.newKnowledgeBaseConfiguration());
    }

    public RuleBase(KieBaseConfiguration baseConf) {
        this.baseConf = baseConf;
        this.ruleBaseConf = baseConf.as(RuleBaseConfiguration.KEY);
        // Create the root entry point node (id=0, the Rete root)
        this.root = new EntryPointNode(0, 0, 0);
        reteBuilder = new ReteBuilder(this);
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


        for (Map.Entry<String, RulePackageChangeSet<DS>> pkgEntry : changeSet.getAdded().entrySet()) {
            String packageName = pkgEntry.getKey();
            RulePackageChangeSet<DS> changedRulePackages = pkgEntry.getValue();

            for (Map.Entry<String, RuleUnitChangeSet> unitEntry : changedRulePackages.getAdded().entrySet()) {
                String unitName = unitEntry.getKey();
                String fqn = packageName + "." + unitName;
                RuleUnitChangeSet<DS> changedUnits = (RuleUnitChangeSet<DS>) unitEntry.getValue();

                @SuppressWarnings("unchecked")
                UnitDescriptor<DS> unitDescriptor = (UnitDescriptor<DS>)
                        unitDescriptors.computeIfAbsent(fqn, k -> new UnitDescriptor<DS>());

                for (Rule rule : changedUnits.getAdded().values()) {
                    reteBuilder.addRule((RuleImpl) rule);
                }

                for (RuleDescriptor<DS> descriptor : changedUnits.getDescriptors()) {
                    unitDescriptor.addRule(descriptor);
                }
            }
        }
    }

    private static void removeAllRules(RuleUnit ruleUnit) {
        List<Rule> removedRules = new ArrayList<>(ruleUnit.getRules().size());
        ruleUnit.getRules().values().stream().forEach(rule -> removedRules.add(rule));
        // @TODO actually remove the rule
    }


    @SuppressWarnings("unchecked")
    <DS> UnitDescriptor<DS> unitDescriptor(String fqn) {
        return (UnitDescriptor<DS>) unitDescriptors.get(fqn);
    }

    public RuleBaseConfiguration getRuleBaseConfiguration() {
        return ruleBaseConf;
    }

    public ReteBuilder getReteBuilder() {
        return reteBuilder;
    }

    /** Returns the Rete root (default entry point node). */
    public EntryPointNode getRete() { return root; }

    /** TODO #6650: partition management not yet implemented in vol2 */
    public org.drools.base.common.RuleBasePartitionId createNewPartitionId() {
        return org.drools.base.common.RuleBasePartitionId.MAIN_PARTITION;
    }
}
