package org.drools.core;

import org.drools.core.RuleBuilder.BaseRuleBuilder;
import org.kie.api.definition.rule.Rule;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class RuleBaseModifier {

    public static <DS> ChangeSet<DS> changeSet() {
        return new ChangeSet<>();
    }

    public static <DS> ChangeSetModifier<DS> with(RuleBase<DS> ruleBase) {
        return new ChangeSetModifier<>(ruleBase);
    }

    public static class ChangeSetModifier<DS> {
        RuleBase<DS> ruleBase;

        public ChangeSetModifier(RuleBase<DS> ruleBase) {
            this.ruleBase = ruleBase;
        }

        public <DS> void apply(ChangeSetBuilder<DS> changeSetBuilder) {
            ruleBase.apply(changeSetBuilder);
//            ChangeSet<DS> changeSet = changeSetBuilder.getChangeSet();
//            for(PackageChangeSet<DS> packages : changeSet.added.values()) {
//               for(UnitChangeSet<DS> units : packages.added.values()) {
//                   for(Rule rule : units.added.values()) {
//
//
//                   }
//               }
//            }
        }
    }

    public interface ChangeSetBuilder<DS> {
        ChangeSet<DS>  getChangeSet();
    }

    public static class ChangeSet<DS> implements ChangeSetBuilder<DS> {
        private Map<String, RulePackageChangeSet<DS>> added   = new HashMap<>();
        private Set<String>                           removed = new HashSet<>();
        private RulePackageChangeSet<DS>              packageChangeSet;

        public RulePackageChangeSet<DS> selectPackage(String packageName) {
            packageChangeSet = added.get(packageName);
            if (packageChangeSet == null) {
                packageChangeSet = new RulePackageChangeSet<DS>(this);
                added.put(packageName, packageChangeSet);
            }
            return packageChangeSet;
        }

        public ChangeSet<DS> remove(String packageName) {
            this.added.remove(packageName);
            this.removed.add(packageName);
            return this;
        }

        @Override
        public ChangeSet<DS> getChangeSet() {
            return this;
        }

        public Map<String, RulePackageChangeSet<DS>> getAdded() {
            return added;
        }

        public Set<String> getRemoved() {
            return removed;
        }
    }


    public static class RulePackageChangeSet<DS> implements ChangeSetBuilder<DS> {
        private ChangeSet<DS>              changeSet;
        private String                         packageName;
        private Map<String, RuleUnitChangeSet> added   = new HashMap<>();
        private Set<String>           removed = new HashSet<>();
        private RuleUnitChangeSet<DS> unitChangeSet;

        public RulePackageChangeSet(ChangeSet<DS> changeSet) {
            this.changeSet = changeSet;
        }

        public RuleUnitChangeSet<DS> selectUnit(String unitName) {
            unitChangeSet = added.get(unitName);
            if (unitChangeSet == null) {
                unitChangeSet =  new RuleUnitChangeSet<DS>(this);
                added.put(unitName, unitChangeSet);
            }

            return unitChangeSet;
        }

        public RulePackageChangeSet<DS> remove(String unitName) {
            this.added.remove(unitName);
            this.removed.add(unitName);
            return this;
        }

        public String getPackageName() {
            return packageName;
        }

        public Map<String, RuleUnitChangeSet> getAdded() {
            return added;
        }

        public Set<String> getRemoved() {
            return removed;
        }

        @Override
        public ChangeSet<DS> getChangeSet() {
            return changeSet;
        }
    }

    public static class RuleUnitChangeSet<DS> implements ChangeSetBuilder<DS>  {
        private RulePackageChangeSet<DS> packageChangeSet;
        private Map<String, Rule>        added   = new HashMap<String, Rule>();
        private Set<String>          removed = new HashSet<>();

        public RuleUnitChangeSet(RulePackageChangeSet<DS> packageChangeSet) {
            this.packageChangeSet = packageChangeSet;
        }

        public RulePackageChangeSet<DS> selectPackage(String packageName) {
            return packageChangeSet.changeSet.selectPackage(packageName);
        }

        public RuleUnitChangeSet<DS> selectUnit(String unitName) {
            return packageChangeSet.selectUnit(unitName);
        }

        public RuleUnitChangeSet<DS> add(BaseRuleBuilder builder) {
            Rule rule = builder.build();
            added.put(rule.getName(), rule);
            return this;
        }

        public RuleUnitChangeSet<DS> remove(String rule) {
            added.remove(rule);
            removed.remove(rule);
            return this;
        }

        public Map<String, Rule> getAdded() {
            return added;
        }

        public Set<String> getRemoved() {
            return removed;
        }

        @Override
        public ChangeSet<DS> getChangeSet() {
            return packageChangeSet.changeSet;
        }
    }
}
