package org.drools.core;

import org.drools.core.RuleBuilder.BaseRuleBuilder;
import org.drools.core.RuleBuilder.RuleDescriptor;
import org.kie.api.definition.rule.Rule;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class RuleBaseModifier {

    public static <CTX> ChangeSet<CTX> changeSet() {
        return new ChangeSet<>();
    }

    public static <CTX> ChangeSetModifier<CTX> with(RuleBase<CTX> ruleBase) {
        return new ChangeSetModifier<>(ruleBase);
    }

    public static class ChangeSetModifier<CTX> {
        RuleBase<CTX> ruleBase;

        public ChangeSetModifier(RuleBase<CTX> ruleBase) {
            this.ruleBase = ruleBase;
        }

        public <CTX> void apply(ChangeSetBuilder<CTX> changeSetBuilder) {
            ruleBase.apply(changeSetBuilder);
//            ChangeSet<CTX> changeSet = changeSetBuilder.getChangeSet();
//            for(PackageChangeSet<CTX> packages : changeSet.added.values()) {
//               for(UnitChangeSet<CTX> units : packages.added.values()) {
//                   for(Rule rule : units.added.values()) {
//
//
//                   }
//               }
//            }
        }
    }

    public interface ChangeSetBuilder<CTX> {
        ChangeSet<CTX>  getChangeSet();
    }

    public static class ChangeSet<CTX> implements ChangeSetBuilder<CTX> {
        private Map<String, RulePackageChangeSet<CTX>> added   = new HashMap<>();
        private Set<String>                           removed = new HashSet<>();
        private RulePackageChangeSet<CTX>              packageChangeSet;

        public RulePackageChangeSet<CTX> selectPackage(String packageName) {
            packageChangeSet = added.get(packageName);
            if (packageChangeSet == null) {
                packageChangeSet = new RulePackageChangeSet<CTX>(this);
                added.put(packageName, packageChangeSet);
            }
            return packageChangeSet;
        }

        public ChangeSet<CTX> remove(String packageName) {
            this.added.remove(packageName);
            this.removed.add(packageName);
            return this;
        }

        @Override
        public ChangeSet<CTX> getChangeSet() {
            return this;
        }

        public Map<String, RulePackageChangeSet<CTX>> getAdded() {
            return added;
        }

        public Set<String> getRemoved() {
            return removed;
        }
    }


    public static class RulePackageChangeSet<CTX> implements ChangeSetBuilder<CTX> {
        private ChangeSet<CTX>              changeSet;
        private String                         packageName;
        private Map<String, RuleUnitChangeSet> added   = new HashMap<>();
        private Set<String>           removed = new HashSet<>();
        private RuleUnitChangeSet<CTX> unitChangeSet;

        public RulePackageChangeSet(ChangeSet<CTX> changeSet) {
            this.changeSet = changeSet;
        }

        public RuleUnitChangeSet<CTX> selectUnit(String unitName) {
            unitChangeSet = added.get(unitName);
            if (unitChangeSet == null) {
                unitChangeSet =  new RuleUnitChangeSet<CTX>(this);
                added.put(unitName, unitChangeSet);
            }

            return unitChangeSet;
        }

        public RulePackageChangeSet<CTX> remove(String unitName) {
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
        public ChangeSet<CTX> getChangeSet() {
            return changeSet;
        }
    }

    public static class RuleUnitChangeSet<CTX> implements ChangeSetBuilder<CTX>  {
        private RulePackageChangeSet<CTX>         packageChangeSet;
        private Map<String, Rule>                added       = new HashMap<>();
        private List<RuleDescriptor<CTX>>         descriptors = new ArrayList<>();
        private Set<String>                      removed     = new HashSet<>();

        public RuleUnitChangeSet(RulePackageChangeSet<CTX> packageChangeSet) {
            this.packageChangeSet = packageChangeSet;
        }

        public RulePackageChangeSet<CTX> selectPackage(String packageName) {
            return packageChangeSet.changeSet.selectPackage(packageName);
        }

        public RuleUnitChangeSet<CTX> selectUnit(String unitName) {
            return packageChangeSet.selectUnit(unitName);
        }

        public RuleUnitChangeSet<CTX> add(BaseRuleBuilder builder) {
            Rule rule = builder.build();
            added.put(rule.getName(), rule);
            RuleDescriptor<CTX> descriptor = builder.descriptor();
            descriptors.add(descriptor);
            return this;
        }

        public RuleUnitChangeSet<CTX> remove(String rule) {
            added.remove(rule);
            removed.remove(rule);
            return this;
        }

        public Map<String, Rule>            getAdded()       { return added; }
        public List<RuleDescriptor<CTX>>     getDescriptors() { return descriptors; }
        public Set<String>                  getRemoved()     { return removed; }

        @Override
        public ChangeSet<CTX> getChangeSet() {
            return packageChangeSet.changeSet;
        }
    }
}
