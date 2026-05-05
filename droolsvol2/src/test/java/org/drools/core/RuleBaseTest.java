package org.drools.core;

import org.drools.api.data.DataStore;
import org.junit.jupiter.api.Test;

public class RuleBaseTest {

    @Test
    public void test0() {
        RuleBase ruleBase = new RuleBase();

        record CTX(DataStore<Person> persons) {};

        RuleBuilder<CTX> builder = new RuleBuilder<>();

        RuleBaseModifier.with(ruleBase)
                        .apply(RuleBaseModifier.changeSet()
                                               .selectPackage("org.domain").selectUnit("Unit1")
                                               .add(builder.rule("r1").ifn(() -> {System.out.println("hello");})));
    }

    @Test
    public void test1() {
        RuleBase ruleBase = new RuleBase();

        record CTX(DataStore<?> ds1) {};

        RuleBuilder<CTX> rb = new RuleBuilder<>();

        RuleBaseModifier.with(ruleBase)
                        .apply(RuleBaseModifier.changeSet()
                                               .selectPackage("org.domain").selectUnit("Unit1")
                                               .add(rb.rule("r1").ifn(() -> {}))
                                               .add(rb.rule("r2").ifn(() -> {})));
    }

    @Test
    public void test2() {
        RuleBase ruleBase = new RuleBase();

        record CTX(DataStore<Person> persons) {};

        record P3(String p3_1, String p3_2, String p3_3) {
            public static final P3 V = new P3(null,null,null);
        };

        RuleBuilder<CTX> rb = new RuleBuilder<>();

        RuleBaseModifier.with(ruleBase)
                        .apply(RuleBaseModifier.changeSet()
                                               .selectPackage("org.domain").selectUnit("Unit1")
                                               .add(rb.rule("rule1").<P3>params()
                                                           .join(rb.from(CTX::persons).filter(b -> b.age() > 20))
                                                           .filter((a, b) -> a.p3_1().length() > b.age())));

    }



}
