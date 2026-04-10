package org.drools.core;

import io.quarkiverse.permuplate.Permute;
import io.quarkiverse.permuplate.PermuteConst;
import io.quarkiverse.permuplate.PermuteTypeParam;

import org.kie.api.definition.rule.Rule;

public class RuleExtendsPoint {
    private Rule rule;
    private int arity;

    public RuleExtendsPoint(Rule rule, int arity) {
        this.rule = rule;
        this.arity = arity;
    }

    public int arity() {
        return arity;
    }

    public void setArity(int arity) {
        this.arity = arity;
    }

    // Template — generates RuleExtendsPoint3..RuleExtendsPoint10
    @Permute(varName = "i", from = "3", to = "10", className = "RuleExtendsPoint${i}",
             inline = true, keepTemplate = true)
    public static class RuleExtendsPoint2<DS,
            @PermuteTypeParam(varName = "j", from = "2", to = "${i}", name = "${alpha(j)}") B>
            extends RuleExtendsPoint {

        @PermuteConst("${i}")
        private static final int TEMPLATE_ARITY = 2;

        public RuleExtendsPoint2(Rule rule) {
            super(rule, TEMPLATE_ARITY);
        }
    }
}
