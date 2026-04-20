package org.drools.core;

import org.drools.api.data.DataStore;
import org.drools.base.base.ClassObjectType;
import org.drools.base.base.ValueResolver;
import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.GroupElement;
import org.drools.base.rule.GroupElementFactory;
import org.drools.base.rule.Pattern;
import org.drools.base.rule.constraint.AlphaNodeFieldConstraint;
import org.drools.base.rule.constraint.BetaConstraint;
import org.drools.base.rule.constraint.Constraint;
import org.drools.base.reteoo.BaseTuple;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.kie.api.runtime.rule.FactHandle;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Structural tests for the vol2 Rete network builder.
 * Verifies the topology produced from rules — the correct structure
 * is the precondition for correct evaluation.
 * All rules are applied via RuleBaseModifier; network is inspected
 * structurally by traversing from ruleBase.getRete() via getOutputs().
 */
public class ReteBuilderTest {

    // Shared context record for all DSL-based tests
    record TestCTX(DataStore<Person> persons,
                   DataStore<String> names,
                   DataStore<Integer> counts) {}

    private RuleBase<TestCTX> ruleBase;

    @BeforeEach
    public void setUp() {
        ruleBase = new RuleBase<>();
    }

    // -------------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------------

    /** Apply a rule via the standard RuleBaseModifier path; return only the new terminals. */
    @SuppressWarnings({"unchecked", "rawtypes"})
    private List<TerminalNode> applyRule(RuleBuilder.BaseRuleBuilder<?> builder) {
        Set<Integer> before = terminalsFor(ruleBase).stream()
                .map(BaseNode::getId).collect(Collectors.toSet());
        RuleBaseModifier.with((RuleBase) ruleBase)
                .apply(RuleBaseModifier.changeSet()
                                       .selectPackage("test").selectUnit("Test")
                                       .add(builder));
        return terminalsFor(ruleBase).stream()
                .filter(t -> !before.contains(t.getId()))
                .collect(Collectors.toList());
    }

    /** Wrap a manually-built RuleImpl so it can go through applyRule(). */
    private List<TerminalNode> applyRuleImpl(RuleImpl rule) {
        return applyRule(new RuleBuilder.BaseRuleBuilder<>(null, rule) {});
    }

    /** Traverse the output tree from the Rete root; collect all TerminalNodes. */
    private static List<TerminalNode> terminalsFor(RuleBase<?> rb) {
        List<TerminalNode> result = new ArrayList<>();
        collectTerminals(rb.getRete(), result, new HashSet<>());
        return result;
    }

    private static void collectTerminals(BaseNode node, List<TerminalNode> acc, Set<Integer> seen) {
        if (!seen.add(node.getId())) return;
        if (node instanceof TerminalNode tn) acc.add(tn);
        for (BaseNode out : node.getOutputs()) collectTerminals(out, acc, seen);
    }

    // -------------------------------------------------------------------------
    // Single-pattern structure
    // -------------------------------------------------------------------------

    @Test
    public void testSinglePatternProducesTerminalNode() {
        List<TerminalNode> terminals = applyRule(
                new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons));

        assertThat(terminals).hasSize(1);
        assertThat(terminals.get(0).getRule().getName()).isEqualTo("r1");
    }

    @Test
    public void testSinglePatternBuildsObjectTypeNode() {
        List<TerminalNode> terminals = applyRule(
                new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons));

        // terminal → LIA → OTN
        BaseNode lia = terminals.get(0).getLeftInput();
        assertThat(lia).isInstanceOf(LeftInputAdapterNode.class);

        BaseNode otn = lia.getLeftInput();
        assertThat(otn).isInstanceOf(ObjectTypeNode.class);
        assertThat(((ObjectTypeNode) otn).getObjectType())
                .isEqualTo(new ClassObjectType(Person.class));
    }

    @Test
    public void testSinglePatternConnectsToRoot() {
        applyRule(new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons));

        // OTN's leftInput is the Rete root (EntryPointNode)
        assertThat(ruleBase.getRete()).isNotNull();
        List<TerminalNode> terminals = terminalsFor(ruleBase);
        BaseNode otn = terminals.get(0).getLeftInput().getLeftInput();
        assertThat(otn.getLeftInput()).isInstanceOf(EntryPointNode.class);
    }

    @Test
    public void testNoPatternRuleUsesInitialFact() {
        // Empty LHS — builder injects an InitialFact pattern so the network has a root
        RuleImpl rule = new RuleImpl("noPatterns");
        rule.setLhs(GroupElementFactory.newAndInstance());
        List<TerminalNode> terminals = applyRuleImpl(rule);

        assertThat(terminals).hasSize(1);
        BaseNode lia = terminals.get(0).getLeftInput();
        assertThat(lia).isInstanceOf(LeftInputAdapterNode.class);
        ObjectTypeNode otn = (ObjectTypeNode) lia.getLeftInput();
        assertThat(((ClassObjectType) otn.getObjectType()).getClassType().getName())
                .contains("InitialFact");
    }

    // -------------------------------------------------------------------------
    // Node sharing
    // -------------------------------------------------------------------------

    @Test
    public void testTwoRulesSamePatternBothGetTerminals() {
        List<TerminalNode> t1 = applyRule(
                new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons));
        List<TerminalNode> t2 = applyRule(
                new RuleBuilder<TestCTX>().rule("r2").from(TestCTX::persons));

        assertThat(t1).hasSize(1);
        assertThat(t2).hasSize(1);
        assertThat(t1.get(0).getRule().getName()).isEqualTo("r1");
        assertThat(t2.get(0).getRule().getName()).isEqualTo("r2");
    }

    @Test
    public void testNodeSharingReusesObjectTypeNodeAndLia() {
        List<TerminalNode> t1 = applyRule(
                new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons));
        List<TerminalNode> t2 = applyRule(
                new RuleBuilder<TestCTX>().rule("r2").from(TestCTX::persons));

        BaseNode lia1 = t1.get(0).getLeftInput();
        BaseNode lia2 = t2.get(0).getLeftInput();
        assertThat(lia1).isSameAs(lia2);

        BaseNode otn1 = lia1.getLeftInput();
        BaseNode otn2 = lia2.getLeftInput();
        assertThat(otn1).isSameAs(otn2);

        // shared LIA has both terminals as outputs
        assertThat(lia1.getOutputs()).contains(t1.get(0), t2.get(0));
    }

    @Test
    public void testDifferentPatternTypesBuildSeparateObjectTypeNodes() {
        List<TerminalNode> t1 = applyRule(
                new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons));
        List<TerminalNode> t2 = applyRule(
                new RuleBuilder<TestCTX>().rule("r2").from(TestCTX::names));

        ObjectTypeNode otn1 = (ObjectTypeNode) t1.get(0).getLeftInput().getLeftInput();
        ObjectTypeNode otn2 = (ObjectTypeNode) t2.get(0).getLeftInput().getLeftInput();

        assertThat(((ClassObjectType) otn1.getObjectType()).getClassType()).isEqualTo(Person.class);
        assertThat(((ClassObjectType) otn2.getObjectType()).getClassType()).isEqualTo(String.class);
        assertThat(otn1).isNotSameAs(otn2);
    }

    @Test
    public void testNodeIdsAreMonotonicallyIncreasing() {
        List<TerminalNode> t1 = applyRule(
                new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons));
        List<TerminalNode> t2 = applyRule(
                new RuleBuilder<TestCTX>().rule("r2").from(TestCTX::names));

        assertThat(t1.get(0).getId()).isGreaterThan(0);
        assertThat(t2.get(0).getId()).isGreaterThan(t1.get(0).getId());
    }

    // -------------------------------------------------------------------------
    // Join network structure
    // -------------------------------------------------------------------------

    @Test
    public void testTwoPatternRuleProducesJoinNode() {
        List<TerminalNode> terminals = applyRule(
                new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons).join(TestCTX::names));

        assertThat(terminals).hasSize(1);
        BaseNode join = terminals.get(0).getLeftInput();
        assertThat(join).isInstanceOf(JoinNode.class);

        // left: LIA → OTN(Person)
        assertThat(join.getLeftInput()).isInstanceOf(LeftInputAdapterNode.class);
        ObjectTypeNode leftOtn = (ObjectTypeNode) join.getLeftInput().getLeftInput();
        assertThat(((ClassObjectType) leftOtn.getObjectType()).getClassType()).isEqualTo(Person.class);

        // right: OTN(String) — bi-linear direct input
        assertThat(((JoinNode) join).getRightInput()).isInstanceOf(ObjectTypeNode.class);
        ObjectTypeNode rightOtn = (ObjectTypeNode) ((JoinNode) join).getRightInput();
        assertThat(((ClassObjectType) rightOtn.getObjectType()).getClassType()).isEqualTo(String.class);
    }

    @Test
    public void testThreePatternRuleProducesNestedJoins() {
        List<TerminalNode> terminals = applyRule(
                new RuleBuilder<TestCTX>().rule("r1")
                        .from(TestCTX::persons).join(TestCTX::names).join(TestCTX::counts));

        assertThat(terminals).hasSize(1);

        // terminal → join2 → join1 (nested)
        BaseNode join2 = terminals.get(0).getLeftInput();
        assertThat(join2).isInstanceOf(JoinNode.class);

        BaseNode join1 = join2.getLeftInput();
        assertThat(join1).isInstanceOf(JoinNode.class);

        // rightmost OTN is Integer
        ObjectTypeNode rightOtn2 = (ObjectTypeNode) ((JoinNode) join2).getRightInput();
        assertThat(((ClassObjectType) rightOtn2.getObjectType()).getClassType()).isEqualTo(Integer.class);
    }

    @Test
    public void testNoBetaConstraintUsesEmptyConstraints() {
        List<TerminalNode> terminals = applyRule(
                new RuleBuilder<TestCTX>().rule("r1").from(TestCTX::persons).join(TestCTX::names));

        JoinNode join = (JoinNode) terminals.get(0).getLeftInput();
        assertThat(join.getConstraints()).isNotNull();
        assertThat(join.getConstraints().getConstraints()).isEmpty();
    }

    @Test
    public void testBetaConstraintStoredOnJoinNode() {
        RuleImpl rule = new RuleImpl("r1");
        GroupElement lhs = GroupElementFactory.newAndInstance();
        Pattern p1 = new Pattern(0, new ClassObjectType(Person.class));
        Pattern p2 = new Pattern(1, new ClassObjectType(String.class));
        p2.addConstraint(new TestBetaConstraint("person.name == name"));
        lhs.addChild(p1);
        lhs.addChild(p2);
        rule.setLhs(lhs);

        List<TerminalNode> terminals = applyRuleImpl(rule);

        JoinNode join = (JoinNode) terminals.get(0).getLeftInput();
        assertThat(join.getConstraints().getConstraints()).hasSize(1);
        assertThat(join.getConstraints().getConstraints().get(0))
                .isInstanceOf(TestBetaConstraint.class);
    }

    // -------------------------------------------------------------------------
    // Alpha constraint structure
    // -------------------------------------------------------------------------

    @Test
    public void testSingleAlphaConstraintBuildsAlphaNode() {
        RuleImpl rule = new RuleImpl("r1");
        GroupElement lhs = GroupElementFactory.newAndInstance();
        Pattern p = new Pattern(0, new ClassObjectType(Person.class));
        p.addConstraint(new TestAlphaConstraint("age > 18"));
        lhs.addChild(p);
        rule.setLhs(lhs);

        List<TerminalNode> terminals = applyRuleImpl(rule);

        // terminal → LIA → AlphaNode → OTN
        BaseNode lia = terminals.get(0).getLeftInput();
        assertThat(lia).isInstanceOf(LeftInputAdapterNode.class);

        BaseNode alpha = lia.getLeftInput();
        assertThat(alpha).isInstanceOf(AlphaNode.class);
        assertThat(((AlphaNode) alpha).getConstraint()).isInstanceOf(TestAlphaConstraint.class);

        assertThat(alpha.getLeftInput()).isInstanceOf(ObjectTypeNode.class);
        assertThat(((ClassObjectType) ((ObjectTypeNode) alpha.getLeftInput()).getObjectType()).getClassType())
                .isEqualTo(Person.class);
    }

    @Test
    public void testTwoAlphaConstraintsChainsNodes() {
        RuleImpl rule = new RuleImpl("r1");
        GroupElement lhs = GroupElementFactory.newAndInstance();
        Pattern p = new Pattern(0, new ClassObjectType(Person.class));
        p.addConstraint(new TestAlphaConstraint("age > 18"));
        p.addConstraint(new TestAlphaConstraint("city == London"));
        lhs.addChild(p);
        rule.setLhs(lhs);

        List<TerminalNode> terminals = applyRuleImpl(rule);

        // terminal → LIA → AlphaNode2 → AlphaNode1 → OTN
        BaseNode lia    = terminals.get(0).getLeftInput();
        BaseNode alpha2 = lia.getLeftInput();
        assertThat(alpha2).isInstanceOf(AlphaNode.class);

        BaseNode alpha1 = alpha2.getLeftInput();
        assertThat(alpha1).isInstanceOf(AlphaNode.class);

        assertThat(alpha1.getLeftInput()).isInstanceOf(ObjectTypeNode.class);
    }

    @Test
    public void testAlphaConstraintWithJoin() {
        // Person(age > 18), String — AlphaNode in left path, plain OTN in right
        RuleImpl rule = new RuleImpl("r1");
        GroupElement lhs = GroupElementFactory.newAndInstance();
        Pattern p1 = new Pattern(0, new ClassObjectType(Person.class));
        p1.addConstraint(new TestAlphaConstraint("age > 18"));
        lhs.addChild(p1);
        lhs.addChild(new Pattern(1, new ClassObjectType(String.class)));
        rule.setLhs(lhs);

        List<TerminalNode> terminals = applyRuleImpl(rule);

        BaseNode join = terminals.get(0).getLeftInput();
        assertThat(join).isInstanceOf(JoinNode.class);

        // left: LIA → AlphaNode → OTN
        BaseNode lia = join.getLeftInput();
        assertThat(lia).isInstanceOf(LeftInputAdapterNode.class);
        assertThat(lia.getLeftInput()).isInstanceOf(AlphaNode.class);

        // right: plain OTN (no alpha)
        assertThat(((JoinNode) join).getRightInput()).isInstanceOf(ObjectTypeNode.class);
    }

    // -------------------------------------------------------------------------
    // Minimal constraint implementations for structural tests
    // -------------------------------------------------------------------------

    static class TestAlphaConstraint implements AlphaNodeFieldConstraint {
        private final String expression;
        TestAlphaConstraint(String expression) { this.expression = expression; }

        @Override public boolean isAllowed(FactHandle handle, ValueResolver valueResolver) { return true; }
        @Override public AlphaNodeFieldConstraint cloneIfInUse() { return this; }
        @Override public boolean isTemporal() { return false; }
        @Override public Constraint.ConstraintType getType() { return Constraint.ConstraintType.ALPHA; }
        @Override public Declaration[] getRequiredDeclarations() { return new Declaration[0]; }
        @Override public void replaceDeclaration(Declaration oldDecl, Declaration newDecl) { }
        @Override public Constraint clone() { return this; }
        @Override public void writeExternal(ObjectOutput out) throws IOException { }
        @Override public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException { }
        @Override public String toString() { return "Alpha(" + expression + ")"; }
    }

    @SuppressWarnings("unchecked")
    static class TestBetaConstraint implements BetaConstraint<Object> {
        private final String expression;
        TestBetaConstraint(String expression) { this.expression = expression; }

        @Override public boolean isAllowedCachedLeft(Object context, FactHandle handle) { return true; }
        @Override public boolean isAllowedCachedRight(BaseTuple tuple, Object context) { return true; }
        @Override public Object createContext() { return null; }
        @Override public BetaConstraint<Object> cloneIfInUse() { return this; }
        @Override public boolean isTemporal() { return false; }
        @Override public Constraint.ConstraintType getType() { return Constraint.ConstraintType.BETA; }
        @Override public Declaration[] getRequiredDeclarations() { return new Declaration[0]; }
        @Override public void replaceDeclaration(Declaration oldDecl, Declaration newDecl) { }
        @Override public Constraint clone() { return this; }
        @Override public void writeExternal(ObjectOutput out) throws IOException { }
        @Override public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException { }
        @Override public String toString() { return "Beta(" + expression + ")"; }
    }
}
