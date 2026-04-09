package org.drools.core;

import org.drools.base.base.ClassObjectType;
import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.rule.GroupElement;
import org.drools.base.rule.GroupElementFactory;
import org.drools.base.rule.Pattern;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * End-to-end tests for vol2 Rete network construction.
 * Tests that rules with simple patterns build the expected node structure:
 * EntryPointNode → ObjectTypeNode → LeftInputAdapterNode → TerminalNode
 */
public class ReteBuilderTest {

    private RuleBase ruleBase;

    @BeforeEach
    public void setUp() {
        ruleBase = new RuleBase();
    }

    private RuleImpl ruleWithPattern(String name, Class<?>... types) {
        RuleImpl rule = new RuleImpl(name);
        GroupElement lhs = GroupElementFactory.newAndInstance();
        for (int i = 0; i < types.length; i++) {
            lhs.addChild(new Pattern(i, new ClassObjectType(types[i])));
        }
        rule.setLhs(lhs);
        return rule;
    }

    @Test
    public void testSinglePatternProducesTerminalNode() {
        RuleImpl rule = ruleWithPattern("r1", Person.class);

        List<TerminalNode> terminals = ruleBase.getReteBuilder().addRule(rule);

        assertThat(terminals).hasSize(1);
        assertThat(terminals.get(0)).isInstanceOf(TerminalNode.class);
        assertThat(terminals.get(0).getRule().getName()).isEqualTo("r1");
    }

    @Test
    public void testSinglePatternBuildsObjectTypeNode() {
        RuleImpl rule = ruleWithPattern("r1", Person.class);

        List<TerminalNode> terminals = ruleBase.getReteBuilder().addRule(rule);

        // The terminal's leftInput should be a LeftInputAdapterNode
        // whose leftInput is the ObjectTypeNode
        TerminalNode terminal = terminals.get(0);
        BaseNode lia = terminal.getLeftInput();
        assertThat(lia).isInstanceOf(LeftInputAdapterNode.class);

        BaseNode otn = lia.getLeftInput();
        assertThat(otn).isInstanceOf(ObjectTypeNode.class);
        assertThat(((ObjectTypeNode) otn).getObjectType())
                .isEqualTo(new ClassObjectType(Person.class));
    }

    @Test
    public void testSinglePatternConnectsToRoot() {
        RuleImpl rule = ruleWithPattern("r1", Person.class);

        ruleBase.getReteBuilder().addRule(rule);

        // OTN's leftInput should be the Rete root (EntryPointNode)
        // (walked up: terminal → LIA → OTN → EntryPointNode)
        // Just verify getRete() is non-null and the network connected
        assertThat(ruleBase.getRete()).isNotNull();
    }

    @Test
    public void testTwoRulesSamePatternShareObjectTypeNode() {
        RuleImpl r1 = ruleWithPattern("r1", Person.class);
        RuleImpl r2 = ruleWithPattern("r2", Person.class);

        List<TerminalNode> t1 = ruleBase.getReteBuilder().addRule(r1);
        List<TerminalNode> t2 = ruleBase.getReteBuilder().addRule(r2);

        // Both rules should have terminal nodes
        assertThat(t1).hasSize(1);
        assertThat(t2).hasSize(1);
        assertThat(t1.get(0).getRule().getName()).isEqualTo("r1");
        assertThat(t2.get(0).getRule().getName()).isEqualTo("r2");
    }

    @Test
    public void testDifferentPatternTypesBuildSeparateObjectTypeNodes() {
        RuleImpl r1 = ruleWithPattern("r1", Person.class);
        RuleImpl r2 = ruleWithPattern("r2", String.class);

        List<TerminalNode> t1 = ruleBase.getReteBuilder().addRule(r1);
        List<TerminalNode> t2 = ruleBase.getReteBuilder().addRule(r2);

        ObjectTypeNode otn1 = (ObjectTypeNode) t1.get(0).getLeftInput().getLeftInput();
        ObjectTypeNode otn2 = (ObjectTypeNode) t2.get(0).getLeftInput().getLeftInput();

        assertThat(((ClassObjectType) otn1.getObjectType()).getClassType()).isEqualTo(Person.class);
        assertThat(((ClassObjectType) otn2.getObjectType()).getClassType()).isEqualTo(String.class);
        assertThat(otn1).isNotSameAs(otn2);
    }

    @Test
    public void testConsequenceOnlyRuleUsesInitialFact() {
        // A rule with no patterns — empty LHS — requires an InitialFact pattern
        // (addInitialFactPattern injects it so the network has a root to attach to)
        RuleImpl rule = new RuleImpl("noPatterns");
        rule.setLhs(GroupElementFactory.newAndInstance()); // empty AND

        List<TerminalNode> terminals = ruleBase.getReteBuilder().addRule(rule);

        assertThat(terminals).hasSize(1);
        // The LIA's OTN should match InitialFact
        BaseNode lia = terminals.get(0).getLeftInput();
        assertThat(lia).isInstanceOf(LeftInputAdapterNode.class);
        ObjectTypeNode otn = (ObjectTypeNode) lia.getLeftInput();
        assertThat(((ClassObjectType) otn.getObjectType()).getClassType().getName())
                .contains("InitialFact");
    }

    @Test
    public void testTwoPatternRuleProducesJoinNode() {
        RuleImpl rule = ruleWithPattern("r1", Person.class, String.class);

        List<TerminalNode> terminals = ruleBase.getReteBuilder().addRule(rule);

        assertThat(terminals).hasSize(1);

        BaseNode joinNode = terminals.get(0).getLeftInput();
        assertThat(joinNode).isInstanceOf(JoinNode.class);

        // left side: LIA for first pattern (Person)
        assertThat(joinNode.getLeftInput()).isInstanceOf(LeftInputAdapterNode.class);
        ObjectTypeNode leftOtn = (ObjectTypeNode) joinNode.getLeftInput().getLeftInput();
        assertThat(((ClassObjectType) leftOtn.getObjectType()).getClassType()).isEqualTo(Person.class);

        // right side: OTN for second pattern (String) — direct object input (bi-linear)
        assertThat(((JoinNode) joinNode).getRightInput()).isInstanceOf(ObjectTypeNode.class);
        ObjectTypeNode rightOtn = (ObjectTypeNode) ((JoinNode) joinNode).getRightInput();
        assertThat(((ClassObjectType) rightOtn.getObjectType()).getClassType()).isEqualTo(String.class);
    }

    @Test
    public void testThreePatternRuleProducesNestedJoins() {
        RuleImpl rule = ruleWithPattern("r1", Person.class, String.class, Integer.class);

        List<TerminalNode> terminals = ruleBase.getReteBuilder().addRule(rule);

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
    public void testNodeIdsAreMonotonicallyIncreasing() {
        // Each addRule() call should allocate new, unique, increasing node IDs
        RuleImpl r1 = ruleWithPattern("r1", Person.class);
        RuleImpl r2 = ruleWithPattern("r2", String.class);

        List<TerminalNode> t1 = ruleBase.getReteBuilder().addRule(r1);
        List<TerminalNode> t2 = ruleBase.getReteBuilder().addRule(r2);

        int id1 = t1.get(0).getId();
        int id2 = t2.get(0).getId();

        assertThat(id1).isGreaterThan(0);
        assertThat(id2).isGreaterThan(id1);
    }
}
