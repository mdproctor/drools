package org.drools.core.mark;

import org.drools.base.base.ClassObjectType;
import org.drools.base.base.ObjectType;
import org.drools.base.definitions.impl.KnowledgePackageImpl;
import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.reteoo.BaseTuple;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.MutableTypeConstraint;
import org.drools.base.rule.Pattern;
import org.drools.base.rule.constraint.BetaConstraint;
import org.drools.base.rule.constraint.Constraint.ConstraintType;
import org.drools.base.util.index.ConstraintTypeOperator;
import org.drools.core.common.BetaConstraints;
import org.drools.core.common.DefaultFactHandle;
import org.drools.core.impl.InternalRuleBase;
import org.drools.core.impl.KnowledgeBaseImpl;
import org.drools.core.impl.RuleBaseFactory;
import org.drools.core.mark.Predicates.Predicate1;
import org.drools.core.mark.Predicates.Predicate2;
import org.drools.core.mark.Tuples.Tuple1;
import org.drools.core.mark.Tuples.Tuple2;
import org.drools.core.mark.Tuples.Tuple3;
import org.drools.core.mark.VoidFunctions.VoidFunction2;
import org.drools.core.reteoo.ReteooFactHandleFactory;
import org.drools.core.reteoo.Tuple;
import org.drools.core.rule.accessor.FactHandleFactory;
import org.drools.core.test.model.Person;
import org.drools.core.test.model.SecondClass;
import org.drools.core.test.model.StockTick;
import org.drools.kiesession.rulebase.SessionsAwareKnowledgeBase;
import org.junit.Ignore;
import org.junit.Test;
import org.kie.api.runtime.KieSession;
import org.kie.api.runtime.rule.FactHandle;
import org.kie.internal.conf.CompositeBaseConfiguration;

import static org.junit.Assert.assertTrue;

public class BetaCosntraintsIndexingTest {

//        Tuple1<Person>                         t1 = Tuples.from((a) -> a.equals("mark"), Person.class);
//        Tuple2<Person, SecondClass>            t2 = t1.filter((a, b) -> a.equals(b), SecondClass.class);
//        Tuple3<Person, SecondClass, StockTick> t3 = t2.filter((a, b, c) -> a.equals(b) && a.equals(c), StockTick.class);
//
//        Tuples.from((a) -> a.equals("mark"), Person.class)
//                .filter((a, b) -> a.equals(b), SecondClass.class)
//                .filter((a, b, c) -> a.equals(b) && a.equals(c), StockTick.class);


    @Test @Ignore
    public void test1() {
        RuleImpl r1 = new RuleImpl("r1");

        final ObjectType stringObjectType = new ClassObjectType(String.class );
        final ObjectType personObjectType = new ClassObjectType(Person.class );

        final Pattern spattern = new Pattern(0,
                                             stringObjectType,
                                                 "s" );

        final Pattern ppattern = new Pattern(1,
                                             personObjectType,
                                             "p" );

        MarkConstraint sconstraint = new MarkConstraint(new Declaration[] {spattern.getDeclaration()}, spattern);
        sconstraint.setPredicate((Predicate1<String>) (a) -> a.equals("London"));
        sconstraint.setType(ConstraintType.ALPHA);
        sconstraint.setConstraintTypeOperator(ConstraintTypeOperator.EQUAL);
        spattern.addConstraint(sconstraint);

        MarkConstraint pconstraint = new MarkConstraint(new Declaration[] {spattern.getDeclaration(), ppattern.getDeclaration()}, ppattern);
        pconstraint.setPredicate((Predicate2<String, Person>) (a, b) ->
                                                                      a.equals(b.getCity())
                                );
        pconstraint.setType(ConstraintType.BETA);
        pconstraint.setConstraintTypeOperator(ConstraintTypeOperator.EQUAL);
        ppattern.addConstraint(pconstraint);
        r1.addPattern(spattern);
        r1.addPattern(ppattern);


        MarkConsequence<?> c = new MarkConsequence<>("default", new Declaration[] {spattern.getDeclaration(), ppattern.getDeclaration()});
        c.setFunction((VoidFunction2<String, Person>) (s, p) -> System.out.println(p.getName() + " lives in " + s));
        r1.setConsequence(c);


        KnowledgeBaseImpl base = new KnowledgeBaseImpl("default", (CompositeBaseConfiguration)  RuleBaseFactory.newKnowledgeBaseConfiguration());
        KnowledgePackageImpl pkg = new KnowledgePackageImpl();
        pkg.addRule(r1);

        base.addPackage(pkg);

        SessionsAwareKnowledgeBase kbase = new SessionsAwareKnowledgeBase(base);
        KieSession session = kbase.newKieSession();
        session.insert("London");
        Person p = new Person("yoda", 300);
        p.setCity("London");
        session.insert(p);
        session.fireAllRules();


        //pPattern.addConstraint();
//        MarkBetaConstraints c = new MarkBetaConstraints() {
//            @Override
//            public boolean isAllowedCachedLeft(MarkContextEntry context, FactHandle handle) {
//                return context.tp.get(0).equals(handle.getObject());
//            }
//
//            @Override
//            public boolean isAllowedCachedRight(MarkContextEntry context, Tuple tuple) {
//                return context.fh.getObject().equals(tuple.get(0).getObject());
//            }
//        };

        //pPattern.addConstraint(c);
    }
}
