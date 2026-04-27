package org.drools.core;

import org.drools.api.data.DataStore;
import org.junit.jupiter.api.Test;

public class ExtensionPointTest {
    record CTX(DataStore<Person> persons,
              DataStore<Library> libraries,
              DataStore<Room> rooms,
              DataStore<Shelf> shelf,
              DataStore<Book> books) {};

    record P3(String p3_1, String p3_2, String p3_3) {
        public static final P3 V = new P3(null,null,null);
    };

    @Test
    public void testExtends1() {
        RuleBuilder<CTX> builder = new RuleBuilder<>();

        var ext = builder.rule("Rule1")
                          .<P3>params()
                          .extensionPoint();

        builder.rule("Rule1Ext1")
               .extendsRule(ext)
               .filter(params -> params.p3_1() == "Jonny Alpha");

        builder.rule("Rule2Ext1")
               .extendsRule(ext)
               .join(builder.from(CTX::persons))
               .filter((params, person) -> person.name() == "Jonny Alpha");

    }

    @Test
    public void testExtends2() {
        RuleBuilder<CTX> builder = new RuleBuilder<>();

        var ext = builder.rule("Rule1")
                          .<P3>params()
                          .join(builder.from(CTX::persons))
                          .extensionPoint();
        builder.rule("Rule1ExtRule1")
               .extendsRule(ext)
               .filter((params, person) -> person.name()== "Jonny Alpha");

        builder.rule("Rule2ExtRule1")
               .extendsRule(ext)
               .join(builder.from(CTX::libraries))
               .filter((params, person, library) -> person.name() == library.name());
    }

    @Test
    public void testExtends3() {
        RuleBuilder<CTX> builder = new RuleBuilder<>();

        var ext = builder.rule("Rule1")
                          .<P3>params()
                          .join(builder.from(CTX::persons))
                          .join(builder.from(CTX::libraries))
                          .extensionPoint();
        builder.rule("Rule1ExtRule1")
               .extendsRule(ext)
               .filter((params, person, library) -> person.name() == library.name());
        builder.rule("Rule2ExtRule1")
               .extendsRule(ext)
               .join(builder.from(CTX::rooms))
               .filter((params, person, library, room) -> person.name() == room.name());
    }

    @Test
    public void testExtends4() {
        RuleBuilder<CTX> builder = new RuleBuilder<>();

        var ext = builder.rule("Rule1")
                          .<P3>params()
                          .join(builder.from(CTX::persons))
                          .join(builder.from(CTX::libraries))
                          .join(builder.from(CTX::rooms))
                          .extensionPoint();
        builder.rule("Rule1ExtRule1")
               .extendsRule(ext)
               .filter((params, person, library, room) -> person.name() == room.name());
        builder.rule("Rule2ExtRule1")
               .extendsRule(ext)
               .join(builder.from(CTX::shelf))
               .filter((params, person, library, room, shelf) -> person.name() == room.name());
    }
}
