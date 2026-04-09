/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
package org.drools.core.function;

import io.quarkiverse.permuplate.Permute;
import io.quarkiverse.permuplate.PermuteConst;
import io.quarkiverse.permuplate.PermuteParam;
import io.quarkiverse.permuplate.PermuteReturn;
import io.quarkiverse.permuplate.PermuteTypeParam;

import java.io.Serializable;

@Permute(varName = "i", from = 3, to = 10, className = "Predicate${i}")
public interface Predicate2<A, @PermuteTypeParam(varName = "j", from = "2", to = "${i}", name = "${alpha(j)}") B>
        extends Predicate, Serializable {

    @PermuteConst("${i}") int ARITY = 2;

    boolean test(A a, @PermuteParam(varName = "j", from = "2", to = "${i}", type = "${alpha(j)}", name = "${lower(j)}") B b);

    default int getArity() {
        return ARITY;
    }

    @PermuteReturn(className = "Predicate${i}", typeArgVarName = "j", typeArgFrom = "1", typeArgTo = "${i}", typeArgName = "${alpha(j)}")
    default Predicate2<A, B> negate() {
        return (A a, @PermuteParam(varName = "j", from = "2", to = "${i}", type = "${alpha(j)}", name = "${lower(j)}") B b) -> !test(a, b);
    }
}
