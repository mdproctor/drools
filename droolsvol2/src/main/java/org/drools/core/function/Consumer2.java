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
import io.quarkiverse.permuplate.PermuteTypeParam;

import java.io.Serializable;

@Permute(varName = "i", from = "3", to = "10", className = "Consumer${i}")
public interface Consumer2<A, @PermuteTypeParam(varName = "j", from = "2", to = "${i}", name = "${alpha(j)}") B>
        extends Consumer, Serializable {

    @PermuteConst("${i}") int ARITY = 2;

    void accept(A a, @PermuteParam(varName = "j", from = "2", to = "${i}", type = "${alpha(j)}", name = "${lower(j)}") B b);

    default int getArity() {
        return ARITY;
    }
}
