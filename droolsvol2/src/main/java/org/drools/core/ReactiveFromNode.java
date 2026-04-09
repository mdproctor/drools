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
package org.drools.core;

/**
 * Vol2 reactive from-node — stub pending vol2 reactive DataSource integration.
 * TODO #6650: implement vol2 ReactiveFromNode (DataSource change notification)
 */
public class ReactiveFromNode extends FromNode<ReactiveFromNode.ReactiveFromMemory> {

    public ReactiveFromNode() { }

    public ReactiveFromNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    @Override
    public ReactiveFromMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return new ReactiveFromMemory();
    }

    /**
     * Memory for reactive from-node — listens to DataSource changes.
     * TODO #6650: implement reactive memory once vol2 DataSource subscription is built.
     */
    public static class ReactiveFromMemory extends FromMemory {
    }
}
