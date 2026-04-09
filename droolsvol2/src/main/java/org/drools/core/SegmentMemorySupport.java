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
 * TODO #6650: Temporary interface — vol2 segment memory initialisation not yet implemented.
 * Adapts vol1 SegmentMemorySupport (LeftTupleSource/LeftTupleNode → BaseNode).
 */
public interface SegmentMemorySupport {
    SegmentMemory createSegmentMemoryLazily(BaseNode segmentRoot);
    SegmentMemory createChildSegment(BaseNode node);
    SegmentMemory createChildSegmentLazily(BaseNode node);

    // TODO #6650: path memory init for subnetworks and query segments — not yet implemented in vol2
    default void initializePathMemory(TupleToObjectNode tton) {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }

    default SegmentMemory getQuerySegmentMemory(QueryElementNode node) {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }
}
