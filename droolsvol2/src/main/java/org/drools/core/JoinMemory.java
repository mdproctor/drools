package org.drools.core;

import org.drools.api.data.ObjectHandle;
import java.util.ArrayList;
import java.util.List;

public class JoinMemory {
    private final List<ObjectHandle<?>> leftHandles  = new ArrayList<>();
    private final List<ObjectHandle<?>> rightHandles = new ArrayList<>();

    public void addLeft(ObjectHandle<?> h)    { leftHandles.add(h); }
    public void removeLeft(ObjectHandle<?> h) { leftHandles.remove(h); }
    public void addRight(ObjectHandle<?> h)   { rightHandles.add(h); }
    public void removeRight(ObjectHandle<?> h){ rightHandles.remove(h); }

    public List<ObjectHandle<?>> getLeftHandles()  { return leftHandles; }
    public List<ObjectHandle<?>> getRightHandles() { return rightHandles; }
}
