package org.drools.core;

import org.drools.api.data.ObjectHandle;

import java.util.ArrayList;
import java.util.List;

public class RecordingUnitProcessor<CTX, T> implements UnitProcessor<CTX, T> {
    private final int            index;
    private final List<LogEntry> log = new ArrayList<>();

    public RecordingUnitProcessor(int index) {
        this.index = index;
    }

    public List<LogEntry> getLog() { return log; }

    @Override
    public void add(UnitInstance<CTX> unit, ObjectHandle<T> h) {
        log.add(new LogEntry(index, "add", h, h.getObject()));
    }

    @Override
    public void update(UnitInstance<CTX> unit, ObjectHandle<T> h) {
        log.add(new LogEntry(index, "update", h, h.getObject()));
    }

    @Override
    public void remove(UnitInstance<CTX> unit, ObjectHandle<T> h) {
        log.add(new LogEntry(index, "remove", h, h.getObject()));
    }
}
