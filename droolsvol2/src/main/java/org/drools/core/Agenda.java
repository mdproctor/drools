package org.drools.core;

import java.util.ArrayDeque;

/**
 * Per-UnitInstance agenda for fn (deferred head) tasks.
 * fn handlers enqueue a Runnable; the agenda drains after each
 * DataStore mutation via UnitInstance.add/update/remove().
 */
class Agenda {

    private final ArrayDeque<Runnable> tasks = new ArrayDeque<>();

    void enqueue(Runnable task) { tasks.addLast(task); }

    void drain() {
        Runnable task;
        while ((task = tasks.pollFirst()) != null) {
            task.run();
        }
    }
}
