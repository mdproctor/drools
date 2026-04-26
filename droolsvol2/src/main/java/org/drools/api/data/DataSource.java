package org.drools.api.data;

import java.util.List;

public interface DataSource<T> {

    /**
     * Returns a snapshot of all currently held elements.
     * Used for synchronous scope evaluation (not/exists checks at rule-fire time).
     */
    default List<T> asList() {
        throw new UnsupportedOperationException("asList() not supported by this DataSource implementation");
    }
}
