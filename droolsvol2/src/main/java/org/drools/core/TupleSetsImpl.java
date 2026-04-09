package org.drools.core;

/**
 * TODO #6650: Temporary stub — TupleSetsImpl not used in this version of vol2.
 * Kept as an empty shell so SegmentMemory compiles.
 */
public class TupleSetsImpl implements TupleSets {
    public TupleImpl getInsertFirst()           { return null; }
    public TupleImpl getDeleteFirst()           { return null; }
    public TupleImpl getUpdateFirst()           { return null; }
    public TupleImpl getNormalizedDeleteFirst() { return null; }
    public int getInsertSize()                  { return 0; }
    public boolean isEmpty()                    { return true; }
    public void resetAll()                      { }
    public void clear()                         { }
    public boolean addInsert(TupleImpl t)           { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public boolean addDelete(TupleImpl t)           { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public boolean addUpdate(TupleImpl t)           { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public boolean addNormalizedDelete(TupleImpl t) { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public void removeInsert(TupleImpl t)       { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public void removeDelete(TupleImpl t)       { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public void removeUpdate(TupleImpl t)       { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public void addAll(TupleSets source)        { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public void addTo(TupleSets target)         { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public TupleSets takeAll()                  { throw new UnsupportedOperationException("vol2 stub — see #6650"); }
    public String toStringSizes()               { return "TupleSetsImpl[stub]"; }
}
