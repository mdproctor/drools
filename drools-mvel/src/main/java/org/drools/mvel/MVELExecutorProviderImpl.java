package org.drools.mvel;

import org.drools.core.util.MVELExecutor;
import org.drools.core.util.MVELExecutorProvider;

public class MVELExecutorProviderImpl implements MVELExecutorProvider {
    @Override
    public MVELExecutor get() {
        return (MVELExecutor) MVELSafeHelper.getEvaluator();
    }
}
