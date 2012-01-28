package submit;

// some useful things to import. add any additional imports you need.
import joeq.Compiler.Quad.*;
import flow.Flow;
import java.util.*;

/**
 * Skeleton class for implementing the Flow.Solver interface.
 */
public class MySolver implements Flow.Solver {

    protected Flow.Analysis analysis;

    /**
     * Sets the analysis.  When visitCFG is called, it will
     * perform this analysis on a given CFG.
     *
     * @param analyzer The analysis to run
     */
    public void registerAnalysis(Flow.Analysis analyzer) {
        this.analysis = analyzer;
    }

    /**
     * Runs the solver over a given control flow graph.  Prior
     * to calling this, an analysis must be registered using
     * registerAnalysis
     *
     * @param cfg The control flow graph to analyze.
     */
    public void visitCFG(ControlFlowGraph cfg) {

        // this needs to come first.
        analysis.preprocess(cfg);

	Set<BasicBlock> blocksNeedingUpdate = new LinkedHashSet<BasicBlock>();

	BasicBlock startBlock = analysis.isForward() ? cfg.entry() : cfg.exit();
	
	blocksNeedingUpdate.add(startBlock);
	while(blocksNeedingUpdate.size() > 0)
	    {
		BasicBlock nextBlock = blocksNeedingUpdate.iterator().next();
		System.out.println(nextBlock);
		System.out.println(nextBlock.size());
		blocksNeedingUpdate.remove(nextBlock);
		if(nextBlock.equals(cfg.entry()) && analysis.isForward())
		    blocksNeedingUpdate.addAll(nextBlock.getSuccessors());
		else if(nextBlock.equals(cfg.entry()))
		    continue;
		if(nextBlock.equals(cfg.exit()) && !analysis.isForward())
		    blocksNeedingUpdate.addAll(nextBlock.getPredecessors());
		else if(nextBlock.equals(cfg.entry()))
		    continue;
	   
		Flow.DataflowObject oldIn;
		oldIn = analysis.getIn((analysis.isForward() ? nextBlock.getQuad(0) : nextBlock.getLastQuad()));
		Flow.DataflowObject newIn = analysis.newTempVar();
		newIn.copy(oldIn);
		for(BasicBlock pred : (analysis.isForward() ? nextBlock.getPredecessors() : nextBlock.getSuccessors()))
		    {
			if(pred.size() >0)
			    newIn.meetWith(analysis.getOut((analysis.isForward() ? pred.getQuad(0) : pred.getLastQuad())));
			else
			    ;
		    }
		Flow.DataflowObject oldOut;
		oldOut = analysis.getOut((analysis.isForward() ? nextBlock.getLastQuad() : nextBlock.getQuad(0)));
		Flow.DataflowObject newOut = analysis.newTempVar();
		newOut.copy(oldOut);
		for(int i = 0; i < nextBlock..next(); iter.hasNext();)
		    {
			System.out.println(q);
		    }
		analysis.setIn((analysis.isForward() ? nextBlock.getQuad(0) : nextBlock.getLastQuad()), newIn);
	    }


        /***********************
         * Your code goes here *
         ***********************/

        // this needs to come last.
        analysis.postprocess(cfg);
    }
}
