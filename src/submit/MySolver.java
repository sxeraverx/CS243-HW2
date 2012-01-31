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

	//Initialize the set of blocks needing update to the algorithm to
	//only the entry point
	Set<BasicBlock> blocksNeedingUpdate = new LinkedHashSet<BasicBlock>();
	BasicBlock startBlock = analysis.isForward() ? cfg.entry() : cfg.exit();
	assert startBlock.size() == 0;
	if(analysis.isForward())
	    {
		assert startBlock.getSuccessors().size() == 1;
		assert startBlock.getSuccessors().get(0).size() > 0;
		startBlock = startBlock.getSuccessors().get(0);
	    }
	else
	    {
		assert startBlock.getPredecessors().size() == 1;
		assert startBlock.getPredecessors().get(0).size() > 0;
		startBlock = startBlock.getPredecessors().get(0);
	    }
	blocksNeedingUpdate.add( startBlock );

	while(blocksNeedingUpdate.size() > 0)
	    {
		BasicBlock nextBlock = blocksNeedingUpdate.iterator().next(); //take out next block to update
		blocksNeedingUpdate.remove(nextBlock); //remove it from the queue

		assert nextBlock.size() > 0 || ((analysis.isForward() && nextBlock.equals(cfg.exit())) || (!analysis.isForward() && nextBlock.equals(cfg.entry())));
		if(nextBlock.size() == 0)
		    continue;
	   
		Flow.DataflowObject oldIn;
		oldIn = analysis.getIn((analysis.isForward() ? nextBlock.getQuad(0) : nextBlock.getLastQuad()));
		Flow.DataflowObject newIn = analysis.newTempVar();
		newIn.copy(oldIn);
		for(BasicBlock pred : (analysis.isForward() ? nextBlock.getPredecessors() : nextBlock.getSuccessors()))
		    {
			if(pred.equals(cfg.entry()))
			    newIn.meetWith(analysis.getEntry());
			else if(pred.equals(cfg.exit()))
			    newIn.meetWith(analysis.getExit());
			else
			    newIn.meetWith(analysis.getOut((analysis.isForward() ? pred.getLastQuad() : pred.getQuad(0))));
		    }
		Flow.DataflowObject top = analysis.newTempVar();
		top.setToTop();
		Flow.DataflowObject out = analysis.getOut((analysis.isForward() ? nextBlock.getLastQuad() : nextBlock.getQuad(0)));
		if(newIn.equals(oldIn) && !out.equals(top)) //no change in input, and we've already processed once, so there will be no change in output.
		    continue;
		ListIterator quadIterator = analysis.isForward() ? nextBlock.iterator() : nextBlock.backwardIterator();

		Flow.DataflowObject currentIn = analysis.newTempVar();
		currentIn = newIn;
		
		while(quadIterator.hasNext())
		    {
			Quad nextQuad = (Quad)quadIterator.next();
			analysis.setIn(nextQuad, currentIn);
			analysis.processQuad(nextQuad);
			currentIn = analysis.getOut(nextQuad);
		    }
		blocksNeedingUpdate.addAll(analysis.isForward() ? nextBlock.getSuccessors() : nextBlock.getPredecessors());
		if((analysis.isForward() ? nextBlock.getSuccessors().contains(cfg.exit()) : nextBlock.getPredecessors().contains(cfg.entry())))
                    {
			Flow.DataflowObject exit = analysis.isForward() ? analysis.getExit() : analysis.getEntry();
			exit.meetWith(currentIn);
                        if(analysis.isForward())
			    analysis.setExit(exit);
			else
			    analysis.setEntry(exit);
                    }

	    }

        /***********************
         * Your code goes here *
         ***********************/

        // this needs to come last.
        analysis.postprocess(cfg);
    }
}
