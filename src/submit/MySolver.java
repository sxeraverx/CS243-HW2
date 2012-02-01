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

	HashMap<BasicBlock,Flow.DataflowObject> basicBlockIn  = new HashMap<BasicBlock,Flow.DataflowObject>();
	HashMap<BasicBlock,Flow.DataflowObject> basicBlockOut = new HashMap<BasicBlock,Flow.DataflowObject>();

	for(Iterator iter = cfg.reversePostOrderIterator(); iter.hasNext();)
	    {
		BasicBlock b = (BasicBlock)iter.next();
		if(b.size()>0)
		    {
			basicBlockIn.put(b, analysis.isForward() ? analysis.getIn(b.getQuad(0)) : analysis.getOut(b.getLastQuad()));
			basicBlockOut.put(b, analysis.isForward() ? analysis.getOut(b.getLastQuad()) : analysis.getIn(b.getQuad(0)));
		    }
		else
		    {
			basicBlockIn.put(b, analysis.newTempVar());
			basicBlockOut.put(b, analysis.newTempVar());
		    }
		blocksNeedingUpdate.add(b);
	    }

	while(blocksNeedingUpdate.size() > 0)
	    {
		BasicBlock nextBlock = blocksNeedingUpdate.iterator().next(); //take out next block to update
		blocksNeedingUpdate.remove(nextBlock); //remove it from the queue
		//System.out.println(nextBlock + " " + basicBlockIn.get(nextBlock));

		/*if(nextBlock.size() == 0)
		continue;*/
	   
		Flow.DataflowObject oldIn = basicBlockIn.get(nextBlock);
		Flow.DataflowObject newIn = analysis.newTempVar();
		newIn.copy(oldIn);
		for(BasicBlock pred : (analysis.isForward() ? nextBlock.getPredecessors() : nextBlock.getSuccessors()))
		    {
			if(pred.equals(cfg.entry()))
			    newIn.meetWith(analysis.getEntry());
			else if(pred.equals(cfg.exit()))
			    newIn.meetWith(analysis.getExit());
			else
			    newIn.meetWith(basicBlockOut.get(pred));
		    }
		//Flow.DataflowObject top = analysis.newTempVar();
		//top.setToTop();
		Flow.DataflowObject out = basicBlockOut.get(nextBlock);
		//if(newIn.equals(oldIn)) //no change in input, and we've already processed once, so there will be no change in output.
		//    continue;
		basicBlockIn.put(nextBlock, newIn);
		oldIn.copy(newIn);
		ListIterator quadIterator = analysis.isForward() ? nextBlock.iterator() : nextBlock.backwardIterator();

		Flow.DataflowObject currentIn = analysis.newTempVar();
		currentIn = newIn;
		//System.out.println(nextBlock);
		while(quadIterator.hasNext())
		    {
			Quad nextQuad = (Quad)quadIterator.next();
			//System.out.println(nextQuad);
			if(analysis.isForward())
			    analysis.setIn(nextQuad, currentIn);
			else
			    analysis.setOut(nextQuad, currentIn);
			analysis.processQuad(nextQuad);
			if(analysis.isForward())
			    currentIn = analysis.getOut(nextQuad);
			else
			    currentIn = analysis.getIn(nextQuad);
		    }
		basicBlockOut.put(nextBlock, currentIn);
		if(!out.equals(currentIn))
		    {
		blocksNeedingUpdate.addAll(analysis.isForward() ? nextBlock.getSuccessors() : nextBlock.getPredecessors());
		    }
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
