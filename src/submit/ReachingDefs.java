package submit;

// some useful things to import. add any additional imports you need.
import java.util.*;
import joeq.Compiler.Quad.*;
import joeq.Compiler.Quad.Operand.RegisterOperand;
import flow.Flow;

/**
 * Skeleton class for implementing a reaching definition analysis
 * using the Flow.Analysis interface.
 */
public class ReachingDefs implements Flow.Analysis {

    /**
     * Class for the dataflow objects in the ReachingDefs analysis.
     * You are free to change this class or move it to another file.
     */
    public static class MyDataflowObject implements Flow.DataflowObject {
        /**
         * Methods from the Flow.DataflowObject interface.
         * See Flow.java for the meaning of these methods.
         * These need to be filled in.
         */
        private Map<String, Set<Integer>> set;
        //TODO: need universalSet in reaching definition?
        public static Map<String, Set<Integer>> universalSet;
        /* constructor */
        public MyDataflowObject () { 
          set = new HashMap<String, Set<Integer>>();
        } 

        public void setToTop() { 
          set = new HashMap<String, Set<Integer>>();
        }
        public void setToBottom() { 
          set = new HashMap<String, Set<Integer>>(universalSet);
        }
        
        /* Reaching Definition, meet is union  */
        public void meetWith (Flow.DataflowObject o) {
          MyDataflowObject a = (MyDataflowObject) o;
          Set<String> keys = a.set.keySet();
          for(String key : keys){
            Set<Integer> l = set.get(key);
            if(l== null)
              set.put(key, l = new TreeSet());
            l.addAll(a.set.get(key));
          }
        }

        public void copy (Flow.DataflowObject o) {
          MyDataflowObject a = (MyDataflowObject) o;
          set = new HashMap<String, Set<Integer>>(a.set);
        }

        /**
         * toString() method for the dataflow objects which is used
         * by postprocess() below.  The format of this method must
         * be of the form "[ID0, ID1, ID2, ...]", where each ID is
         * the identifier of a quad defining some register, and the
         * list of IDs must be sorted.  See src/test/test.rd.out
         * for example output of the analysis.  The output format of
         * your reaching definitions analysis must match this exactly.
         */
        @Override
        public String toString() {
          Set<Integer> l = new TreeSet();
          Set<String> keys = set.keySet();
          for( String key : keys)
            l.addAll(set.get(key)); 
          return l.toString();
        }
        
        public void genVar(String v, int id) {
          Set<Integer> l = set.get(v);
          if(l == null )
            set.put(v, l=new TreeSet<Integer> ());
          l.add(id);
        //    System.out.println(q.getID());
        }
        public void killVar(String v) {
          set.remove(v);
        }
    }

    /**
     * Dataflow objects for the interior and entry/exit points
     * of the CFG. in[ID] and out[ID] store the entry and exit
     * state for the input and output of the quad with identifier ID.
     *
     * You are free to modify these fields, just make sure to
     * preserve the data printed by postprocess(), which relies on these.
     */
    private MyDataflowObject[] in, out;
    private MyDataflowObject entry, exit;

    /**
     * This method initializes the datflow framework.
     *
     * @param cfg  The control flow graph we are going to process.
     */
    public void preprocess(ControlFlowGraph cfg) {
        // this line must come first.
        System.out.println("Method: "+cfg.getMethod().getName().toString());

        // get the amount of space we need to allocate for the in/out arrays.
        QuadIterator qit = new QuadIterator(cfg);
        int max = 0;
        while (qit.hasNext()) {
            int id = qit.next().getID();
            if (id > max) 
                max = id;
        }
        max += 1;

        // allocate the in and out arrays.
        in = new MyDataflowObject[max];
        out = new MyDataflowObject[max];

        // initialize the contents of in and out.
        qit = new QuadIterator(cfg);
        while (qit.hasNext()) {
            int id = qit.next().getID();
            in[id] = new MyDataflowObject();
            out[id] = new MyDataflowObject();
        }

        // initialize the entry and exit points.
        entry = new MyDataflowObject();
        exit = new MyDataflowObject();

        /************************************************
         * Your remaining initialization code goes here *
         ************************************************/
        Map<String, Set<Integer>> s = new HashMap<String, Set<Integer>>();
        MyDataflowObject.universalSet = s;
        qit = new QuadIterator(cfg);
        while (qit.hasNext()) {
          Quad q = qit.next();
          for(RegisterOperand def : q.getDefinedRegisters()){
            String reg_name = new String (def.getRegister().toString());
            Set<Integer> l = s.get(reg_name);
            if(l == null)
              s.put(reg_name, l=new TreeSet<Integer>());
            l.add(q.getID());
//            System.out.println(q.getID());
          }
        }
    }

    /**
     * This method is called after the fixpoint is reached.
     * It must print out the dataflow objects associated with
     * the entry, exit, and all interior points of the CFG.
     * Unless you modify in, out, entry, or exit you shouldn't
     * need to change this method.
     *
     * @param cfg  Unused.
     */
    public void postprocess (ControlFlowGraph cfg) {
        System.out.println("entry: " + entry.toString());
        for (int i=0; i<in.length; i++) {
            if (in[i] != null) {
                System.out.println(i + " in:  " + in[i].toString());
                System.out.println(i + " out: " + out[i].toString());
            }
        }
        System.out.println("exit: " + exit.toString());
    }

    /**
     * Other methods from the Flow.Analysis interface.
     * See Flow.java for the meaning of these methods.
     * These need to be filled in.
     */

    public Flow.DataflowObject newTempVar() { 
      return new MyDataflowObject (); 
    }
    public boolean isForward () { return true; }
    public Flow.DataflowObject getEntry() { 
      Flow.DataflowObject result = newTempVar();
      result.copy(entry);
      return result; 
    }
    public Flow.DataflowObject getExit() { 
      Flow.DataflowObject result = newTempVar();
      result.copy(exit);
      return result; 
    }
    public void setEntry(Flow.DataflowObject value) {
      entry.copy(value);
    }
    public void setExit(Flow.DataflowObject value) {
      exit.copy(value);
    }
    public Flow.DataflowObject getIn(Quad q) { 
      Flow.DataflowObject result = newTempVar();
      result.copy(in[q.getID()]);
      return result; 
    }
    public Flow.DataflowObject getOut(Quad q) { 
      Flow.DataflowObject result = newTempVar();
      result.copy(out[q.getID()]);
      return result;
    }
    public void setIn(Quad q, Flow.DataflowObject value) {
      in[q.getID()].copy(value);
    }
    public void setOut(Quad q, Flow.DataflowObject value) {
      out[q.getID()].copy(value);
    }
    /* This is the transfer function */
    public void processQuad(Quad q) {
      MyDataflowObject val = new MyDataflowObject ();
      val.copy(in[q.getID()]);
      for (RegisterOperand def : q.getDefinedRegisters()) {
        val.killVar(def.getRegister().toString());
      }
      for (RegisterOperand def : q.getDefinedRegisters()) {
        val.genVar(def.getRegister().toString(), q.getID());
      }
      out[q.getID()].copy(val);
    }

}
