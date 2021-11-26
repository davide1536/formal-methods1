import pynusmv
import sys
from pynusmv.dd import StateInputs
import copy

from pynusmv.prop import false, not_
from pynusmv_lower_interface.nusmv.enc.bdd.bdd import pick_one_state
from pynusmv_lower_interface.nusmv.node.node import is_list_empty, llength

def reverse_tuple(tuples):
    new_tuple = tuples[::-1]
    return new_tuple


def get_path(errorState, newSet ,fsm):
    '''
    This function computes the path of reacheable state from the error state to the initial state.
    At iteration i, given a state that belongs to the path to reach the error state, the algorithm computes
    its pre image, it intersecates this set with the set given by the states discovered at iteration len(newSet) - i
    where len(newSet) is the number of sets "new" in symbolic bfs algorithm. Thanks to this intersecation in retrieves the next state and repeat the process.
    This procedure is reapeted for each "new" set. 
    For more detail watch the report.  
    '''
    path = ()
    path_obj = []
    state = fsm.pick_one_state(newSet[0].intersection(errorState))

    path = (state.get_str_values() ,)
    path_obj.append(state)

    preSetBdd = fsm.weak_pre(state)
    next_state = state
    pathSet = preSetBdd
    print("lo stato è: ", state.get_str_values())       # 1 --- 2 --- 3 --- X  fsm.init()

    for i in range(1,len(newSet)):

        state = fsm.pick_one_state(newSet[i].intersection(pathSet))
        stateInput = fsm.get_inputs_between_states(state, next_state)
       
        path = path + (fsm.pick_one_inputs(stateInput).get_str_values(),)
        path = path + (state.get_str_values() ,)

        path_obj.append(stateInput)
        path_obj.append(state)


        print("con input: ", fsm.pick_one_inputs(stateInput).get_str_values())
        print("lo stato è: ", state.get_str_values())

        preSetBdd = fsm.weak_pre(state)
        next_state = state

        pathSet = preSetBdd
    
    path_obj.reverse()
    return reverse_tuple(path), path_obj


""" This function verifies the correctness of the path computed by the get_path function """
def verify_correctness(trace_obj, fsm):
    if not trace_obj[0].intersected(fsm.init):
        return False
    
    for i in range(0, len(trace_obj) - 2 , 2):
        next_state = trace_obj[i+2]
        post_set = fsm.post(trace_obj[i], trace_obj[i+1])
        if not next_state.intersected(post_set):
            return False
    
    return True


def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec


def check_explain_inv_spec(spec, fsm):
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ennding with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    
    
    notBddSpec = spec_to_bdd(fsm,pynusmv.prop.not_(spec))

    #start symbolic bfs
    setOfnew = []
    trace_obj = []
    reach = fsm.init
    new = fsm.init
    setOfnew.append(new)
    # for state in fsm.pick_all_states(fsm.init):
    #     print("stati iniziali: ", state.get_str_values())
    while not(new.is_false()):
        if (new.intersected(notBddSpec)):
            setOfnew.reverse()
            trace, trace_obj = get_path(notBddSpec, setOfnew, fsm)
            res = False
            return res, trace, trace_obj
            # return res, trace
        new = fsm.post(new).diff(reach)
        setOfnew.append(new)


        reach = reach.union(new)


    res = True
    trace = None

    # ltlspec = pynusmv.prop.g(spec)
    # res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)


    return res, trace, trace_obj

if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
#filename = "test/gigamax.smv"
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']

i = 0


fsm = pynusmv.glob.prop_database().master.bddFsm

for prop in pynusmv.glob.prop_database():
   
    spec = prop.expr
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
        res, trace, trace_obj = check_explain_inv_spec(spec, fsm)
        if res == True:
            print("Invariant is respected")
        else:
            print("Invariant is not respected")
            print("trace ",trace)
            correct = verify_correctness(trace_obj, fsm)
            if correct:
                print("********** trace is correct **********")
            else:
                print("********** trace is not correct **********")
            

    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")


pynusmv.init.deinit_nusmv()

    
