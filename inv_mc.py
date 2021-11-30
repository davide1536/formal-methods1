import pynusmv
import sys
from pynusmv.dd import StateInputs
import copy
from tabulate import tabulate
import os

from pynusmv.prop import false, not_
from pynusmv_lower_interface.nusmv.enc.bdd.bdd import pick_one_state
from pynusmv_lower_interface.nusmv.node.node import is_list_empty, llength

directory = "test/"

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

    for i in range(1,len(newSet)):

        state = fsm.pick_one_state(newSet[i].intersection(pathSet))
        stateInput = fsm.get_inputs_between_states(state, next_state)
       
        path = path + (fsm.pick_one_inputs(stateInput).get_str_values(),)
        path = path + (state.get_str_values() ,)

        path_obj.append(stateInput)
        path_obj.append(state)

        preSetBdd = fsm.weak_pre(state)
        next_state = state

        pathSet = preSetBdd
    
    path_obj.reverse()
    return reverse_tuple(path), path_obj


""" This function verifies the correctness of the path computed by the get_path function """
def verify_correctness(trace_obj, fsm, notBddSpec):
    #check if the initial state belongs to the set of initial states
    if not trace_obj[0].intersected(fsm.init):
        return False
    
    #check if the last state violates the invariant
    if not trace_obj[len(trace_obj)-1].intersected(notBddSpec):
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


def check_explain_inv_spec(spec, fsm, notBddSpec):
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
    ltlspec = pynusmv.prop.g(spec)
    real_res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)

    
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
            return res,real_res, trace, trace_obj
            # return res, trace
        new = fsm.post(new).diff(reach)
        setOfnew.append(new)


        reach = reach.union(new)


    res = True
    trace = None

   

    return res,real_res, trace, trace_obj


#results shown as a table
def tot_results(file_names, tot_res, tot_real_res, tot_trace_correctness):

    tot_matching = [tot_res[i] == tot_real_res[i] for i in range(len(tot_res))]

    table = []
    table.append(file_names)                 #table[0]
    table.append(tot_res)                    #table[1]
    table.append(tot_real_res)               #table[2]
    table.append(tot_matching)               #table[3]
    table.append(tot_trace_correctness)      #table[4]

    res_table = []
    for i in range(len(file_names)):
        res_table.append([table[0][i], table[1][i], table[2][i], table[3][i], table[4][i]])
    
    print()
    print(tabulate(res_table, headers= ["filename_invariant", "our_results", "instructor_results", "matching", "trace correctness"], tablefmt='pretty'))


#function that automate execution
def execute_all():

    tot_res = []
    tot_trace_correctness = []
    tot_matching = []
    tot_real_res = []
    file_names = []
    
    for filename in os.listdir(directory):
        print()
        print("-"*15 + " I'm running the file: ", filename, "-"*15)
        print()
        # if len(sys.argv) != 2:
        #     print("Usage:", sys.argv[0], "filename.smv")
        #     sys.exit(1)
    
        file_name = filename
    
        #filename = sys.argv[1]
        #filename = "test/gigamax.smv"
        pynusmv.init.init_nusmv()
        pynusmv.glob.load_from_file("test/"+filename)
        pynusmv.glob.compute_model()
        invtype = pynusmv.prop.propTypes['Invariant']

        i = 1

        fsm = pynusmv.glob.prop_database().master.bddFsm

        for prop in pynusmv.glob.prop_database():
            if prop.type == invtype:
                file_name_temp = file_name + "_inv_" + str(i)
                file_names.append(file_name_temp)
                spec = prop.expr

                print("Property", spec, "is an INVARSPEC.")
                notBddSpec = spec_to_bdd(fsm,pynusmv.prop.not_(spec))
                res,real_res, trace, trace_obj = check_explain_inv_spec(spec, fsm, notBddSpec)
                tot_res.append(res)
                tot_real_res.append(real_res)
                if res == True:
                    print("Invariant is respected")
                    print()
                    tot_trace_correctness.append(None)
                else:
                    print("Invariant is not respected")
                    print("trace ",trace)
                    correct = verify_correctness(trace_obj, fsm, notBddSpec)
                    tot_trace_correctness.append(correct)
                    if correct:
                        print( "-"*4 + " Trace is correct " + "-"*4)
                    else:
                        print("-"*4 +" Trace is not correct "+ "-"*4)
                    
                    
                i = i+1
            else:
                print("Property", spec, "is not an INVARSPEC, skipped.")

        print()
        pynusmv.init.deinit_nusmv()
    tot_results(file_names, tot_res, tot_real_res, tot_trace_correctness)

execute_all()

    
