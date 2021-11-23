import pynusmv
import sys
from pynusmv.dd import StateInputs
import copy

from pynusmv.prop import false, not_
from pynusmv_lower_interface.nusmv.enc.bdd.bdd import pick_one_state
from pynusmv_lower_interface.nusmv.node.node import is_list_empty, llength

def get_path(pathSet, newSet ,fsm):
    i = 1
    old_state = None
    for i in range(len(newSet)):
        print("iterazione ", i)
        state = fsm.pick_one_state(newSet[i].intersection(pathSet))
        if i > 0:
            stateInput = fsm.get_inputs_between_states(state, old_state)
            #print("possibile input: ",stateInput)
            #stateInput = get_inputs_between_states(current, state)[0]
        else:
            stateInput = fsm.pick_one_inputs(state)
        if i > 0:
            print("input: ", fsm.pick_one_inputs(stateInput).get_str_values())
        print("lo stato è: ", state.get_str_values())
        #print("con input: ", stateInput.get_str_values())
        preSetBdd = fsm.weak_pre(state)
        old_state = state

        # for state in fsm.pick_all_states(preSetBdd):
        #     print("set con cui è possible raggiungere quello stato è: ", state.get_str_values())

        pathSet = preSetBdd

    # for state in fsm.pick_all_states(errorBdd):
    #     print("stato di errore: ", state.get_str_values())
    # #calcolo la pre immagine debole del set di stati di errore
    # preSetBdd = fsm.weak_pre(errorBdd)

    # for state in fsm.pick_all_states(preSetBdd):
    #     print("set con cui è possible raggiungere quello di errore: ", state.get_str_values())
    # print("con input: ", fsm.pick_all_inputs(preSetBdd))
    # preStateBdd = newSet.intersection(preSetBdd)
    # print(preStateBdd)
    # for state in fsm.pick_all_states(preStateBdd):
    #     print("stato precedente a quello di errore: ", state.get_str_values())

def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def check_explain_inv_spec(spec):
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
    fsm = pynusmv.glob.prop_database().master.bddFsm
    # for state in fsm.pick_all_states(fsm.pick_all_states_inputs(fsm.init)):
    #     print("stati di input per quest bdd: ", state.get_str_values())
    #trasformo la specifica "spec" in bdd
    bddspec = spec_to_bdd(fsm, spec)
    
    #calcolo la negazione del bdd corrispndende a alla specifica "spec"
    notBddSpec = spec_to_bdd(fsm,pynusmv.prop.not_(spec))
    # print("specifica negata:",notBddSpec )

    #un po' di print per capire 
    # for state in fsm.pick_all_states(fsm.init):
    #    print("stati iniziali ", state.get_str_values())

    #for state in fsm.pick_all_states(fsm.post(fsm.init)):
    #    print("post normale ", state.get_str_values())
    #
    #from pynusmv.fsm import BddTrans
    #trans = BddTrans.from_string(fsm.bddEnc.symbTable,"next(x) = 10")
    #for state in fsm.pick_all_states(trans.post(fsm.init)):
        #print("post trans ", state.get_str_values())
    
    #inizio bfs symbolic
    setOfnew = []
    reach = fsm.init
    new = fsm.init
    setOfnew.append(new)

    for state in fsm.pick_all_states(fsm.init):
        print("stati iniziali: ", state.get_str_values())
    res = True
    while not(new.is_false()):
        if (new.intersected(notBddSpec)):
            setOfnew.reverse()
            get_path(notBddSpec, setOfnew, fsm)
            res = False
            trace = None
            break
            # return res, trace
        new = fsm.post(new).diff(reach)
        setOfnew.append(new)

        # for state in fsm.pick_all_states(new):
        #     print("stati new: ", state.get_str_values())

        reach = reach.union(new)

        # for state in fsm.pick_all_states(reach):
        #     print("stati reach: ", state.get_str_values())

    res = True
    trace = None

    #queste 2 righe penso che ce le abbia messe il prof visto che la funzione
    #"check_explain_ltl_spec(ltlspec)" fa esattamento quello che richiede l'esercizio
    ltlspec = pynusmv.prop.g(spec)
    res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)


    return res, trace

if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
#filename = "test/gigamax.smv"
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']

#print(fsm.pick_one_state(fsm.init).get_str_values())
#for state in fsm.pick_all_states(fsm.post(fsm.init)):
    #print("state", state.get_str_values())
#il ciclo serve per controllare ogni proprietà
i = 0
for prop in pynusmv.glob.prop_database():
   
    spec = prop.expr
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
        res, trace = check_explain_inv_spec(spec)
        if res == True:
            print("Invariant is respected")
        else:
            print("Invariant is not respected")
            print("trace giusta ",trace)
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")
   
pynusmv.init.deinit_nusmv()
