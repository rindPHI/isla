import pickle

from isla.solver import ISLaSolver

with (open("/tmp/saved_debug_state", "rb")) as debug_state_file:
    try:
        solver: ISLaSolver = pickle.load(debug_state_file)
        while True:
            try:
                result = solver.solve()
                print(f"Found solution: {result}")
            except StopIteration:
                pass
    except EOFError as e:
        print(e)
