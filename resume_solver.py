import pickle

from isla.solver import ISLaSolver

with (open("/tmp/saved_debug_state", "rb")) as debug_state_file:
    try:
        solver: ISLaSolver = pickle.load(debug_state_file)
        it = solver.solve()
        while True:
            try:
                result = next(it)
                print(f"Found solution: {result}")
            except StopIteration:
                pass
    except EOFError as e:
        print(e)
