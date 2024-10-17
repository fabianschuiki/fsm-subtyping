import z3
from copy import deepcopy
from termcolor import colored


def fresh(sort):
    return z3.FreshConst(sort)


def get_initial_state():
    return {
        "state": z3.IntVal(0),
        "tmp_a": fresh(z3.BitVecSort(8)),
        "tmp_b": fresh(z3.BitVecSort(8)),
        "tmp_c": fresh(z3.BitVecSort(8)),
    }


def get_inputs():
    return {
        "arg_valid": fresh(z3.BoolSort()),
        "arg_a": fresh(z3.BitVecSort(8)),
        "arg_b": fresh(z3.BitVecSort(8)),
        "res_ready": fresh(z3.BoolSort()),
    }


def advance(values):
    state = values["state"]
    next_state = state
    start = (state == 0) & values["arg_valid"]
    next_state = z3.If(start, 1, next_state)
    next_state = z3.If((state > 0), state + 1, next_state)
    next_state = z3.If((state == 4), state, next_state)
    next_state = z3.If((state == 4) & values["res_ready"], 0, next_state)

    tmp = values["tmp_c"]
    for i in range(4):
        j = 3 - i
        tmp = z3.If((state == i + 1), (values["tmp_a"] + values["tmp_b"]) >>
                    (j * 2), tmp)

    return {
        "state": next_state,
        "arg_ready": state == 0,
        "res_c": tmp,
        "res_valid": (state == 4),
        "tmp_a": z3.If(start, values["arg_a"], values["tmp_a"]),
        "tmp_b": z3.If(start, values["arg_b"], values["tmp_b"]),
        "tmp_c": tmp,
    }


def get_covers(values):
    return {
        "result_is_42":
        (values["res_c"] == 42) & values["res_valid"] & values["res_ready"],
        "inputs_are_20_22": (values["arg_a"] == 20) & (values["arg_b"] == 22),
        "unreachable": (values["res_c"] == 19) & (values["res_c"] == 18),
    }


# Dump a little waveform to the terminal.
def dump_trace(cycles, solver):
    model = solver.model()

    signal_names = {}
    for values in cycles:
        for name in values.keys():
            signal_names[name] = None
    signal_names = ["cycle"] + list(signal_names)
    signal_values = [""] * len(signal_names)

    dot = colored("┄", "cyan")

    for cycle, values in enumerate(cycles):
        formatted = []
        for name in signal_names:
            if name == "cycle":
                formatted.append(f"{cycle}")
                continue
            value = values.get(name)
            if value is not None:
                value = model.eval(value)
                if value == True:
                    formatted.append("1")
                    continue
                if value == False:
                    formatted.append("0")
                    continue
                if hasattr(value, "as_string"):
                    formatted.append(value.as_string())
                    continue
            formatted.append("·")

        max_length = max(map(lambda x: len(x), formatted)) + 2
        for i, text in enumerate(formatted):
            text += dot * (max_length - len(text))
            signal_values[i] += text

    max_length = max(map(lambda x: len(x), signal_names)) + 2
    for i, (name, values) in enumerate(zip(signal_names, signal_values)):
        name = name + dot * (max_length - len(name))
        print(f"  {name}|{dot}{dot}{values}")


# Check covers.
state = get_initial_state()
state_names = list(state.keys())

proven_covers = set()
cycles = []
solver = z3.Solver()
for i in range(10):
    current_values = state | get_inputs()
    next_values = advance(current_values)
    current_values |= {(k, v)
                       for k, v in next_values.items() if k not in state_names}
    # print(f"Cycle {len(cycles)}: {current_values}")
    cycles.append(current_values)

    # Cover reachable?
    for name, condition in get_covers(current_values).items():
        if name in proven_covers: continue
        solver.push()
        solver.add(condition)
        if solver.check() == z3.sat:
            print(colored(f"Cover `{name}` matched", "green"))
            tweaked_cycles = deepcopy(cycles)
            tweaked_cycles[-1][name] = condition
            dump_trace(tweaked_cycles, solver)
            proven_covers.add(name)
        solver.pop()

    state = current_values | next_values

for name in get_covers(current_values):
    if name not in proven_covers:
        print(colored(f"Cover `{name}` failed", "red"))

# n = advance(state)

# print(n)
