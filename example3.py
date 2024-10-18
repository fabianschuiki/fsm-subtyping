import z3

bv8 = z3.BitVecSort(8)


class State:

    def __init__(self, name, sort):
        self.name = name
        self.now = z3.FreshConst(sort, name)
        self.next = self.now


class Transaction:

    def __init__(self, name, result_sorts, argument_sorts):
        self.name = name
        self.results = [
            z3.FreshConst(s, f"{name}_res{i}")
            for i, s in enumerate(result_sorts)
        ]
        self.arguments = [
            z3.FreshConst(s, f"{name}_arg{i}")
            for i, s in enumerate(argument_sorts)
        ]
        self.fire = z3.FreshConst(z3.BoolSort(), f"{name}_fire")


class Machine:

    def __init__(self, name):
        self.name = name
        self.states = []
        self.transactions = []


def machine_a(solver: z3.Solver):
    work = Transaction("A_work", [bv8], [bv8, bv8])
    solver.add(work.fire)
    solver.add(work.results[0] == work.arguments[0] + work.arguments[1])
    m = Machine("A")
    m.transactions += [work]
    m.work = work
    return m


def machine_b(solver: z3.Solver):
    state = State("B_state", z3.BoolSort())
    tmp = State("B_tmp", bv8)
    arg = Transaction("B_arg", [], [bv8, bv8])
    res = Transaction("B_res", [bv8], [])

    solver.add(~state.now == arg.fire)
    c = arg.arguments[0] + arg.arguments[1]
    state.next = z3.If(~state.now & ~res.fire, True, False)
    tmp.next = z3.If(~state.now, c, tmp.now)
    solver.add(res.fire == z3.If(~state.now, arg.fire, True))
    solver.add(res.results[0] == tmp.next)

    m = Machine("B")
    m.states += [state, tmp]
    m.transactions += [arg, res]
    m.arg = arg
    m.res = res
    return m


def machine_b_impl_a(solver: z3.Solver, b, a):
    seen_a = State("BimplA_seen_a", bv8)
    seen_b = State("BimplA_seen_b", bv8)
    seen_a.next = z3.If(b.arg.fire, b.arg.arguments[0], seen_a.next)
    seen_b.next = z3.If(b.arg.fire, b.arg.arguments[1], seen_b.next)

    checks = [
        (a.work.fire == b.res.fire),
        (z3.Implies(a.work.fire, a.work.arguments[0] == seen_a.next)),
        (z3.Implies(a.work.fire, a.work.arguments[1] == seen_b.next)),
        (z3.Implies(a.work.fire, a.work.results[0] == b.res.results[0])),
    ]

    m = Machine("BimplA")
    m.states += [seen_a, seen_b]
    return m, checks


solver = z3.Solver()
a = machine_a(solver)
b = machine_b(solver)
print(solver)
print(solver.check())

solver.push()
b_impl_a, checks = machine_b_impl_a(solver, b, a)
for check in checks:
    print(f"check {check}")
    solver.push()
    solver.add(~check)
    if solver.check() == z3.sat:
        print("failed")
        print(solver.model())
    solver.pop()
solver.pop()
