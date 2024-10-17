import z3


class When:
    conditions = []

    def __init__(self, condition):
        self.condition = condition

    def __enter__(self):
        When.conditions.append(self.condition)

    def __exit__(self, type, value, traceback):
        When.conditions.pop()


STATES_CURRENT = dict()
STATES_NEXT = dict()


class State:

    def __init__(self, name, sort):
        self.name = name
        self.sort = sort
        x = z3.FreshConst(sort)
        STATES_CURRENT[name] = x
        STATES_NEXT[name] = x

    def get(self):
        return STATES_NEXT[self.name]

    def assign(self, value):
        if len(When.conditions) > 0:
            c = When.conditions[0]
            for c2 in When.conditions[1:]:
                c &= c2
            STATES_NEXT[self.name] = z3.If(c, value, STATES_NEXT[self.name])
        else:
            STATES_NEXT[self.name] = value


class Transaction:

    def __init__(self, name, result_sorts, operand_sorts):
        self.name = name
        self.result_sorts = result_sorts
        self.operand_sorts = operand_sorts

    def receive(self):
        return [z3.FreshConst(s) for s in self.operand_sorts]

    def send(self, *args):
        pass

    def try_send(self, *args):
        return z3.FreshConst(z3.BoolSort())


# class Transaction:
#     # - operand types
#     # - result types
#     pass


class Machine:
    # - input transactions
    # - output transactions

    def __init__(self):
        self.input_txs = []
        self.output_txs = []

    def body(self):
        arg = Transaction("arg", [], [z3.BitVecSort(8), z3.BitVecSort(8)])
        res = Transaction("res", [z3.BitVecSort(8)], [])
        state = State("state", z3.BoolSort())
        result = State("result", z3.BitVecSort(8))
        with When(state.get() == False):
            a, b = arg.receive()
            done = res.try_send(a + b)
            with When(done == False):
                state.assign(True)
                result.assign(a + b)
        with When(state.get() == True):
            res.send(result)
            state.assign(False)


# Check implementation.
Machine().body()
print(STATES_CURRENT)
print(STATES_NEXT)
