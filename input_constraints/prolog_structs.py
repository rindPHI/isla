from typing import Union, Iterable


class Term:
    pass


class Atom(Term):
    def __init__(self, name: str):
        self.name = name

    def __eq__(self, other):
        return type(other) == type(self) and other.name == self.name

    def __repr__(self):
        return f"Atom({self.name})"

    def __str__(self):
        return self.name if " " not in self.name else f"'{self.name}'"


class Number(Term):
    def __init__(self, value: Union[float, int]):
        self.value = value

    def __eq__(self, other):
        return type(other) == type(self) and other.value == self.value

    def __repr__(self):
        return f"Number({self.value})"

    def __str__(self):
        return str(self.value)


class Variable(Term):
    def __init__(self, name: str):
        assert name[0] == "_" or name[0].isupper()
        self.name = name

    def __hash__(self):
        return hash((type(self), self.name))

    def __eq__(self, other):
        return type(other) == type(self) and other.name == self.name

    def __repr__(self):
        return f"Variable({self.name})"

    def __str__(self):
        return self.name if " " not in self.name else f"'{self.name}'"


class Functor:
    def __init__(self, name: str, arity: int, infix=False):
        self.name = name
        self.arity = arity
        self.infix = infix
        assert not infix or arity == 2

    def __eq__(self, other):
        return type(other) == type(self) and (other.name, other.arity) == (self.name, self.arity)

    def __repr__(self):
        return f"Functor({self.name}, {self.arity})"

    def __str__(self):
        return self.name


class CompoundTerm(Term):
    def __init__(self, functor: Functor, arguments: Iterable[Term]):
        self.functor = functor
        self.arguments = list(arguments)
        assert self.functor.arity == len(self.arguments)

    def __eq__(self, other):
        return type(other) == type(self) and (other.functor, other.arguments) == self.functor, self.arguments

    def __repr__(self):
        return f"{type(self).__name__}({repr(self.functor)}, [{', '.join(map(repr, self.arguments))}])"

    def __str__(self):
        if self.functor.infix:
            return (" " + str(self.functor) + " ").join(map(str, self.arguments))
        else:
            return f"{str(self.functor)}({', '.join(map(str, self.arguments))})"


class ListTerm(CompoundTerm):
    def __init__(self, arguments: Iterable[Term]):
        list_arguments = list(arguments)
        super().__init__(Functor("'[|]'", len(list_arguments) + 1), list_arguments + [Atom("[]")])

    def __str__(self):
        return "[" + ", ".join(map(str, self.arguments[:-1])) + "]"


class StringTerm(ListTerm):
    def __init__(self, arg: str):
        super().__init__(list(map(Number, map(ord, arg))))

    def __str__(self):
        number: Number
        return '"' + "".join([chr(number.value) for number in self.arguments[:-1]]) + '"'


class Predicate:
    def __init__(self, name: str, arity: int, infix=False):
        self.name = name
        self.arity = arity
        self.infix = infix
        assert not infix or arity == 2

    def __eq__(self, other):
        return type(other) == type(self) and (other.name, other.arity) == (self.name, self.arity)

    def __repr__(self):
        return f"Predicate({self.name}, {self.arity})"

    def __str__(self):
        return self.name


class Goal:
    pass


class PredicateApplication(Goal):
    def __init__(self, predicate: Predicate, arguments: Iterable[Term]):
        self.predicate = predicate
        self.arguments = list(arguments)
        assert self.predicate.arity == len(self.arguments)

    def __eq__(self, other):
        return type(other) == type(self) and (other.predicate, other.arguments) == self.predicate, self.arguments

    def __repr__(self):
        return f"{type(self).__name__}({repr(self.predicate)}, [{', '.join(map(repr, self.arguments))}])"

    def __str__(self):
        if self.predicate.infix:
            return (" " + str(self.predicate) + " ").join(map(str, self.arguments))
        else:
            return f"{str(self.predicate)}({', '.join(map(str, self.arguments))})"


class Conjunction(Goal):
    def __init__(self, arguments: Iterable[Goal]):
        self.arguments = list(arguments)

    def __eq__(self, other):
        return type(other) == type(self) and other.arguments == self.arguments

    def __repr__(self):
        return f"Conjunction([{', '.join(map(repr, self.arguments))}])"

    def __str__(self):
        return "(" + ", ".join(map(lambda s: f"({s})", map(str, self.arguments))) + ")"


class Disjunction(Goal):
    def __init__(self, arguments: Iterable[Goal]):
        self.arguments = list(arguments)

    def __eq__(self, other):
        return type(other) == type(self) and other.arguments == self.arguments

    def __repr__(self):
        return f"Disjunction([{', '.join(map(repr, self.arguments))}])"

    def __str__(self):
        return "(" + "; ".join(map(lambda s: f"({s})", map(str, self.arguments))) + ")"


class Conditional(Goal):
    def __init__(self, condition: Goal, then_branch: Goal, else_branch: Goal):
        self.condition = condition
        self.then_branch = then_branch
        self.else_branch = else_branch

    def __eq__(self, other):
        return type(other) == type(self) and ((other.condition, other.then_branch, other.else_branch) ==
                                              (self.condition, self.then_branch, self.else_branch))

    def __repr__(self):
        return f"Conditional([{repr(self.condition)}, {repr(self.then_branch)}, {repr(self.else_branch)}])"

    def __str__(self):
        return f"(({str(self.condition)}) -> ({str(self.then_branch)}) ; ({str(self.else_branch)}))"


class Rule:
    def __init__(self, head: PredicateApplication, goals: Iterable[Goal]):
        self.head = head
        self.goals = list(goals)

    def __eq__(self, other):
        return type(self) == type(other) and (other.head, other.goals) == (self.head, self.goals)

    def __repr__(self):
        return f"Rule({repr(self.head), [{', '.join(map(repr, self.goals))}]})"

    def __str__(self):
        # Full stops omitted since pyswip does not accept them
        if self.goals:
            # Rule
            return f"{str(self.head)} :- {', '.join(map(str, self.goals))}"
        else:
            # Fact
            return str(self.head)
