from abc import ABC
from collections.abc import Callable, Mapping
from functools import cached_property
from typing import TYPE_CHECKING, Self, ClassVar, cast, get_type_hints, Any, Literal

import z3

__all__ = [
    "Expr",
    "Bool",
    "false",
    "true",
    "Int",
    "Finite",
    "Enum",
    "Fun",
    "Rel",
    "WFRel",
]

if not TYPE_CHECKING:

    class Expr(z3.ExprRef, ABC):
        """
        A representation of a Z3 logical sort at the type-level.
        New type-safe sorts are defined by sub-classing this class
        (either directly or through the `Finite` class).

        This allows us to define a type-safe interface for Z3,
        so that well-sortedness of expressions can be *statically* checked
        by tools for checking Python type annotations
        (e.g., `mypy`).

        An instance of the class represents a (transition-system) constant
        of this sort.

        For example, we can declare a `Ticket` sort by writing:
        >>> class Ticket(Expr): ...

        Note the ellipsis (`...`) are not a placeholder ---
        this is the literal code for defining a type-level sort.

        To create a variable (equivalent to `z3.Const`) use:
        >>> t = Ticket("t")
        t

        To create a mutable constant use:
        >>> t = Ticket("t", mutable=True)
        t

        Note though that this is never needed
        when creating user-defined transition systems
        with `ts.TransitionSystem`.
        """

        const_name: str
        mutable: bool

        _cache: ClassVar[dict[str, type["Expr"]]] = {}

        def __init__(
            self, name: str, *, mutable: bool = False, const: z3.ExprRef | None = None
        ) -> None:
            if const is None:
                const = z3.Const(name, self.__class__.ref())
            super(Expr, self).__init__(const.ast, const.ctx)
            self.const_name = name
            self.mutable = mutable

        @classmethod
        def __init_subclass__(cls, **kwargs) -> None:
            super().__init_subclass__(**kwargs)
            cls._cache[cls.__name__] = cls

        @classmethod
        def ref(cls) -> z3.SortRef:
            return z3.DeclareSort(cls.__name__)

        @classmethod
        def declare(cls, name: str) -> "Sort":
            if name not in cls._cache:
                cls._cache[name] = type(name, (Expr,), {})
            return cls._cache[name]

        @classmethod
        def finite(cls) -> bool:
            return False

        @cached_property
        def fun(self) -> "Fun[Self]":
            return Fun[self.__class__](self.const_name, self.mutable)

        @cached_property
        def fun_ref(self) -> z3.FuncDeclRef:
            return self.decl()

        @cached_property
        def next(self) -> Self:
            """
            Returns post-state copy of a constant.
            The constant must be mutable.

            >>> Ticket("service", mutable=True).next
            service'
            """
            assert (
                self.mutable
            ), f"No next (post-state) version of immutable symbol {self.const_name}"
            return self.__class__(self.const_name + "'", mutable=self.mutable)

        def unchanged(self) -> z3.BoolRef:
            """
            Produces a formula expressing
            that a mutable constant is unchanged during a transition.

            For example, given mutable
            >>> service = Ticket("service", mutable=True)

            the code
            >>> service.unchanged()
            service' == service

            produces the same formula as
            >>> service.next == service
            service' == service
            """
            if not self.mutable:
                return z3.BoolVal(True)
            return self.update(self)

        def update(self, val: Self) -> z3.BoolRef:
            """
            Produces a formula expressing
            that a mutable constant is equal to `val` in the post-state.

            For example, given
            >>> service: Ticket
            >>> next_service: Ticket

            the code
            >>> service.update(next_service)
            service' == next_service

            produces the same formula as
            >>> service.next == next_service
            service' == next_service
            """
            assert self.mutable, f"Trying to update immutable constant {self}"
            return self.next == val

    class Bool(Expr):
        """
        Type-level Bool sort, for transition-system symbols
        that operate with Booleans.
        Known to be finite.
        """

        @classmethod
        def ref(cls) -> z3.SortRef:
            return z3.BoolSort()

        def neg(self) -> Self:
            """Type-safe version of `z3.Not` for type-level Bools."""
            if self is false:
                return true
            elif self is true:
                return false
            else:
                return cast(Self, z3.Not(self))

        @classmethod
        def finite(cls) -> Literal[True]:
            return True

    class Int(Expr):
        """
        Type-level Int sort, for transition-system symbols
        that operate with integers.
        """

        @classmethod
        def ref(cls) -> z3.SortRef:
            return z3.IntSort()


if TYPE_CHECKING:

    class Expr(z3.Const, ABC):
        const_name: str

        def __init__(
            self, name: str, mutable: bool = True, *, const: z3.ExprRef | None = None
        ) -> None: ...

        @classmethod
        def ref(cls) -> z3.SortRef: ...

        @classmethod
        def const(cls, name: str) -> Self: ...

        @classmethod
        def consts(cls, names: str) -> list[Self]: ...

        @classmethod
        def declare(cls, name: str) -> "Sort": ...

        @classmethod
        def finite(cls) -> bool: ...

        @property
        def next(self) -> Self: ...

        @property
        def fun(self) -> "Fun[Self]": ...

        @property
        def fun_ref(self) -> z3.FuncDeclRef: ...

        def unchanged(self) -> z3.BoolRef: ...

        def update(self, val: Self) -> z3.BoolRef: ...

    class Bool(Expr, z3.Bool):
        def neg(self) -> Self: ...

    class Int(Expr, z3.Int): ...


class Finite(Expr, ABC):
    """
    A subclass of `Expr` for defining sorts that are
    *assumed by the user* to be finite.

    For example,
    >>> class Process(Finite): ...

    declares the `Process` sort as finite.
    """

    @classmethod
    def finite(cls) -> Literal[True]:
        return True


class Enum(Expr, ABC):
    """
    A subclass of `Expr` for defining enumerated sorts.
    A type-level equivalent of `z3.EnumSort`.

    For example, we can represent the state of
    a Process in a system with a `State` sort:
    >>> class State(Enum):
    ...     waiting: "State"
    ...     critical: "State"
    ...     neutral: "State"

    Each field annotated with the class's type
    is one variant of the EnumSort,
    and can be accessed directly as a class field.

    For example, assuming `server_state` is mutable constant
    of sort `State`
    >>> server_state = State("server_state", mutable=True)
    server_state

    we can update it to the `waiting` state:
    >>> server_state.update(State.waiting)
    server_state == waiting

    All sorts defined by subclasses of `Enum` are known to be finite.
    """

    enum_sort: ClassVar[z3.SortRef]
    enum_values: tuple[Self, ...]

    @classmethod
    def finite(cls) -> bool:
        return True

    @classmethod
    def __init_subclass__(cls, **kwargs: Any) -> None:
        super().__init_subclass__(**kwargs)
        names = []
        for field, hint in get_type_hints(cls, localns={cls.__name__: cls}).items():
            if hint is cls:
                names.append(field)

        sort, values = z3.EnumSort(cls.__name__, names)
        cls.enum_sort = sort

        enum_values: list[Self] = []
        for name, value in zip(names, values):
            enum_value: Self = cls(name, False, const=value)  # type: ignore
            setattr(cls, name, enum_value)
            enum_values.append(enum_value)

        cls.enum_values = tuple(enum_values)

    @classmethod
    def ref(cls) -> z3.SortRef:
        return cls.enum_sort


type Sort = type[Expr]
type Signature = tuple[Sort, ...]


class Fun[*Ts, T: z3.ExprRef]:
    """
    A type-level representation of a z3.Function signature.
    It maintains well-sortedness,
    allowing to be called only with arguments of the correct sort,
    and producing a result of the correct sort.

    `Fun` **should not be instantiated directly**.
    Instead, it should only be used as annotations inside
    transition systems (see `ts.TransitionSystem`).

    For example, a `has_ticket` function of type
    `Fun[Process, Ticket, Bool]`
    >>> has_ticket: Fun[Process, Ticket, Bool]

    can be called like so
    >>> result = has_ticket(p, t)

    and will be type-checked,
    ensuring that `p` is of type `Process`,
    `t` is of type `Ticket`,
    and `result` is of type `Bool`.
    """

    name: str
    mutable: bool
    fun: z3.FuncDeclRef

    signature: ClassVar[Signature]
    _cache: ClassVar[dict[Signature, type]] = {}

    def __init__(
        self, name: str, *, mutable: bool = True, fun: z3.FuncDeclRef | None = None
    ) -> None:
        self.name = name
        self.mutable = mutable
        if fun is None:
            fun = z3.Function(name, *(sort.ref() for sort in self.signature))
        self.fun = fun

    @classmethod
    def __class_getitem__(cls, item: Sort | Signature) -> "type[Fun[*Ts, T]]":
        if not isinstance(item, tuple):
            item = (item,)
        return cls.declare(item)

    @classmethod
    def declare(cls, signature: Signature) -> type:
        if signature not in cls._cache:
            cls._cache[signature] = type(
                cls._subclass_name(signature), (cls,), {"signature": signature}
            )

        return cls._cache[signature]

    @classmethod
    def _subclass_name(cls, signature: Signature) -> str:
        return f"Fun[{", ".join(str(sort) for sort in signature)}]"

    @cached_property
    def next(self) -> Self:
        if not self.mutable:
            return self
        return self.__class__(self.name + "'", mutable=self.mutable)

    def __call__(self, *args: *Ts) -> T:
        return self.fun(*args)  # type: ignore

    def unchanged(self) -> z3.BoolRef:
        """
        Produces a universal formula expressing that for all inputs,
        the output of the function remains unchanged between the pre-state
        and the post-state.

        For example, given the `has_ticket: Fun[Process, Ticket, Bool]` object:
        >>> has_ticket.unchanged()
        ForAll([Process1, Ticket2],
                has_ticket'(Process1, Ticket2) == has_ticket(Process1, Ticket2))
        """
        return self.update_with_lambda(lambda old, new, *args: old(*args) == new(*args))

    def update_with_lambda(
        self, fun: Callable[[Self, Self, *Ts], z3.BoolRef]
    ) -> z3.BoolRef:
        consts = tuple(sort(f"X{i}") for i, sort in enumerate(self.signature[0:-1]))
        args = cast(tuple[*Ts], consts)
        return z3.ForAll(consts, fun(self, self.next, *args))

    def forall(self, fun: Callable[[*Ts], z3.BoolRef]) -> z3.BoolRef:
        return self.update_with_lambda(lambda _old, _new, *args: fun(*args))

    def set_next(self, fun: Callable[[Self, *Ts], T]) -> z3.BoolRef:
        return self.update_with_lambda(
            lambda old, new, *args: new(*args) == fun(old, *args)
        )

    def update(self, places: Mapping[tuple[*Ts], T]) -> z3.BoolRef:
        """
        Produces a universal formula expressing that for all inputs,
        the output of the function remains unchanged between the pre-state
        and the post-state,
        except for inputs equal to keys of `places`,
        where the post-state function returns the matching value in `places`.

        For example,
        >>> has_ticket.update({(p1, t1): true, (p2, t2): false})
        ForAll([Process1, Ticket2],
                has_ticket'(Process1, Ticket2) ==
                If(And(Process1 == p1, Ticket2 == t1), true,
                    If(And(Process1 == p2, Ticket2 == t2), false,
                        has_ticket(Process1, Ticket2))))
        """

        def update(old: Self, new: Self, *args: *Ts) -> z3.BoolRef:
            if_expr = old(*args)
            for place_args, new_value in places.items():
                if_expr = z3.If(_pairwise_equal(place_args, args), new_value, if_expr)
            return new(*args) == if_expr

        return self.update_with_lambda(update)


def _pairwise_equal[*Ts](args1: tuple[*Ts], args2: tuple[*Ts]) -> z3.BoolRef:
    return z3.And(*(parg == arg for parg, arg in zip(args1, args2)))  # type: ignore


class Rel[*Ts](Fun[*Ts, Bool]):
    """
    A type-level representation of relations, function that return Booleans.
    """

    @classmethod
    def __class_getitem__(cls, item: Sort | Signature) -> "type[Rel[*Ts]]":
        if not isinstance(item, tuple):
            item = (item,)

        return super().__class_getitem__(item + (Bool,))  # type: ignore

    @classmethod
    def _subclass_name(cls, signature: Signature) -> str:
        return f"Rel[{", ".join(str(sort) for sort in signature[0:-1])}]"

    def well_founded(self) -> bool:
        return False

    def update(self, places: Mapping[tuple[*Ts], z3.BoolRef]) -> z3.BoolRef:
        """
        Overrides `Fun.update` to allow arbitrary `z3` formulas
        (`z3.BoolRef`) in updated values.
        """
        return super().update(cast(Mapping[tuple[*Ts], Bool], places))

    def set_next(self, fun: Callable[[Self, *Ts], z3.BoolRef]) -> z3.BoolRef:
        return super().set_next(cast(Callable[[Self, *Ts], Bool], fun))


class WFRel[T: Expr](Rel[T, T]):
    """
    A binary relation, *assumed by the user* to be well-founded.
    """

    @classmethod
    def __class_getitem__(cls, item: Sort | Signature) -> "type[Rel[T, T]]":
        if not isinstance(item, tuple):
            item = (item,)

        return super().__class_getitem__(item + item)

    @classmethod
    def _subclass_name(cls, signature: Signature) -> str:
        return f"WFRel[{", ".join(str(sort) for sort in signature[0:-1])}]"

    def well_founded(self) -> bool:
        return True


false: Bool = Bool("__false__", const=z3.BoolVal(False))
"""Type-safe equivalent and shorthand for `z3.BoolVal(False)`."""

true: Bool = Bool("__true__", const=z3.BoolVal(True))
"""Type-safe equivalent and shorthand for `z3.BoolVal(True)`"""
