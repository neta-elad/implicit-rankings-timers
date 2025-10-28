from abc import ABC
from collections.abc import Callable, Mapping
from functools import cached_property
from typing import TYPE_CHECKING, Self, ClassVar, cast, get_type_hints, Any, Literal

import z3

__all__ = [
    "Expr",
    "Finite",
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
        ```python
        class Thread(Expr): ...
        ```
        Note the ellipsis (`...`) are not a placeholder ---
        this is the literal code for defining a type-level sort.

        To create a variable (equivalent to `z3.Const`) use:
        ```python
        t = Thread("t")
        ```
        """

        const_name: str
        mutable: bool

        _cache: ClassVar[dict[str, type["Expr"]]] = {}

        def __init__(
            self, name: str, mutable: bool = False, *, const: z3.ExprRef | None = None
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
            return self.__class__(self.const_name + "'", self.mutable)

        def unchanged(self) -> z3.BoolRef:
            if not self.mutable:
                return z3.BoolVal(True)
            return self.update(self)

        def update(self, val: Self) -> z3.BoolRef:
            assert self.mutable, f"Trying to update immutable constant {self}"
            return self.next == val

    class Bool(Expr):
        @classmethod
        def ref(cls) -> z3.SortRef:
            return z3.BoolSort()

        def neg(self) -> Self:
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
        @classmethod
        def ref(cls) -> z3.SortRef:
            return z3.IntSort()

        @classmethod
        def lt(cls) -> "Rel[Int, Int]":
            return WFRel[Int]("<", False, (z3.IntVal(0) < 0).decl())


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

    class Int(Expr, z3.Int):
        @classmethod
        def lt(cls) -> "Rel[Int, Int]": ...


class Finite(Expr, ABC):
    """
    A subclass of Expr for defining sorts that are
    *assumed by the user* to be finite.
    For example,
    ```python
    class Thread(Finite): ...
    ```
    declares the `Thread` sort as finite.
    """

    @classmethod
    def finite(cls) -> Literal[True]:
        return True


class Enum(Expr, ABC):
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
    name: str
    mutable: bool
    fun: z3.FuncDeclRef

    signature: ClassVar[Signature]
    _cache: ClassVar[dict[Signature, type]] = {}

    def __init__(
        self, name: str, mutable: bool = True, fun: z3.FuncDeclRef | None = None
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
        return self.__class__(self.name + "'", self.mutable)

    def __call__(self, *args: *Ts) -> T:
        return self.fun(*args)  # type: ignore

    def unchanged(self) -> z3.BoolRef:
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
        def update(old: Self, new: Self, *args: *Ts) -> z3.BoolRef:
            if_expr = old(*args)
            for place_args, new_value in places.items():
                if_expr = z3.If(_pairwise_equal(place_args, args), new_value, if_expr)
            return new(*args) == if_expr

        return self.update_with_lambda(update)


def _pairwise_equal[*Ts](args1: tuple[*Ts], args2: tuple[*Ts]) -> z3.BoolRef:
    return z3.And(*(parg == arg for parg, arg in zip(args1, args2)))  # type: ignore


class Rel[*Ts](Fun[*Ts, Bool]):
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
        return super().update(cast(Mapping[tuple[*Ts], Bool], places))

    def set_next(self, fun: Callable[[Self, *Ts], z3.BoolRef]) -> z3.BoolRef:
        return super().set_next(cast(Callable[[Self, *Ts], Bool], fun))


class WFRel[T: Expr](Rel[T, T]):
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


false = Bool("__false__", False, const=z3.BoolVal(False))
true = Bool("__true__", False, const=z3.BoolVal(True))
