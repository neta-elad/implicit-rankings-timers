from abc import ABC
from collections.abc import Callable
from functools import cached_property
from typing import TYPE_CHECKING, Self, ClassVar, cast, get_type_hints, Any

import z3

if not TYPE_CHECKING:

    class Expr(z3.ExprRef, ABC):
        const_name: str
        mutable: bool

        _cache: ClassVar[dict[str, type["Expr"]]] = {}

        def __init__(
            self, name: str, mutable: bool = True, *, const: "z3.Const | None" = None
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
        def const(cls, name: str) -> Self:
            return z3.Const(name, cls.ref())

        @classmethod
        def consts(cls, names: str) -> tuple[Self, ...]:
            return z3.Consts(names, cls.ref())

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

        def unchanged(self) -> z3.BoolRef:
            if not self.mutable:
                return z3.BoolVal(True)
            return self == self.__class__(self.const_name + "'", self.mutable)

    class Bool(Expr):
        @classmethod
        def ref(cls) -> z3.SortRef:
            return z3.BoolSort()

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

        def __init__(self, name: str) -> None: ...

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

    class Bool(z3.Bool, Expr): ...

    class Int(z3.Int, Expr):
        @classmethod
        def lt(cls) -> "Rel[Int, Int]": ...


class Finite(Expr, ABC):
    @classmethod
    def finite(cls) -> bool:
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

    # origin = get_origin(hint) or hint
    # mutable = True
    # if origin is Immutable:
    #     mutable = False
    #     origin = get_args(hint)[0]
    #
    # name = field
    # if mutable:
    #     name += self.suffix
    #
    # if issubclass(origin, Expr):
    #     symbol = origin(name, mutable)
    #     symbols[field] = symbol.fun_ref
    # elif issubclass(origin, Fun):
    #     symbol = origin(name, mutable)
    #     symbols[field] = symbol.fun
    # else:
    #     continue
    # object.__setattr__(self, field, symbol)

    @classmethod
    def ref(cls) -> z3.SortRef:
        return cls.enum_sort


type Sort = type[Expr]
type Signature = tuple[Sort, ...]


class Fun[*Ts, T: Expr]:
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

    def __call__(self, *args: *Ts) -> T:
        return self.fun(*args)  # type: ignore

    def unchanged(self) -> z3.BoolRef:
        return self.update(lambda old, new, *args: old(*args) == new(*args))

    def update(self, fun: Callable[[Self, Self, *Ts], z3.BoolRef]) -> z3.BoolRef:
        consts = tuple(sort(f"X{i}") for i, sort in enumerate(self.signature[0:-1]))
        args = cast(tuple[*Ts], consts)
        self_next = self.__class__(self.name + "'", self.mutable)
        return z3.ForAll(consts, fun(self, self_next, *args))


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


class WFRel[T: Expr](Rel[T, T]):
    def well_founded(self) -> bool:
        return True
