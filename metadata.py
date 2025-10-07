import inspect
from collections.abc import Iterator
from typing import Any

_METADATA = "__irt_metadata__"


def add_marker[T](obj: T, marker: object) -> T:
    if not hasattr(obj, _METADATA):
        setattr(obj, _METADATA, set())

    markers: set[object] = getattr(obj, _METADATA)
    markers.add(marker)
    return obj


def get_methods(obj: object, marker: object) -> Iterator[tuple[str, Any]]:
    for name, member in inspect.getmembers(obj.__class__):
        if has_marker(member, marker):
            yield name, member


def has_marker(obj: object, marker: object) -> bool:
    return hasattr(obj, _METADATA) and marker in getattr(obj, _METADATA)
