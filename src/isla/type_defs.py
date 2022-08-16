from typing import Tuple, Optional, List, Dict, TypeVar, TypeAlias

S = TypeVar('S')
T = TypeVar('T')

ParseTree = Tuple[str, Optional[List['ParseTree']]]
Path = Tuple[int, ...]
Grammar = Dict[str, List[str]]
ImmutableGrammar = Tuple[Tuple[str, Tuple[str, ...]], ...]
CanonicalGrammar = Dict[str, List[List[str]]]
ImmutableList: TypeAlias = Tuple[T, ...]
Pair: TypeAlias = Tuple[S, T]
