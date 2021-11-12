from typing import Tuple, Optional, List, Dict

ParseTree = Tuple[str, Optional[List['ParseTree']]]
Path = Tuple[int, ...]
Grammar = Dict[str, List[str]]
ImmutableGrammar = Tuple[Tuple[str, Tuple[str, ...]]]
CanonicalGrammar = Dict[str, List[List[str]]]
