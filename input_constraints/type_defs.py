from typing import Tuple, Optional, List, Dict, Union

ParseTree = Tuple[str, Optional[List['ParseTree']]]
AbstractTree = Tuple[Union[str, 'isla.Constant'], Optional[List['AbstractTree']]]
Path = Tuple[int, ...]
Grammar = Dict[str, List[str]]
CanonicalGrammar = Dict[str, List[List[str]]]
ExpansionAlternative = str
CanonicalExpansionAlternative = List[str]