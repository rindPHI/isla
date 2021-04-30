from typing import Tuple, Optional, List

ParseTree = Tuple[str, Optional[List['ParseTree']]]
Path = Tuple[int, ...]