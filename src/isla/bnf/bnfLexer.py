# Generated from bnf.g4 by ANTLR 4.10.1
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
    from typing import TextIO
else:
    from typing.io import TextIO


def serializedATN():
    return [
        4,0,7,60,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,
        6,7,6,1,0,1,0,1,0,1,0,1,1,1,1,1,2,1,2,4,2,24,8,2,11,2,12,2,25,1,
        2,1,2,1,3,1,3,1,3,5,3,33,8,3,10,3,12,3,36,9,3,1,3,1,3,1,4,1,4,1,
        4,1,5,4,5,44,8,5,11,5,12,5,45,1,5,1,5,1,6,1,6,5,6,52,8,6,10,6,12,
        6,55,9,6,1,6,1,6,1,6,1,6,2,34,53,0,7,1,1,3,2,5,3,7,4,9,5,11,6,13,
        7,1,0,3,2,0,60,60,62,62,6,0,34,34,92,92,98,98,110,110,114,114,116,
        116,3,0,9,10,13,13,32,32,64,0,1,1,0,0,0,0,3,1,0,0,0,0,5,1,0,0,0,
        0,7,1,0,0,0,0,9,1,0,0,0,0,11,1,0,0,0,0,13,1,0,0,0,1,15,1,0,0,0,3,
        19,1,0,0,0,5,21,1,0,0,0,7,29,1,0,0,0,9,39,1,0,0,0,11,43,1,0,0,0,
        13,49,1,0,0,0,15,16,5,58,0,0,16,17,5,58,0,0,17,18,5,61,0,0,18,2,
        1,0,0,0,19,20,5,124,0,0,20,4,1,0,0,0,21,23,5,60,0,0,22,24,8,0,0,
        0,23,22,1,0,0,0,24,25,1,0,0,0,25,23,1,0,0,0,25,26,1,0,0,0,26,27,
        1,0,0,0,27,28,5,62,0,0,28,6,1,0,0,0,29,34,5,34,0,0,30,33,3,9,4,0,
        31,33,9,0,0,0,32,30,1,0,0,0,32,31,1,0,0,0,33,36,1,0,0,0,34,35,1,
        0,0,0,34,32,1,0,0,0,35,37,1,0,0,0,36,34,1,0,0,0,37,38,5,34,0,0,38,
        8,1,0,0,0,39,40,5,92,0,0,40,41,7,1,0,0,41,10,1,0,0,0,42,44,7,2,0,
        0,43,42,1,0,0,0,44,45,1,0,0,0,45,43,1,0,0,0,45,46,1,0,0,0,46,47,
        1,0,0,0,47,48,6,5,0,0,48,12,1,0,0,0,49,53,5,35,0,0,50,52,9,0,0,0,
        51,50,1,0,0,0,52,55,1,0,0,0,53,54,1,0,0,0,53,51,1,0,0,0,54,56,1,
        0,0,0,55,53,1,0,0,0,56,57,5,10,0,0,57,58,1,0,0,0,58,59,6,6,0,0,59,
        14,1,0,0,0,6,0,25,32,34,45,53,1,6,0,0
    ]

class bnfLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    T__0 = 1
    T__1 = 2
    NONTERMINAL = 3
    STRING = 4
    ESC = 5
    WS = 6
    LINE_COMMENT = 7

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'::='", "'|'" ]

    symbolicNames = [ "<INVALID>",
            "NONTERMINAL", "STRING", "ESC", "WS", "LINE_COMMENT" ]

    ruleNames = [ "T__0", "T__1", "NONTERMINAL", "STRING", "ESC", "WS", 
                  "LINE_COMMENT" ]

    grammarFileName = "bnf.g4"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.10.1")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None


