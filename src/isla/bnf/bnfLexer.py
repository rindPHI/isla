# Generated from bnf.g4 by ANTLR 4.7.1
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\n")
        buf.write("B\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write("\4\b\t\b\4\t\t\t\3\2\3\2\3\2\3\2\3\3\3\3\3\4\3\4\3\5\3")
        buf.write("\5\6\5\36\n\5\r\5\16\5\37\3\5\3\5\3\6\3\6\3\6\7\6\'\n")
        buf.write("\6\f\6\16\6*\13\6\3\6\3\6\3\7\3\7\3\7\3\b\6\b\62\n\b\r")
        buf.write("\b\16\b\63\3\b\3\b\3\t\3\t\7\t:\n\t\f\t\16\t=\13\t\3\t")
        buf.write("\3\t\3\t\3\t\4(;\2\n\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21")
        buf.write("\n\3\2\5\4\2>>@@\b\2$$^^ddppttvv\5\2\13\f\17\17\"\"\2")
        buf.write("F\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13")
        buf.write("\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\3\23\3")
        buf.write("\2\2\2\5\27\3\2\2\2\7\31\3\2\2\2\t\33\3\2\2\2\13#\3\2")
        buf.write("\2\2\r-\3\2\2\2\17\61\3\2\2\2\21\67\3\2\2\2\23\24\7<\2")
        buf.write("\2\24\25\7<\2\2\25\26\7?\2\2\26\4\3\2\2\2\27\30\7~\2\2")
        buf.write("\30\6\3\2\2\2\31\32\7=\2\2\32\b\3\2\2\2\33\35\7>\2\2\34")
        buf.write("\36\n\2\2\2\35\34\3\2\2\2\36\37\3\2\2\2\37\35\3\2\2\2")
        buf.write("\37 \3\2\2\2 !\3\2\2\2!\"\7@\2\2\"\n\3\2\2\2#(\7$\2\2")
        buf.write("$\'\5\r\7\2%\'\13\2\2\2&$\3\2\2\2&%\3\2\2\2\'*\3\2\2\2")
        buf.write("()\3\2\2\2(&\3\2\2\2)+\3\2\2\2*(\3\2\2\2+,\7$\2\2,\f\3")
        buf.write("\2\2\2-.\7^\2\2./\t\3\2\2/\16\3\2\2\2\60\62\t\4\2\2\61")
        buf.write("\60\3\2\2\2\62\63\3\2\2\2\63\61\3\2\2\2\63\64\3\2\2\2")
        buf.write("\64\65\3\2\2\2\65\66\b\b\2\2\66\20\3\2\2\2\67;\7%\2\2")
        buf.write("8:\13\2\2\298\3\2\2\2:=\3\2\2\2;<\3\2\2\2;9\3\2\2\2<>")
        buf.write("\3\2\2\2=;\3\2\2\2>?\7\f\2\2?@\3\2\2\2@A\b\t\2\2A\22\3")
        buf.write("\2\2\2\b\2\37&(\63;\3\b\2\2")
        return buf.getvalue()


class bnfLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    T__0 = 1
    T__1 = 2
    T__2 = 3
    NONTERMINAL = 4
    STRING = 5
    ESC = 6
    WS = 7
    LINE_COMMENT = 8

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'::='", "'|'", "';'" ]

    symbolicNames = [ "<INVALID>",
            "NONTERMINAL", "STRING", "ESC", "WS", "LINE_COMMENT" ]

    ruleNames = [ "T__0", "T__1", "T__2", "NONTERMINAL", "STRING", "ESC", 
                  "WS", "LINE_COMMENT" ]

    grammarFileName = "bnf.g4"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7.1")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None


