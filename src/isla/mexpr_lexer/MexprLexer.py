# Generated from MexprLexer.g4 by ANTLR 4.7.1
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\r")
        buf.write("X\b\1\b\1\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6")
        buf.write("\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t\13\4\f\t\f\4\r")
        buf.write("\t\r\4\16\t\16\3\2\3\2\3\2\3\2\3\3\3\3\3\3\3\3\3\4\6\4")
        buf.write(")\n\4\r\4\16\4*\3\5\6\5.\n\5\r\5\16\5/\3\5\3\5\3\6\3\6")
        buf.write("\3\6\3\6\3\7\3\7\3\7\7\7;\n\7\f\7\16\7>\13\7\3\b\5\bA")
        buf.write("\n\b\3\t\3\t\3\n\3\n\3\13\3\13\3\f\6\fJ\n\f\r\f\16\fK")
        buf.write("\3\f\3\f\3\r\3\r\3\r\3\r\3\16\6\16U\n\16\r\16\16\16V\2")
        buf.write("\2\17\5\3\7\4\t\5\13\6\r\7\17\b\21\2\23\2\25\t\27\n\31")
        buf.write("\13\33\f\35\r\5\2\3\4\6\4\2]]}}\6\2/\60C\\aac|\5\2\13")
        buf.write("\f\17\17\"\"\3\2__\2Y\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2")
        buf.write("\2\2\2\13\3\2\2\2\3\r\3\2\2\2\3\17\3\2\2\2\3\25\3\2\2")
        buf.write("\2\3\27\3\2\2\2\3\31\3\2\2\2\4\33\3\2\2\2\4\35\3\2\2\2")
        buf.write("\5\37\3\2\2\2\7#\3\2\2\2\t(\3\2\2\2\13-\3\2\2\2\r\63\3")
        buf.write("\2\2\2\17\67\3\2\2\2\21@\3\2\2\2\23B\3\2\2\2\25D\3\2\2")
        buf.write("\2\27F\3\2\2\2\31I\3\2\2\2\33O\3\2\2\2\35T\3\2\2\2\37")
        buf.write(" \7}\2\2 !\3\2\2\2!\"\b\2\2\2\"\6\3\2\2\2#$\7]\2\2$%\3")
        buf.write("\2\2\2%&\b\3\3\2&\b\3\2\2\2\')\n\2\2\2(\'\3\2\2\2)*\3")
        buf.write("\2\2\2*(\3\2\2\2*+\3\2\2\2+\n\3\2\2\2,.\7\f\2\2-,\3\2")
        buf.write("\2\2./\3\2\2\2/-\3\2\2\2/\60\3\2\2\2\60\61\3\2\2\2\61")
        buf.write("\62\b\5\4\2\62\f\3\2\2\2\63\64\7\177\2\2\64\65\3\2\2\2")
        buf.write("\65\66\b\6\5\2\66\16\3\2\2\2\67<\5\21\b\28;\5\21\b\29")
        buf.write(";\5\23\t\2:8\3\2\2\2:9\3\2\2\2;>\3\2\2\2<:\3\2\2\2<=\3")
        buf.write("\2\2\2=\20\3\2\2\2><\3\2\2\2?A\t\3\2\2@?\3\2\2\2A\22\3")
        buf.write("\2\2\2BC\4\62;\2C\24\3\2\2\2DE\7@\2\2E\26\3\2\2\2FG\7")
        buf.write(">\2\2G\30\3\2\2\2HJ\t\4\2\2IH\3\2\2\2JK\3\2\2\2KI\3\2")
        buf.write("\2\2KL\3\2\2\2LM\3\2\2\2MN\b\f\4\2N\32\3\2\2\2OP\7_\2")
        buf.write("\2PQ\3\2\2\2QR\b\r\5\2R\34\3\2\2\2SU\n\5\2\2TS\3\2\2\2")
        buf.write("UV\3\2\2\2VT\3\2\2\2VW\3\2\2\2W\36\3\2\2\2\f\2\3\4*/:")
        buf.write("<@KV\6\7\3\2\7\4\2\b\2\2\6\2\2")
        return buf.getvalue()


class MexprLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    VAR_DECL = 1
    OPTIONAL = 2

    BRAOP = 1
    OPTOP = 2
    TEXT = 3
    NL = 4
    BRACL = 5
    ID = 6
    GT = 7
    LT = 8
    WS = 9
    OPTCL = 10
    OPTTXT = 11

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE", "VAR_DECL", "OPTIONAL" ]

    literalNames = [ "<INVALID>",
            "'{'", "'['", "'}'", "'>'", "'<'", "']'" ]

    symbolicNames = [ "<INVALID>",
            "BRAOP", "OPTOP", "TEXT", "NL", "BRACL", "ID", "GT", "LT", "WS", 
            "OPTCL", "OPTTXT" ]

    ruleNames = [ "BRAOP", "OPTOP", "TEXT", "NL", "BRACL", "ID", "ID_LETTER", 
                  "DIGIT", "GT", "LT", "WS", "OPTCL", "OPTTXT" ]

    grammarFileName = "MexprLexer.g4"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7.1")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None


