# Generated from MexprLexer.g4 by ANTLR 4.7.1
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\n")
        buf.write("G\b\1\b\1\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6")
        buf.write("\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t\13\3\2\3\2\3\2")
        buf.write("\3\2\3\3\3\3\3\3\3\3\3\4\6\4#\n\4\r\4\16\4$\3\5\6\5(\n")
        buf.write("\5\r\5\16\5)\3\5\3\5\3\6\3\6\3\6\3\6\3\7\3\7\3\7\7\7\65")
        buf.write("\n\7\f\7\16\78\13\7\3\b\5\b;\n\b\3\t\3\t\3\n\3\n\3\n\3")
        buf.write("\n\3\13\6\13D\n\13\r\13\16\13E\2\2\f\5\3\7\4\t\5\13\6")
        buf.write("\r\7\17\b\21\2\23\2\25\t\27\n\5\2\3\4\5\4\2]]}}\5\2C\\")
        buf.write("aac|\3\2__\2G\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13")
        buf.write("\3\2\2\2\3\r\3\2\2\2\3\17\3\2\2\2\4\25\3\2\2\2\4\27\3")
        buf.write("\2\2\2\5\31\3\2\2\2\7\35\3\2\2\2\t\"\3\2\2\2\13\'\3\2")
        buf.write("\2\2\r-\3\2\2\2\17\61\3\2\2\2\21:\3\2\2\2\23<\3\2\2\2")
        buf.write("\25>\3\2\2\2\27C\3\2\2\2\31\32\7}\2\2\32\33\3\2\2\2\33")
        buf.write("\34\b\2\2\2\34\6\3\2\2\2\35\36\7]\2\2\36\37\3\2\2\2\37")
        buf.write(" \b\3\3\2 \b\3\2\2\2!#\n\2\2\2\"!\3\2\2\2#$\3\2\2\2$\"")
        buf.write("\3\2\2\2$%\3\2\2\2%\n\3\2\2\2&(\7\f\2\2\'&\3\2\2\2()\3")
        buf.write("\2\2\2)\'\3\2\2\2)*\3\2\2\2*+\3\2\2\2+,\b\5\4\2,\f\3\2")
        buf.write("\2\2-.\7\177\2\2./\3\2\2\2/\60\b\6\5\2\60\16\3\2\2\2\61")
        buf.write("\66\5\21\b\2\62\65\5\21\b\2\63\65\5\23\t\2\64\62\3\2\2")
        buf.write("\2\64\63\3\2\2\2\658\3\2\2\2\66\64\3\2\2\2\66\67\3\2\2")
        buf.write("\2\67\20\3\2\2\28\66\3\2\2\29;\t\3\2\2:9\3\2\2\2;\22\3")
        buf.write("\2\2\2<=\4\62;\2=\24\3\2\2\2>?\7_\2\2?@\3\2\2\2@A\b\n")
        buf.write("\5\2A\26\3\2\2\2BD\n\4\2\2CB\3\2\2\2DE\3\2\2\2EC\3\2\2")
        buf.write("\2EF\3\2\2\2F\30\3\2\2\2\13\2\3\4$)\64\66:E\6\7\3\2\7")
        buf.write("\4\2\b\2\2\6\2\2")
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
    OPTCL = 7
    OPTTXT = 8

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE", "VAR_DECL", "OPTIONAL" ]

    literalNames = [ "<INVALID>",
            "'{'", "'['", "'}'", "']'" ]

    symbolicNames = [ "<INVALID>",
            "BRAOP", "OPTOP", "TEXT", "NL", "BRACL", "ID", "OPTCL", "OPTTXT" ]

    ruleNames = [ "BRAOP", "OPTOP", "TEXT", "NL", "BRACL", "ID", "ID_LETTER", 
                  "DIGIT", "OPTCL", "OPTTXT" ]

    grammarFileName = "MexprLexer.g4"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7.1")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None


