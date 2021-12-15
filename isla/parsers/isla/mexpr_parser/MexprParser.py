# Generated from MexprParser.g4 by ANTLR 4.7.1
# encoding: utf-8
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys

def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\n")
        buf.write("\25\4\2\t\2\4\3\t\3\3\2\6\2\b\n\2\r\2\16\2\t\3\3\3\3\3")
        buf.write("\3\3\3\3\3\3\3\3\3\5\3\23\n\3\3\3\2\2\4\2\4\2\2\2\25\2")
        buf.write("\7\3\2\2\2\4\22\3\2\2\2\6\b\5\4\3\2\7\6\3\2\2\2\b\t\3")
        buf.write("\2\2\2\t\7\3\2\2\2\t\n\3\2\2\2\n\3\3\2\2\2\13\f\7\3\2")
        buf.write("\2\f\r\7\b\2\2\r\23\7\7\2\2\16\17\7\4\2\2\17\20\7\n\2")
        buf.write("\2\20\23\7\t\2\2\21\23\7\5\2\2\22\13\3\2\2\2\22\16\3\2")
        buf.write("\2\2\22\21\3\2\2\2\23\5\3\2\2\2\4\t\22")
        return buf.getvalue()


class MexprParser ( Parser ):

    grammarFileName = "MexprParser.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'{'", "'['", "<INVALID>", "<INVALID>", 
                     "'}'", "<INVALID>", "']'" ]

    symbolicNames = [ "<INVALID>", "BRAOP", "OPTOP", "TEXT", "NL", "BRACL", 
                      "ID", "OPTCL", "OPTTXT" ]

    RULE_matchExpr = 0
    RULE_matchExprElement = 1

    ruleNames =  [ "matchExpr", "matchExprElement" ]

    EOF = Token.EOF
    BRAOP=1
    OPTOP=2
    TEXT=3
    NL=4
    BRACL=5
    ID=6
    OPTCL=7
    OPTTXT=8

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None



    class MatchExprContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def matchExprElement(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(MexprParser.MatchExprElementContext)
            else:
                return self.getTypedRuleContext(MexprParser.MatchExprElementContext,i)


        def getRuleIndex(self):
            return MexprParser.RULE_matchExpr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterMatchExpr" ):
                listener.enterMatchExpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitMatchExpr" ):
                listener.exitMatchExpr(self)




    def matchExpr(self):

        localctx = MexprParser.MatchExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_matchExpr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 5 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 4
                self.matchExprElement()
                self.state = 7 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not ((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << MexprParser.BRAOP) | (1 << MexprParser.OPTOP) | (1 << MexprParser.TEXT))) != 0)):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class MatchExprElementContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return MexprParser.RULE_matchExprElement

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)



    class MatchExprCharsContext(MatchExprElementContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a MexprParser.MatchExprElementContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def TEXT(self):
            return self.getToken(MexprParser.TEXT, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterMatchExprChars" ):
                listener.enterMatchExprChars(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitMatchExprChars" ):
                listener.exitMatchExprChars(self)


    class MatchExprOptionalContext(MatchExprElementContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a MexprParser.MatchExprElementContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def OPTOP(self):
            return self.getToken(MexprParser.OPTOP, 0)
        def OPTTXT(self):
            return self.getToken(MexprParser.OPTTXT, 0)
        def OPTCL(self):
            return self.getToken(MexprParser.OPTCL, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterMatchExprOptional" ):
                listener.enterMatchExprOptional(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitMatchExprOptional" ):
                listener.exitMatchExprOptional(self)


    class MatchExprVarContext(MatchExprElementContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a MexprParser.MatchExprElementContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def BRAOP(self):
            return self.getToken(MexprParser.BRAOP, 0)
        def ID(self):
            return self.getToken(MexprParser.ID, 0)
        def BRACL(self):
            return self.getToken(MexprParser.BRACL, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterMatchExprVar" ):
                listener.enterMatchExprVar(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitMatchExprVar" ):
                listener.exitMatchExprVar(self)



    def matchExprElement(self):

        localctx = MexprParser.MatchExprElementContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_matchExprElement)
        try:
            self.state = 16
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [MexprParser.BRAOP]:
                localctx = MexprParser.MatchExprVarContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 9
                self.match(MexprParser.BRAOP)
                self.state = 10
                self.match(MexprParser.ID)
                self.state = 11
                self.match(MexprParser.BRACL)
                pass
            elif token in [MexprParser.OPTOP]:
                localctx = MexprParser.MatchExprOptionalContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 12
                self.match(MexprParser.OPTOP)
                self.state = 13
                self.match(MexprParser.OPTTXT)
                self.state = 14
                self.match(MexprParser.OPTCL)
                pass
            elif token in [MexprParser.TEXT]:
                localctx = MexprParser.MatchExprCharsContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 15
                self.match(MexprParser.TEXT)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





