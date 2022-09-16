# Generated from MexprParser.g4 by ANTLR 4.11.1
# encoding: utf-8
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,11,27,2,0,7,0,2,1,7,1,2,2,7,2,1,0,4,0,8,8,0,11,0,12,0,9,1,1,
        1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,21,8,1,1,2,1,2,1,2,1,2,1,2,0,
        0,3,0,2,4,0,0,26,0,7,1,0,0,0,2,20,1,0,0,0,4,22,1,0,0,0,6,8,3,2,1,
        0,7,6,1,0,0,0,8,9,1,0,0,0,9,7,1,0,0,0,9,10,1,0,0,0,10,1,1,0,0,0,
        11,12,5,1,0,0,12,13,3,4,2,0,13,14,5,6,0,0,14,15,5,5,0,0,15,21,1,
        0,0,0,16,17,5,2,0,0,17,18,5,11,0,0,18,21,5,10,0,0,19,21,5,3,0,0,
        20,11,1,0,0,0,20,16,1,0,0,0,20,19,1,0,0,0,21,3,1,0,0,0,22,23,5,8,
        0,0,23,24,5,6,0,0,24,25,5,7,0,0,25,5,1,0,0,0,2,9,20
    ]

class MexprParser ( Parser ):

    grammarFileName = "MexprParser.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'{'", "'['", "<INVALID>", "<INVALID>", 
                     "'}'", "<INVALID>", "'>'", "'<'", "<INVALID>", "']'" ]

    symbolicNames = [ "<INVALID>", "BRAOP", "OPTOP", "TEXT", "NL", "BRACL", 
                      "ID", "GT", "LT", "WS", "OPTCL", "OPTTXT" ]

    RULE_matchExpr = 0
    RULE_matchExprElement = 1
    RULE_varType = 2

    ruleNames =  [ "matchExpr", "matchExprElement", "varType" ]

    EOF = Token.EOF
    BRAOP=1
    OPTOP=2
    TEXT=3
    NL=4
    BRACL=5
    ID=6
    GT=7
    LT=8
    WS=9
    OPTCL=10
    OPTTXT=11

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.11.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class MatchExprContext(ParserRuleContext):
        __slots__ = 'parser'

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
            self.state = 7 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 6
                self.matchExprElement()
                self.state = 9 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (((_la) & ~0x3f) == 0 and ((1 << _la) & 14) != 0):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class MatchExprElementContext(ParserRuleContext):
        __slots__ = 'parser'

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
        def varType(self):
            return self.getTypedRuleContext(MexprParser.VarTypeContext,0)

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
            self.state = 20
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                localctx = MexprParser.MatchExprVarContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 11
                self.match(MexprParser.BRAOP)
                self.state = 12
                self.varType()
                self.state = 13
                self.match(MexprParser.ID)
                self.state = 14
                self.match(MexprParser.BRACL)
                pass
            elif token in [2]:
                localctx = MexprParser.MatchExprOptionalContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 16
                self.match(MexprParser.OPTOP)
                self.state = 17
                self.match(MexprParser.OPTTXT)
                self.state = 18
                self.match(MexprParser.OPTCL)
                pass
            elif token in [3]:
                localctx = MexprParser.MatchExprCharsContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 19
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


    class VarTypeContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def LT(self):
            return self.getToken(MexprParser.LT, 0)

        def ID(self):
            return self.getToken(MexprParser.ID, 0)

        def GT(self):
            return self.getToken(MexprParser.GT, 0)

        def getRuleIndex(self):
            return MexprParser.RULE_varType

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterVarType" ):
                listener.enterVarType(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitVarType" ):
                listener.exitVarType(self)




    def varType(self):

        localctx = MexprParser.VarTypeContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_varType)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 22
            self.match(MexprParser.LT)
            self.state = 23
            self.match(MexprParser.ID)
            self.state = 24
            self.match(MexprParser.GT)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





