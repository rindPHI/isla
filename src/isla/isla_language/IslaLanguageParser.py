# Generated from IslaLanguage.g4 by ANTLR 4.10.1
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
        4,1,43,182,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,1,0,3,0,12,8,
        0,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,2,3,2,26,8,2,1,2,
        1,2,1,2,3,2,31,8,2,3,2,33,8,2,1,2,1,2,1,2,1,2,1,2,3,2,40,8,2,1,2,
        1,2,1,2,3,2,45,8,2,3,2,47,8,2,1,2,1,2,1,2,1,2,1,2,3,2,54,8,2,1,2,
        1,2,1,2,1,2,1,2,3,2,61,8,2,3,2,63,8,2,1,2,1,2,1,2,1,2,1,2,3,2,70,
        8,2,1,2,1,2,1,2,1,2,1,2,3,2,77,8,2,3,2,79,8,2,1,2,1,2,1,2,1,2,1,
        2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,5,2,100,
        8,2,10,2,12,2,103,9,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,3,2,112,8,2,1,
        2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,5,2,129,
        8,2,10,2,12,2,132,9,2,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,
        3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,4,3,155,8,3,11,3,12,3,
        156,1,3,1,3,3,3,161,8,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,
        1,3,1,3,5,3,175,8,3,10,3,12,3,178,9,3,1,4,1,4,1,4,0,2,4,6,5,0,2,
        4,6,8,0,7,3,0,7,7,20,23,34,41,1,0,20,21,1,0,22,23,1,0,36,37,1,0,
        34,35,2,0,7,7,38,41,1,0,24,28,219,0,11,1,0,0,0,2,15,1,0,0,0,4,111,
        1,0,0,0,6,160,1,0,0,0,8,179,1,0,0,0,10,12,3,2,1,0,11,10,1,0,0,0,
        11,12,1,0,0,0,12,13,1,0,0,0,13,14,3,4,2,0,14,1,1,0,0,0,15,16,5,1,
        0,0,16,17,5,27,0,0,17,18,5,2,0,0,18,19,5,25,0,0,19,20,5,3,0,0,20,
        3,1,0,0,0,21,22,6,2,-1,0,22,23,5,4,0,0,23,25,5,25,0,0,24,26,5,27,
        0,0,25,24,1,0,0,0,25,26,1,0,0,0,26,32,1,0,0,0,27,30,5,5,0,0,28,31,
        5,27,0,0,29,31,5,25,0,0,30,28,1,0,0,0,30,29,1,0,0,0,31,33,1,0,0,
        0,32,27,1,0,0,0,32,33,1,0,0,0,33,34,1,0,0,0,34,35,5,2,0,0,35,112,
        3,4,2,15,36,37,5,6,0,0,37,39,5,25,0,0,38,40,5,27,0,0,39,38,1,0,0,
        0,39,40,1,0,0,0,40,46,1,0,0,0,41,44,5,5,0,0,42,45,5,27,0,0,43,45,
        5,25,0,0,44,42,1,0,0,0,44,43,1,0,0,0,45,47,1,0,0,0,46,41,1,0,0,0,
        46,47,1,0,0,0,47,48,1,0,0,0,48,49,5,2,0,0,49,112,3,4,2,14,50,51,
        5,4,0,0,51,53,5,25,0,0,52,54,5,27,0,0,53,52,1,0,0,0,53,54,1,0,0,
        0,54,55,1,0,0,0,55,56,5,7,0,0,56,62,5,26,0,0,57,60,5,5,0,0,58,61,
        5,27,0,0,59,61,5,25,0,0,60,58,1,0,0,0,60,59,1,0,0,0,61,63,1,0,0,
        0,62,57,1,0,0,0,62,63,1,0,0,0,63,64,1,0,0,0,64,65,5,2,0,0,65,112,
        3,4,2,13,66,67,5,6,0,0,67,69,5,25,0,0,68,70,5,27,0,0,69,68,1,0,0,
        0,69,70,1,0,0,0,70,71,1,0,0,0,71,72,5,7,0,0,72,78,5,26,0,0,73,76,
        5,5,0,0,74,77,5,27,0,0,75,77,5,25,0,0,76,74,1,0,0,0,76,75,1,0,0,
        0,77,79,1,0,0,0,78,73,1,0,0,0,78,79,1,0,0,0,79,80,1,0,0,0,80,81,
        5,2,0,0,81,112,3,4,2,12,82,83,5,6,0,0,83,84,5,8,0,0,84,85,5,27,0,
        0,85,86,5,2,0,0,86,112,3,4,2,11,87,88,5,4,0,0,88,89,5,8,0,0,89,90,
        5,27,0,0,90,91,5,2,0,0,91,112,3,4,2,10,92,93,5,9,0,0,93,112,3,4,
        2,9,94,95,5,27,0,0,95,96,5,15,0,0,96,101,3,8,4,0,97,98,5,16,0,0,
        98,100,3,8,4,0,99,97,1,0,0,0,100,103,1,0,0,0,101,99,1,0,0,0,101,
        102,1,0,0,0,102,104,1,0,0,0,103,101,1,0,0,0,104,105,5,17,0,0,105,
        112,1,0,0,0,106,112,3,6,3,0,107,108,5,15,0,0,108,109,3,4,2,0,109,
        110,5,17,0,0,110,112,1,0,0,0,111,21,1,0,0,0,111,36,1,0,0,0,111,50,
        1,0,0,0,111,66,1,0,0,0,111,82,1,0,0,0,111,87,1,0,0,0,111,92,1,0,
        0,0,111,94,1,0,0,0,111,106,1,0,0,0,111,107,1,0,0,0,112,130,1,0,0,
        0,113,114,10,8,0,0,114,115,5,10,0,0,115,129,3,4,2,9,116,117,10,7,
        0,0,117,118,5,11,0,0,118,129,3,4,2,8,119,120,10,6,0,0,120,121,5,
        12,0,0,121,129,3,4,2,7,122,123,10,5,0,0,123,124,5,13,0,0,124,129,
        3,4,2,6,125,126,10,4,0,0,126,127,5,14,0,0,127,129,3,4,2,5,128,113,
        1,0,0,0,128,116,1,0,0,0,128,119,1,0,0,0,128,122,1,0,0,0,128,125,
        1,0,0,0,129,132,1,0,0,0,130,128,1,0,0,0,130,131,1,0,0,0,131,5,1,
        0,0,0,132,130,1,0,0,0,133,134,6,3,-1,0,134,161,5,18,0,0,135,161,
        5,19,0,0,136,161,5,28,0,0,137,161,5,27,0,0,138,161,5,24,0,0,139,
        161,5,25,0,0,140,161,5,26,0,0,141,161,7,0,0,0,142,143,7,1,0,0,143,
        144,5,15,0,0,144,145,3,6,3,0,145,146,5,17,0,0,146,161,1,0,0,0,147,
        148,5,15,0,0,148,149,3,6,3,0,149,150,5,17,0,0,150,161,1,0,0,0,151,
        152,5,15,0,0,152,154,3,6,3,0,153,155,3,6,3,0,154,153,1,0,0,0,155,
        156,1,0,0,0,156,154,1,0,0,0,156,157,1,0,0,0,157,158,1,0,0,0,158,
        159,5,17,0,0,159,161,1,0,0,0,160,133,1,0,0,0,160,135,1,0,0,0,160,
        136,1,0,0,0,160,137,1,0,0,0,160,138,1,0,0,0,160,139,1,0,0,0,160,
        140,1,0,0,0,160,141,1,0,0,0,160,142,1,0,0,0,160,147,1,0,0,0,160,
        151,1,0,0,0,161,176,1,0,0,0,162,163,10,6,0,0,163,164,7,2,0,0,164,
        175,3,6,3,7,165,166,10,5,0,0,166,167,7,3,0,0,167,175,3,6,3,6,168,
        169,10,4,0,0,169,170,7,4,0,0,170,175,3,6,3,5,171,172,10,3,0,0,172,
        173,7,5,0,0,173,175,3,6,3,4,174,162,1,0,0,0,174,165,1,0,0,0,174,
        168,1,0,0,0,174,171,1,0,0,0,175,178,1,0,0,0,176,174,1,0,0,0,176,
        177,1,0,0,0,177,7,1,0,0,0,178,176,1,0,0,0,179,180,7,6,0,0,180,9,
        1,0,0,0,21,11,25,30,32,39,44,46,53,60,62,69,76,78,101,111,128,130,
        156,160,174,176
    ]

class IslaLanguageParser ( Parser ):

    grammarFileName = "IslaLanguage.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'const'", "':'", "';'", "'forall'", "'in'", 
                     "'exists'", "'='", "'int'", "'not'", "'and'", "'or'", 
                     "'xor'", "'implies'", "'iff'", "'('", "','", "')'", 
                     "'true'", "'false'", "'re.+'", "'re.*'", "'re.++'", 
                     "'str.++'", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "'.'", "'..'", 
                     "'['", "']'", "'/'", "'*'", "'+'", "'-'", "'>='", "'<='", 
                     "'>'", "'<'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "XPATHEXPR", "VAR_TYPE", "STRING", "ID", "INT", "ESC", 
                      "DOT", "TWODOTS", "BROP", "BRCL", "DIV", "MUL", "PLUS", 
                      "MINUS", "GEQ", "LEQ", "GT", "LT", "WS", "LINE_COMMENT" ]

    RULE_start = 0
    RULE_constDecl = 1
    RULE_formula = 2
    RULE_sexpr = 3
    RULE_predicateArg = 4

    ruleNames =  [ "start", "constDecl", "formula", "sexpr", "predicateArg" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    T__6=7
    T__7=8
    T__8=9
    T__9=10
    T__10=11
    T__11=12
    T__12=13
    T__13=14
    T__14=15
    T__15=16
    T__16=17
    T__17=18
    T__18=19
    T__19=20
    T__20=21
    T__21=22
    T__22=23
    XPATHEXPR=24
    VAR_TYPE=25
    STRING=26
    ID=27
    INT=28
    ESC=29
    DOT=30
    TWODOTS=31
    BROP=32
    BRCL=33
    DIV=34
    MUL=35
    PLUS=36
    MINUS=37
    GEQ=38
    LEQ=39
    GT=40
    LT=41
    WS=42
    LINE_COMMENT=43

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.10.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class StartContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)


        def constDecl(self):
            return self.getTypedRuleContext(IslaLanguageParser.ConstDeclContext,0)


        def getRuleIndex(self):
            return IslaLanguageParser.RULE_start

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterStart" ):
                listener.enterStart(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitStart" ):
                listener.exitStart(self)




    def start(self):

        localctx = IslaLanguageParser.StartContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_start)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 11
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==IslaLanguageParser.T__0:
                self.state = 10
                self.constDecl()


            self.state = 13
            self.formula(0)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ConstDeclContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self):
            return self.getToken(IslaLanguageParser.ID, 0)

        def VAR_TYPE(self):
            return self.getToken(IslaLanguageParser.VAR_TYPE, 0)

        def getRuleIndex(self):
            return IslaLanguageParser.RULE_constDecl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterConstDecl" ):
                listener.enterConstDecl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitConstDecl" ):
                listener.exitConstDecl(self)




    def constDecl(self):

        localctx = IslaLanguageParser.ConstDeclContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_constDecl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 15
            self.match(IslaLanguageParser.T__0)
            self.state = 16
            self.match(IslaLanguageParser.ID)
            self.state = 17
            self.match(IslaLanguageParser.T__1)
            self.state = 18
            self.match(IslaLanguageParser.VAR_TYPE)
            self.state = 19
            self.match(IslaLanguageParser.T__2)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class FormulaContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return IslaLanguageParser.RULE_formula

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class ExistsMexprContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.boundVarType = None # Token
            self.varId = None # Token
            self.inId = None # Token
            self.inVarType = None # Token
            self.copyFrom(ctx)

        def STRING(self):
            return self.getToken(IslaLanguageParser.STRING, 0)
        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)

        def VAR_TYPE(self, i:int=None):
            if i is None:
                return self.getTokens(IslaLanguageParser.VAR_TYPE)
            else:
                return self.getToken(IslaLanguageParser.VAR_TYPE, i)
        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(IslaLanguageParser.ID)
            else:
                return self.getToken(IslaLanguageParser.ID, i)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExistsMexpr" ):
                listener.enterExistsMexpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExistsMexpr" ):
                listener.exitExistsMexpr(self)


    class NegationContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterNegation" ):
                listener.enterNegation(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitNegation" ):
                listener.exitNegation(self)


    class ImplicationContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.FormulaContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterImplication" ):
                listener.enterImplication(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitImplication" ):
                listener.exitImplication(self)


    class ForallMexprContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.boundVarType = None # Token
            self.varId = None # Token
            self.inId = None # Token
            self.inVarType = None # Token
            self.copyFrom(ctx)

        def STRING(self):
            return self.getToken(IslaLanguageParser.STRING, 0)
        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)

        def VAR_TYPE(self, i:int=None):
            if i is None:
                return self.getTokens(IslaLanguageParser.VAR_TYPE)
            else:
                return self.getToken(IslaLanguageParser.VAR_TYPE, i)
        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(IslaLanguageParser.ID)
            else:
                return self.getToken(IslaLanguageParser.ID, i)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterForallMexpr" ):
                listener.enterForallMexpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitForallMexpr" ):
                listener.exitForallMexpr(self)


    class ExistsIntContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(IslaLanguageParser.ID, 0)
        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExistsInt" ):
                listener.enterExistsInt(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExistsInt" ):
                listener.exitExistsInt(self)


    class DisjunctionContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.FormulaContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterDisjunction" ):
                listener.enterDisjunction(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitDisjunction" ):
                listener.exitDisjunction(self)


    class PredicateAtomContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(IslaLanguageParser.ID, 0)
        def predicateArg(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.PredicateArgContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.PredicateArgContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterPredicateAtom" ):
                listener.enterPredicateAtom(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitPredicateAtom" ):
                listener.exitPredicateAtom(self)


    class SMTFormulaContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def sexpr(self):
            return self.getTypedRuleContext(IslaLanguageParser.SexprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSMTFormula" ):
                listener.enterSMTFormula(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSMTFormula" ):
                listener.exitSMTFormula(self)


    class EquivalenceContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.FormulaContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterEquivalence" ):
                listener.enterEquivalence(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitEquivalence" ):
                listener.exitEquivalence(self)


    class ExistsContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.boundVarType = None # Token
            self.varId = None # Token
            self.inId = None # Token
            self.inVarType = None # Token
            self.copyFrom(ctx)

        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)

        def VAR_TYPE(self, i:int=None):
            if i is None:
                return self.getTokens(IslaLanguageParser.VAR_TYPE)
            else:
                return self.getToken(IslaLanguageParser.VAR_TYPE, i)
        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(IslaLanguageParser.ID)
            else:
                return self.getToken(IslaLanguageParser.ID, i)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExists" ):
                listener.enterExists(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExists" ):
                listener.exitExists(self)


    class ConjunctionContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.FormulaContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterConjunction" ):
                listener.enterConjunction(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitConjunction" ):
                listener.exitConjunction(self)


    class ParFormulaContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterParFormula" ):
                listener.enterParFormula(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitParFormula" ):
                listener.exitParFormula(self)


    class ForallContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.boundVarType = None # Token
            self.varId = None # Token
            self.inId = None # Token
            self.inVarType = None # Token
            self.copyFrom(ctx)

        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)

        def VAR_TYPE(self, i:int=None):
            if i is None:
                return self.getTokens(IslaLanguageParser.VAR_TYPE)
            else:
                return self.getToken(IslaLanguageParser.VAR_TYPE, i)
        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(IslaLanguageParser.ID)
            else:
                return self.getToken(IslaLanguageParser.ID, i)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterForall" ):
                listener.enterForall(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitForall" ):
                listener.exitForall(self)


    class ExclusiveOrContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.FormulaContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExclusiveOr" ):
                listener.enterExclusiveOr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExclusiveOr" ):
                listener.exitExclusiveOr(self)


    class ForallIntContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(IslaLanguageParser.ID, 0)
        def formula(self):
            return self.getTypedRuleContext(IslaLanguageParser.FormulaContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterForallInt" ):
                listener.enterForallInt(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitForallInt" ):
                listener.exitForallInt(self)



    def formula(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = IslaLanguageParser.FormulaContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 4
        self.enterRecursionRule(localctx, 4, self.RULE_formula, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 111
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,14,self._ctx)
            if la_ == 1:
                localctx = IslaLanguageParser.ForallContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 22
                self.match(IslaLanguageParser.T__3)

                self.state = 23
                localctx.boundVarType = self.match(IslaLanguageParser.VAR_TYPE)
                self.state = 25
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==IslaLanguageParser.ID:
                    self.state = 24
                    localctx.varId = self.match(IslaLanguageParser.ID)


                self.state = 32
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==IslaLanguageParser.T__4:
                    self.state = 27
                    self.match(IslaLanguageParser.T__4)
                    self.state = 30
                    self._errHandler.sync(self)
                    token = self._input.LA(1)
                    if token in [IslaLanguageParser.ID]:
                        self.state = 28
                        localctx.inId = self.match(IslaLanguageParser.ID)
                        pass
                    elif token in [IslaLanguageParser.VAR_TYPE]:
                        self.state = 29
                        localctx.inVarType = self.match(IslaLanguageParser.VAR_TYPE)
                        pass
                    else:
                        raise NoViableAltException(self)



                self.state = 34
                self.match(IslaLanguageParser.T__1)
                self.state = 35
                self.formula(15)
                pass

            elif la_ == 2:
                localctx = IslaLanguageParser.ExistsContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 36
                self.match(IslaLanguageParser.T__5)

                self.state = 37
                localctx.boundVarType = self.match(IslaLanguageParser.VAR_TYPE)
                self.state = 39
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==IslaLanguageParser.ID:
                    self.state = 38
                    localctx.varId = self.match(IslaLanguageParser.ID)


                self.state = 46
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==IslaLanguageParser.T__4:
                    self.state = 41
                    self.match(IslaLanguageParser.T__4)
                    self.state = 44
                    self._errHandler.sync(self)
                    token = self._input.LA(1)
                    if token in [IslaLanguageParser.ID]:
                        self.state = 42
                        localctx.inId = self.match(IslaLanguageParser.ID)
                        pass
                    elif token in [IslaLanguageParser.VAR_TYPE]:
                        self.state = 43
                        localctx.inVarType = self.match(IslaLanguageParser.VAR_TYPE)
                        pass
                    else:
                        raise NoViableAltException(self)



                self.state = 48
                self.match(IslaLanguageParser.T__1)
                self.state = 49
                self.formula(14)
                pass

            elif la_ == 3:
                localctx = IslaLanguageParser.ForallMexprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 50
                self.match(IslaLanguageParser.T__3)

                self.state = 51
                localctx.boundVarType = self.match(IslaLanguageParser.VAR_TYPE)
                self.state = 53
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==IslaLanguageParser.ID:
                    self.state = 52
                    localctx.varId = self.match(IslaLanguageParser.ID)


                self.state = 55
                self.match(IslaLanguageParser.T__6)
                self.state = 56
                self.match(IslaLanguageParser.STRING)
                self.state = 62
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==IslaLanguageParser.T__4:
                    self.state = 57
                    self.match(IslaLanguageParser.T__4)
                    self.state = 60
                    self._errHandler.sync(self)
                    token = self._input.LA(1)
                    if token in [IslaLanguageParser.ID]:
                        self.state = 58
                        localctx.inId = self.match(IslaLanguageParser.ID)
                        pass
                    elif token in [IslaLanguageParser.VAR_TYPE]:
                        self.state = 59
                        localctx.inVarType = self.match(IslaLanguageParser.VAR_TYPE)
                        pass
                    else:
                        raise NoViableAltException(self)



                self.state = 64
                self.match(IslaLanguageParser.T__1)
                self.state = 65
                self.formula(13)
                pass

            elif la_ == 4:
                localctx = IslaLanguageParser.ExistsMexprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 66
                self.match(IslaLanguageParser.T__5)

                self.state = 67
                localctx.boundVarType = self.match(IslaLanguageParser.VAR_TYPE)
                self.state = 69
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==IslaLanguageParser.ID:
                    self.state = 68
                    localctx.varId = self.match(IslaLanguageParser.ID)


                self.state = 71
                self.match(IslaLanguageParser.T__6)
                self.state = 72
                self.match(IslaLanguageParser.STRING)
                self.state = 78
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==IslaLanguageParser.T__4:
                    self.state = 73
                    self.match(IslaLanguageParser.T__4)
                    self.state = 76
                    self._errHandler.sync(self)
                    token = self._input.LA(1)
                    if token in [IslaLanguageParser.ID]:
                        self.state = 74
                        localctx.inId = self.match(IslaLanguageParser.ID)
                        pass
                    elif token in [IslaLanguageParser.VAR_TYPE]:
                        self.state = 75
                        localctx.inVarType = self.match(IslaLanguageParser.VAR_TYPE)
                        pass
                    else:
                        raise NoViableAltException(self)



                self.state = 80
                self.match(IslaLanguageParser.T__1)
                self.state = 81
                self.formula(12)
                pass

            elif la_ == 5:
                localctx = IslaLanguageParser.ExistsIntContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 82
                self.match(IslaLanguageParser.T__5)
                self.state = 83
                self.match(IslaLanguageParser.T__7)
                self.state = 84
                self.match(IslaLanguageParser.ID)
                self.state = 85
                self.match(IslaLanguageParser.T__1)
                self.state = 86
                self.formula(11)
                pass

            elif la_ == 6:
                localctx = IslaLanguageParser.ForallIntContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 87
                self.match(IslaLanguageParser.T__3)
                self.state = 88
                self.match(IslaLanguageParser.T__7)
                self.state = 89
                self.match(IslaLanguageParser.ID)
                self.state = 90
                self.match(IslaLanguageParser.T__1)
                self.state = 91
                self.formula(10)
                pass

            elif la_ == 7:
                localctx = IslaLanguageParser.NegationContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 92
                self.match(IslaLanguageParser.T__8)
                self.state = 93
                self.formula(9)
                pass

            elif la_ == 8:
                localctx = IslaLanguageParser.PredicateAtomContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 94
                self.match(IslaLanguageParser.ID)
                self.state = 95
                self.match(IslaLanguageParser.T__14)
                self.state = 96
                self.predicateArg()
                self.state = 101
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while _la==IslaLanguageParser.T__15:
                    self.state = 97
                    self.match(IslaLanguageParser.T__15)
                    self.state = 98
                    self.predicateArg()
                    self.state = 103
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)

                self.state = 104
                self.match(IslaLanguageParser.T__16)
                pass

            elif la_ == 9:
                localctx = IslaLanguageParser.SMTFormulaContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 106
                self.sexpr(0)
                pass

            elif la_ == 10:
                localctx = IslaLanguageParser.ParFormulaContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 107
                self.match(IslaLanguageParser.T__14)
                self.state = 108
                self.formula(0)
                self.state = 109
                self.match(IslaLanguageParser.T__16)
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 130
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,16,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 128
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,15,self._ctx)
                    if la_ == 1:
                        localctx = IslaLanguageParser.ConjunctionContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 113
                        if not self.precpred(self._ctx, 8):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 8)")
                        self.state = 114
                        self.match(IslaLanguageParser.T__9)
                        self.state = 115
                        self.formula(9)
                        pass

                    elif la_ == 2:
                        localctx = IslaLanguageParser.DisjunctionContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 116
                        if not self.precpred(self._ctx, 7):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 7)")
                        self.state = 117
                        self.match(IslaLanguageParser.T__10)
                        self.state = 118
                        self.formula(8)
                        pass

                    elif la_ == 3:
                        localctx = IslaLanguageParser.ExclusiveOrContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 119
                        if not self.precpred(self._ctx, 6):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 6)")
                        self.state = 120
                        self.match(IslaLanguageParser.T__11)
                        self.state = 121
                        self.formula(7)
                        pass

                    elif la_ == 4:
                        localctx = IslaLanguageParser.ImplicationContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 122
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 123
                        self.match(IslaLanguageParser.T__12)
                        self.state = 124
                        self.formula(6)
                        pass

                    elif la_ == 5:
                        localctx = IslaLanguageParser.EquivalenceContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 125
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 126
                        self.match(IslaLanguageParser.T__13)
                        self.state = 127
                        self.formula(5)
                        pass

             
                self.state = 132
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,16,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class SexprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return IslaLanguageParser.RULE_sexpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class SexprInfixReStrContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def sexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.SexprContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.SexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprInfixReStr" ):
                listener.enterSexprInfixReStr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprInfixReStr" ):
                listener.exitSexprInfixReStr(self)


    class SexprNumContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def INT(self):
            return self.getToken(IslaLanguageParser.INT, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprNum" ):
                listener.enterSexprNum(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprNum" ):
                listener.exitSexprNum(self)


    class SexprXPathExprContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def XPATHEXPR(self):
            return self.getToken(IslaLanguageParser.XPATHEXPR, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprXPathExpr" ):
                listener.enterSexprXPathExpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprXPathExpr" ):
                listener.exitSexprXPathExpr(self)


    class SexprOpContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def GEQ(self):
            return self.getToken(IslaLanguageParser.GEQ, 0)
        def LEQ(self):
            return self.getToken(IslaLanguageParser.LEQ, 0)
        def GT(self):
            return self.getToken(IslaLanguageParser.GT, 0)
        def LT(self):
            return self.getToken(IslaLanguageParser.LT, 0)
        def DIV(self):
            return self.getToken(IslaLanguageParser.DIV, 0)
        def MUL(self):
            return self.getToken(IslaLanguageParser.MUL, 0)
        def PLUS(self):
            return self.getToken(IslaLanguageParser.PLUS, 0)
        def MINUS(self):
            return self.getToken(IslaLanguageParser.MINUS, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprOp" ):
                listener.enterSexprOp(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprOp" ):
                listener.exitSexprOp(self)


    class SexprInfixPlusMinusContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def sexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.SexprContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.SexprContext,i)

        def PLUS(self):
            return self.getToken(IslaLanguageParser.PLUS, 0)
        def MINUS(self):
            return self.getToken(IslaLanguageParser.MINUS, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprInfixPlusMinus" ):
                listener.enterSexprInfixPlusMinus(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprInfixPlusMinus" ):
                listener.exitSexprInfixPlusMinus(self)


    class SexprTrueContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprTrue" ):
                listener.enterSexprTrue(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprTrue" ):
                listener.exitSexprTrue(self)


    class SexprFreeIdContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def VAR_TYPE(self):
            return self.getToken(IslaLanguageParser.VAR_TYPE, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprFreeId" ):
                listener.enterSexprFreeId(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprFreeId" ):
                listener.exitSexprFreeId(self)


    class SepxrAppContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.op = None # SexprContext
            self.copyFrom(ctx)

        def sexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.SexprContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.SexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSepxrApp" ):
                listener.enterSepxrApp(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSepxrApp" ):
                listener.exitSepxrApp(self)


    class SexprInfixMulDivContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def sexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.SexprContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.SexprContext,i)

        def MUL(self):
            return self.getToken(IslaLanguageParser.MUL, 0)
        def DIV(self):
            return self.getToken(IslaLanguageParser.DIV, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprInfixMulDiv" ):
                listener.enterSexprInfixMulDiv(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprInfixMulDiv" ):
                listener.exitSexprInfixMulDiv(self)


    class SexprIdContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(IslaLanguageParser.ID, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprId" ):
                listener.enterSexprId(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprId" ):
                listener.exitSexprId(self)


    class SexprPrefixContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def sexpr(self):
            return self.getTypedRuleContext(IslaLanguageParser.SexprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprPrefix" ):
                listener.enterSexprPrefix(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprPrefix" ):
                listener.exitSexprPrefix(self)


    class SepxrParenContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def sexpr(self):
            return self.getTypedRuleContext(IslaLanguageParser.SexprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSepxrParen" ):
                listener.enterSepxrParen(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSepxrParen" ):
                listener.exitSepxrParen(self)


    class SexprStrContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def STRING(self):
            return self.getToken(IslaLanguageParser.STRING, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprStr" ):
                listener.enterSexprStr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprStr" ):
                listener.exitSexprStr(self)


    class SexprInfixEqContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def sexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.SexprContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.SexprContext,i)

        def GEQ(self):
            return self.getToken(IslaLanguageParser.GEQ, 0)
        def LEQ(self):
            return self.getToken(IslaLanguageParser.LEQ, 0)
        def GT(self):
            return self.getToken(IslaLanguageParser.GT, 0)
        def LT(self):
            return self.getToken(IslaLanguageParser.LT, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprInfixEq" ):
                listener.enterSexprInfixEq(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprInfixEq" ):
                listener.exitSexprInfixEq(self)


    class SexprFalseContext(SexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a IslaLanguageParser.SexprContext
            super().__init__(parser)
            self.copyFrom(ctx)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprFalse" ):
                listener.enterSexprFalse(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprFalse" ):
                listener.exitSexprFalse(self)



    def sexpr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = IslaLanguageParser.SexprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 6
        self.enterRecursionRule(localctx, 6, self.RULE_sexpr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 160
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,18,self._ctx)
            if la_ == 1:
                localctx = IslaLanguageParser.SexprTrueContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 134
                self.match(IslaLanguageParser.T__17)
                pass

            elif la_ == 2:
                localctx = IslaLanguageParser.SexprFalseContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 135
                self.match(IslaLanguageParser.T__18)
                pass

            elif la_ == 3:
                localctx = IslaLanguageParser.SexprNumContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 136
                self.match(IslaLanguageParser.INT)
                pass

            elif la_ == 4:
                localctx = IslaLanguageParser.SexprIdContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 137
                self.match(IslaLanguageParser.ID)
                pass

            elif la_ == 5:
                localctx = IslaLanguageParser.SexprXPathExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 138
                self.match(IslaLanguageParser.XPATHEXPR)
                pass

            elif la_ == 6:
                localctx = IslaLanguageParser.SexprFreeIdContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 139
                self.match(IslaLanguageParser.VAR_TYPE)
                pass

            elif la_ == 7:
                localctx = IslaLanguageParser.SexprStrContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 140
                self.match(IslaLanguageParser.STRING)
                pass

            elif la_ == 8:
                localctx = IslaLanguageParser.SexprOpContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 141
                _la = self._input.LA(1)
                if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << IslaLanguageParser.T__6) | (1 << IslaLanguageParser.T__19) | (1 << IslaLanguageParser.T__20) | (1 << IslaLanguageParser.T__21) | (1 << IslaLanguageParser.T__22) | (1 << IslaLanguageParser.DIV) | (1 << IslaLanguageParser.MUL) | (1 << IslaLanguageParser.PLUS) | (1 << IslaLanguageParser.MINUS) | (1 << IslaLanguageParser.GEQ) | (1 << IslaLanguageParser.LEQ) | (1 << IslaLanguageParser.GT) | (1 << IslaLanguageParser.LT))) != 0)):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                pass

            elif la_ == 9:
                localctx = IslaLanguageParser.SexprPrefixContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 142
                localctx.op = self._input.LT(1)
                _la = self._input.LA(1)
                if not(_la==IslaLanguageParser.T__19 or _la==IslaLanguageParser.T__20):
                    localctx.op = self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 143
                self.match(IslaLanguageParser.T__14)
                self.state = 144
                self.sexpr(0)
                self.state = 145
                self.match(IslaLanguageParser.T__16)
                pass

            elif la_ == 10:
                localctx = IslaLanguageParser.SepxrParenContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 147
                self.match(IslaLanguageParser.T__14)
                self.state = 148
                self.sexpr(0)
                self.state = 149
                self.match(IslaLanguageParser.T__16)
                pass

            elif la_ == 11:
                localctx = IslaLanguageParser.SepxrAppContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 151
                self.match(IslaLanguageParser.T__14)
                self.state = 152
                localctx.op = self.sexpr(0)
                self.state = 154 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while True:
                    self.state = 153
                    self.sexpr(0)
                    self.state = 156 
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)
                    if not ((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << IslaLanguageParser.T__6) | (1 << IslaLanguageParser.T__14) | (1 << IslaLanguageParser.T__17) | (1 << IslaLanguageParser.T__18) | (1 << IslaLanguageParser.T__19) | (1 << IslaLanguageParser.T__20) | (1 << IslaLanguageParser.T__21) | (1 << IslaLanguageParser.T__22) | (1 << IslaLanguageParser.XPATHEXPR) | (1 << IslaLanguageParser.VAR_TYPE) | (1 << IslaLanguageParser.STRING) | (1 << IslaLanguageParser.ID) | (1 << IslaLanguageParser.INT) | (1 << IslaLanguageParser.DIV) | (1 << IslaLanguageParser.MUL) | (1 << IslaLanguageParser.PLUS) | (1 << IslaLanguageParser.MINUS) | (1 << IslaLanguageParser.GEQ) | (1 << IslaLanguageParser.LEQ) | (1 << IslaLanguageParser.GT) | (1 << IslaLanguageParser.LT))) != 0)):
                        break

                self.state = 158
                self.match(IslaLanguageParser.T__16)
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 176
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,20,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 174
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,19,self._ctx)
                    if la_ == 1:
                        localctx = IslaLanguageParser.SexprInfixReStrContext(self, IslaLanguageParser.SexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_sexpr)
                        self.state = 162
                        if not self.precpred(self._ctx, 6):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 6)")
                        self.state = 163
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==IslaLanguageParser.T__21 or _la==IslaLanguageParser.T__22):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 164
                        self.sexpr(7)
                        pass

                    elif la_ == 2:
                        localctx = IslaLanguageParser.SexprInfixPlusMinusContext(self, IslaLanguageParser.SexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_sexpr)
                        self.state = 165
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 166
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==IslaLanguageParser.PLUS or _la==IslaLanguageParser.MINUS):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 167
                        self.sexpr(6)
                        pass

                    elif la_ == 3:
                        localctx = IslaLanguageParser.SexprInfixMulDivContext(self, IslaLanguageParser.SexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_sexpr)
                        self.state = 168
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 169
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==IslaLanguageParser.DIV or _la==IslaLanguageParser.MUL):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 170
                        self.sexpr(5)
                        pass

                    elif la_ == 4:
                        localctx = IslaLanguageParser.SexprInfixEqContext(self, IslaLanguageParser.SexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_sexpr)
                        self.state = 171
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 172
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << IslaLanguageParser.T__6) | (1 << IslaLanguageParser.GEQ) | (1 << IslaLanguageParser.LEQ) | (1 << IslaLanguageParser.GT) | (1 << IslaLanguageParser.LT))) != 0)):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 173
                        self.sexpr(4)
                        pass

             
                self.state = 178
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,20,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class PredicateArgContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self):
            return self.getToken(IslaLanguageParser.ID, 0)

        def VAR_TYPE(self):
            return self.getToken(IslaLanguageParser.VAR_TYPE, 0)

        def INT(self):
            return self.getToken(IslaLanguageParser.INT, 0)

        def STRING(self):
            return self.getToken(IslaLanguageParser.STRING, 0)

        def XPATHEXPR(self):
            return self.getToken(IslaLanguageParser.XPATHEXPR, 0)

        def getRuleIndex(self):
            return IslaLanguageParser.RULE_predicateArg

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterPredicateArg" ):
                listener.enterPredicateArg(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitPredicateArg" ):
                listener.exitPredicateArg(self)




    def predicateArg(self):

        localctx = IslaLanguageParser.PredicateArgContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_predicateArg)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 179
            _la = self._input.LA(1)
            if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << IslaLanguageParser.XPATHEXPR) | (1 << IslaLanguageParser.VAR_TYPE) | (1 << IslaLanguageParser.STRING) | (1 << IslaLanguageParser.ID) | (1 << IslaLanguageParser.INT))) != 0)):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[2] = self.formula_sempred
        self._predicates[3] = self.sexpr_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def formula_sempred(self, localctx:FormulaContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 8)
         

            if predIndex == 1:
                return self.precpred(self._ctx, 7)
         

            if predIndex == 2:
                return self.precpred(self._ctx, 6)
         

            if predIndex == 3:
                return self.precpred(self._ctx, 5)
         

            if predIndex == 4:
                return self.precpred(self._ctx, 4)
         

    def sexpr_sempred(self, localctx:SexprContext, predIndex:int):
            if predIndex == 5:
                return self.precpred(self._ctx, 6)
         

            if predIndex == 6:
                return self.precpred(self._ctx, 5)
         

            if predIndex == 7:
                return self.precpred(self._ctx, 4)
         

            if predIndex == 8:
                return self.precpred(self._ctx, 3)
         




