# Generated from IslaLanguage.g4 by ANTLR 4.11.1
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
        4,1,44,193,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,1,0,3,
        0,14,8,0,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,2,3,2,28,
        8,2,1,2,1,2,1,2,3,2,33,8,2,3,2,35,8,2,1,2,1,2,1,2,1,2,1,2,3,2,42,
        8,2,1,2,1,2,1,2,3,2,47,8,2,3,2,49,8,2,1,2,1,2,1,2,1,2,1,2,3,2,56,
        8,2,1,2,1,2,1,2,1,2,1,2,3,2,63,8,2,3,2,65,8,2,1,2,1,2,1,2,1,2,1,
        2,3,2,72,8,2,1,2,1,2,1,2,1,2,1,2,3,2,79,8,2,3,2,81,8,2,1,2,1,2,1,
        2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,
        2,5,2,102,8,2,10,2,12,2,105,9,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,3,2,
        114,8,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,
        1,2,5,2,131,8,2,10,2,12,2,134,9,2,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,
        3,1,3,1,3,3,3,146,8,3,1,3,1,3,1,3,1,3,1,3,5,3,153,8,3,10,3,12,3,
        156,9,3,3,3,158,8,3,1,3,1,3,1,3,1,3,4,3,164,8,3,11,3,12,3,165,1,
        3,1,3,3,3,170,8,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,
        3,5,3,184,8,3,10,3,12,3,187,9,3,1,4,1,4,1,5,1,5,1,5,0,2,4,6,6,0,
        2,4,6,8,10,0,5,2,0,25,26,36,36,1,0,37,38,2,0,7,7,39,42,2,0,23,24,
        28,30,6,0,7,7,15,16,18,19,21,21,25,26,36,42,231,0,13,1,0,0,0,2,17,
        1,0,0,0,4,113,1,0,0,0,6,169,1,0,0,0,8,188,1,0,0,0,10,190,1,0,0,0,
        12,14,3,2,1,0,13,12,1,0,0,0,13,14,1,0,0,0,14,15,1,0,0,0,15,16,3,
        4,2,0,16,1,1,0,0,0,17,18,5,1,0,0,18,19,5,29,0,0,19,20,5,2,0,0,20,
        21,5,24,0,0,21,22,5,3,0,0,22,3,1,0,0,0,23,24,6,2,-1,0,24,25,5,4,
        0,0,25,27,5,24,0,0,26,28,5,29,0,0,27,26,1,0,0,0,27,28,1,0,0,0,28,
        34,1,0,0,0,29,32,5,5,0,0,30,33,5,29,0,0,31,33,5,24,0,0,32,30,1,0,
        0,0,32,31,1,0,0,0,33,35,1,0,0,0,34,29,1,0,0,0,34,35,1,0,0,0,35,36,
        1,0,0,0,36,37,5,2,0,0,37,114,3,4,2,15,38,39,5,6,0,0,39,41,5,24,0,
        0,40,42,5,29,0,0,41,40,1,0,0,0,41,42,1,0,0,0,42,48,1,0,0,0,43,46,
        5,5,0,0,44,47,5,29,0,0,45,47,5,24,0,0,46,44,1,0,0,0,46,45,1,0,0,
        0,47,49,1,0,0,0,48,43,1,0,0,0,48,49,1,0,0,0,49,50,1,0,0,0,50,51,
        5,2,0,0,51,114,3,4,2,14,52,53,5,4,0,0,53,55,5,24,0,0,54,56,5,29,
        0,0,55,54,1,0,0,0,55,56,1,0,0,0,56,57,1,0,0,0,57,58,5,7,0,0,58,64,
        5,28,0,0,59,62,5,5,0,0,60,63,5,29,0,0,61,63,5,24,0,0,62,60,1,0,0,
        0,62,61,1,0,0,0,63,65,1,0,0,0,64,59,1,0,0,0,64,65,1,0,0,0,65,66,
        1,0,0,0,66,67,5,2,0,0,67,114,3,4,2,13,68,69,5,6,0,0,69,71,5,24,0,
        0,70,72,5,29,0,0,71,70,1,0,0,0,71,72,1,0,0,0,72,73,1,0,0,0,73,74,
        5,7,0,0,74,80,5,28,0,0,75,78,5,5,0,0,76,79,5,29,0,0,77,79,5,24,0,
        0,78,76,1,0,0,0,78,77,1,0,0,0,79,81,1,0,0,0,80,75,1,0,0,0,80,81,
        1,0,0,0,81,82,1,0,0,0,82,83,5,2,0,0,83,114,3,4,2,12,84,85,5,6,0,
        0,85,86,5,8,0,0,86,87,5,29,0,0,87,88,5,2,0,0,88,114,3,4,2,11,89,
        90,5,4,0,0,90,91,5,8,0,0,91,92,5,29,0,0,92,93,5,2,0,0,93,114,3,4,
        2,10,94,95,5,17,0,0,95,114,3,4,2,9,96,97,5,29,0,0,97,98,5,10,0,0,
        98,103,3,8,4,0,99,100,5,11,0,0,100,102,3,8,4,0,101,99,1,0,0,0,102,
        105,1,0,0,0,103,101,1,0,0,0,103,104,1,0,0,0,104,106,1,0,0,0,105,
        103,1,0,0,0,106,107,5,12,0,0,107,114,1,0,0,0,108,109,5,10,0,0,109,
        110,3,4,2,0,110,111,5,12,0,0,111,114,1,0,0,0,112,114,3,6,3,0,113,
        23,1,0,0,0,113,38,1,0,0,0,113,52,1,0,0,0,113,68,1,0,0,0,113,84,1,
        0,0,0,113,89,1,0,0,0,113,94,1,0,0,0,113,96,1,0,0,0,113,108,1,0,0,
        0,113,112,1,0,0,0,114,132,1,0,0,0,115,116,10,8,0,0,116,117,5,15,
        0,0,117,131,3,4,2,9,118,119,10,7,0,0,119,120,5,16,0,0,120,131,3,
        4,2,8,121,122,10,6,0,0,122,123,5,18,0,0,123,131,3,4,2,7,124,125,
        10,5,0,0,125,126,5,20,0,0,126,131,3,4,2,6,127,128,10,4,0,0,128,129,
        5,9,0,0,129,131,3,4,2,5,130,115,1,0,0,0,130,118,1,0,0,0,130,121,
        1,0,0,0,130,124,1,0,0,0,130,127,1,0,0,0,131,134,1,0,0,0,132,130,
        1,0,0,0,132,133,1,0,0,0,133,5,1,0,0,0,134,132,1,0,0,0,135,136,6,
        3,-1,0,136,170,5,13,0,0,137,170,5,14,0,0,138,170,5,30,0,0,139,170,
        5,29,0,0,140,170,5,23,0,0,141,170,5,24,0,0,142,170,5,28,0,0,143,
        146,5,22,0,0,144,146,3,10,5,0,145,143,1,0,0,0,145,144,1,0,0,0,146,
        170,1,0,0,0,147,148,5,22,0,0,148,157,5,10,0,0,149,154,3,6,3,0,150,
        151,5,11,0,0,151,153,3,6,3,0,152,150,1,0,0,0,153,156,1,0,0,0,154,
        152,1,0,0,0,154,155,1,0,0,0,155,158,1,0,0,0,156,154,1,0,0,0,157,
        149,1,0,0,0,157,158,1,0,0,0,158,159,1,0,0,0,159,170,5,12,0,0,160,
        161,5,10,0,0,161,163,3,6,3,0,162,164,3,6,3,0,163,162,1,0,0,0,164,
        165,1,0,0,0,165,163,1,0,0,0,165,166,1,0,0,0,166,167,1,0,0,0,167,
        168,5,12,0,0,168,170,1,0,0,0,169,135,1,0,0,0,169,137,1,0,0,0,169,
        138,1,0,0,0,169,139,1,0,0,0,169,140,1,0,0,0,169,141,1,0,0,0,169,
        142,1,0,0,0,169,145,1,0,0,0,169,147,1,0,0,0,169,160,1,0,0,0,170,
        185,1,0,0,0,171,172,10,5,0,0,172,173,5,21,0,0,173,184,3,6,3,6,174,
        175,10,4,0,0,175,176,7,0,0,0,176,184,3,6,3,5,177,178,10,3,0,0,178,
        179,7,1,0,0,179,184,3,6,3,4,180,181,10,2,0,0,181,182,7,2,0,0,182,
        184,3,6,3,3,183,171,1,0,0,0,183,174,1,0,0,0,183,177,1,0,0,0,183,
        180,1,0,0,0,184,187,1,0,0,0,185,183,1,0,0,0,185,186,1,0,0,0,186,
        7,1,0,0,0,187,185,1,0,0,0,188,189,7,3,0,0,189,9,1,0,0,0,190,191,
        7,4,0,0,191,11,1,0,0,0,24,13,27,32,34,41,46,48,55,62,64,71,78,80,
        103,113,130,132,145,154,157,165,169,183,185
    ]

class IslaLanguageParser ( Parser ):

    grammarFileName = "IslaLanguage.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'const'", "':'", "';'", "'forall'", "'in'", 
                     "'exists'", "'='", "'int'", "'iff'", "'('", "','", 
                     "')'", "'true'", "'false'", "'and'", "'or'", "'not'", 
                     "'xor'", "'=>'", "'implies'", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "'div'", "'mod'", "'abs'", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "'.'", "'..'", "'['", "']'", "'*'", "'+'", "'-'", "'>='", 
                     "'<='", "'>'", "'<'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "AND", "OR", 
                      "NOT", "XOR", "IMPLIES_SMT", "IMPLIES_ISLA", "SMT_INFIX_RE_STR", 
                      "SMT_NONBINARY_OP", "XPATHEXPR", "VAR_TYPE", "DIV", 
                      "MOD", "ABS", "STRING", "ID", "INT", "ESC", "DOT", 
                      "TWODOTS", "BROP", "BRCL", "MUL", "PLUS", "MINUS", 
                      "GEQ", "LEQ", "GT", "LT", "WS", "LINE_COMMENT" ]

    RULE_start = 0
    RULE_constDecl = 1
    RULE_formula = 2
    RULE_sexpr = 3
    RULE_predicateArg = 4
    RULE_smt_binary_op = 5

    ruleNames =  [ "start", "constDecl", "formula", "sexpr", "predicateArg", 
                   "smt_binary_op" ]

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
    AND=15
    OR=16
    NOT=17
    XOR=18
    IMPLIES_SMT=19
    IMPLIES_ISLA=20
    SMT_INFIX_RE_STR=21
    SMT_NONBINARY_OP=22
    XPATHEXPR=23
    VAR_TYPE=24
    DIV=25
    MOD=26
    ABS=27
    STRING=28
    ID=29
    INT=30
    ESC=31
    DOT=32
    TWODOTS=33
    BROP=34
    BRCL=35
    MUL=36
    PLUS=37
    MINUS=38
    GEQ=39
    LEQ=40
    GT=41
    LT=42
    WS=43
    LINE_COMMENT=44

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.11.1")
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
            self.state = 13
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==1:
                self.state = 12
                self.constDecl()


            self.state = 15
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
            self.state = 17
            self.match(IslaLanguageParser.T__0)
            self.state = 18
            self.match(IslaLanguageParser.ID)
            self.state = 19
            self.match(IslaLanguageParser.T__1)
            self.state = 20
            self.match(IslaLanguageParser.VAR_TYPE)
            self.state = 21
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

        def NOT(self):
            return self.getToken(IslaLanguageParser.NOT, 0)
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

        def IMPLIES_ISLA(self):
            return self.getToken(IslaLanguageParser.IMPLIES_ISLA, 0)

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

        def OR(self):
            return self.getToken(IslaLanguageParser.OR, 0)

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

        def AND(self):
            return self.getToken(IslaLanguageParser.AND, 0)

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

        def XOR(self):
            return self.getToken(IslaLanguageParser.XOR, 0)

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
            self.state = 113
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,14,self._ctx)
            if la_ == 1:
                localctx = IslaLanguageParser.ForallContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 24
                self.match(IslaLanguageParser.T__3)

                self.state = 25
                localctx.boundVarType = self.match(IslaLanguageParser.VAR_TYPE)
                self.state = 27
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==29:
                    self.state = 26
                    localctx.varId = self.match(IslaLanguageParser.ID)


                self.state = 34
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==5:
                    self.state = 29
                    self.match(IslaLanguageParser.T__4)
                    self.state = 32
                    self._errHandler.sync(self)
                    token = self._input.LA(1)
                    if token in [29]:
                        self.state = 30
                        localctx.inId = self.match(IslaLanguageParser.ID)
                        pass
                    elif token in [24]:
                        self.state = 31
                        localctx.inVarType = self.match(IslaLanguageParser.VAR_TYPE)
                        pass
                    else:
                        raise NoViableAltException(self)



                self.state = 36
                self.match(IslaLanguageParser.T__1)
                self.state = 37
                self.formula(15)
                pass

            elif la_ == 2:
                localctx = IslaLanguageParser.ExistsContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 38
                self.match(IslaLanguageParser.T__5)

                self.state = 39
                localctx.boundVarType = self.match(IslaLanguageParser.VAR_TYPE)
                self.state = 41
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==29:
                    self.state = 40
                    localctx.varId = self.match(IslaLanguageParser.ID)


                self.state = 48
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==5:
                    self.state = 43
                    self.match(IslaLanguageParser.T__4)
                    self.state = 46
                    self._errHandler.sync(self)
                    token = self._input.LA(1)
                    if token in [29]:
                        self.state = 44
                        localctx.inId = self.match(IslaLanguageParser.ID)
                        pass
                    elif token in [24]:
                        self.state = 45
                        localctx.inVarType = self.match(IslaLanguageParser.VAR_TYPE)
                        pass
                    else:
                        raise NoViableAltException(self)



                self.state = 50
                self.match(IslaLanguageParser.T__1)
                self.state = 51
                self.formula(14)
                pass

            elif la_ == 3:
                localctx = IslaLanguageParser.ForallMexprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 52
                self.match(IslaLanguageParser.T__3)

                self.state = 53
                localctx.boundVarType = self.match(IslaLanguageParser.VAR_TYPE)
                self.state = 55
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==29:
                    self.state = 54
                    localctx.varId = self.match(IslaLanguageParser.ID)


                self.state = 57
                self.match(IslaLanguageParser.T__6)
                self.state = 58
                self.match(IslaLanguageParser.STRING)
                self.state = 64
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==5:
                    self.state = 59
                    self.match(IslaLanguageParser.T__4)
                    self.state = 62
                    self._errHandler.sync(self)
                    token = self._input.LA(1)
                    if token in [29]:
                        self.state = 60
                        localctx.inId = self.match(IslaLanguageParser.ID)
                        pass
                    elif token in [24]:
                        self.state = 61
                        localctx.inVarType = self.match(IslaLanguageParser.VAR_TYPE)
                        pass
                    else:
                        raise NoViableAltException(self)



                self.state = 66
                self.match(IslaLanguageParser.T__1)
                self.state = 67
                self.formula(13)
                pass

            elif la_ == 4:
                localctx = IslaLanguageParser.ExistsMexprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 68
                self.match(IslaLanguageParser.T__5)

                self.state = 69
                localctx.boundVarType = self.match(IslaLanguageParser.VAR_TYPE)
                self.state = 71
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==29:
                    self.state = 70
                    localctx.varId = self.match(IslaLanguageParser.ID)


                self.state = 73
                self.match(IslaLanguageParser.T__6)
                self.state = 74
                self.match(IslaLanguageParser.STRING)
                self.state = 80
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==5:
                    self.state = 75
                    self.match(IslaLanguageParser.T__4)
                    self.state = 78
                    self._errHandler.sync(self)
                    token = self._input.LA(1)
                    if token in [29]:
                        self.state = 76
                        localctx.inId = self.match(IslaLanguageParser.ID)
                        pass
                    elif token in [24]:
                        self.state = 77
                        localctx.inVarType = self.match(IslaLanguageParser.VAR_TYPE)
                        pass
                    else:
                        raise NoViableAltException(self)



                self.state = 82
                self.match(IslaLanguageParser.T__1)
                self.state = 83
                self.formula(12)
                pass

            elif la_ == 5:
                localctx = IslaLanguageParser.ExistsIntContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 84
                self.match(IslaLanguageParser.T__5)
                self.state = 85
                self.match(IslaLanguageParser.T__7)
                self.state = 86
                self.match(IslaLanguageParser.ID)
                self.state = 87
                self.match(IslaLanguageParser.T__1)
                self.state = 88
                self.formula(11)
                pass

            elif la_ == 6:
                localctx = IslaLanguageParser.ForallIntContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 89
                self.match(IslaLanguageParser.T__3)
                self.state = 90
                self.match(IslaLanguageParser.T__7)
                self.state = 91
                self.match(IslaLanguageParser.ID)
                self.state = 92
                self.match(IslaLanguageParser.T__1)
                self.state = 93
                self.formula(10)
                pass

            elif la_ == 7:
                localctx = IslaLanguageParser.NegationContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 94
                self.match(IslaLanguageParser.NOT)
                self.state = 95
                self.formula(9)
                pass

            elif la_ == 8:
                localctx = IslaLanguageParser.PredicateAtomContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 96
                self.match(IslaLanguageParser.ID)
                self.state = 97
                self.match(IslaLanguageParser.T__9)
                self.state = 98
                self.predicateArg()
                self.state = 103
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while _la==11:
                    self.state = 99
                    self.match(IslaLanguageParser.T__10)
                    self.state = 100
                    self.predicateArg()
                    self.state = 105
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)

                self.state = 106
                self.match(IslaLanguageParser.T__11)
                pass

            elif la_ == 9:
                localctx = IslaLanguageParser.ParFormulaContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 108
                self.match(IslaLanguageParser.T__9)
                self.state = 109
                self.formula(0)
                self.state = 110
                self.match(IslaLanguageParser.T__11)
                pass

            elif la_ == 10:
                localctx = IslaLanguageParser.SMTFormulaContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 112
                self.sexpr(0)
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 132
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,16,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 130
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,15,self._ctx)
                    if la_ == 1:
                        localctx = IslaLanguageParser.ConjunctionContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 115
                        if not self.precpred(self._ctx, 8):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 8)")
                        self.state = 116
                        self.match(IslaLanguageParser.AND)
                        self.state = 117
                        self.formula(9)
                        pass

                    elif la_ == 2:
                        localctx = IslaLanguageParser.DisjunctionContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 118
                        if not self.precpred(self._ctx, 7):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 7)")
                        self.state = 119
                        self.match(IslaLanguageParser.OR)
                        self.state = 120
                        self.formula(8)
                        pass

                    elif la_ == 3:
                        localctx = IslaLanguageParser.ExclusiveOrContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 121
                        if not self.precpred(self._ctx, 6):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 6)")
                        self.state = 122
                        self.match(IslaLanguageParser.XOR)
                        self.state = 123
                        self.formula(7)
                        pass

                    elif la_ == 4:
                        localctx = IslaLanguageParser.ImplicationContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 124
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 125
                        self.match(IslaLanguageParser.IMPLIES_ISLA)
                        self.state = 126
                        self.formula(6)
                        pass

                    elif la_ == 5:
                        localctx = IslaLanguageParser.EquivalenceContext(self, IslaLanguageParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 127
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 128
                        self.match(IslaLanguageParser.T__8)
                        self.state = 129
                        self.formula(5)
                        pass

             
                self.state = 134
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

        def SMT_INFIX_RE_STR(self):
            return self.getToken(IslaLanguageParser.SMT_INFIX_RE_STR, 0)

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

        def SMT_NONBINARY_OP(self):
            return self.getToken(IslaLanguageParser.SMT_NONBINARY_OP, 0)
        def smt_binary_op(self):
            return self.getTypedRuleContext(IslaLanguageParser.Smt_binary_opContext,0)


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
        def MOD(self):
            return self.getToken(IslaLanguageParser.MOD, 0)

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

        def SMT_NONBINARY_OP(self):
            return self.getToken(IslaLanguageParser.SMT_NONBINARY_OP, 0)
        def sexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(IslaLanguageParser.SexprContext)
            else:
                return self.getTypedRuleContext(IslaLanguageParser.SexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexprPrefix" ):
                listener.enterSexprPrefix(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexprPrefix" ):
                listener.exitSexprPrefix(self)


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
            self.state = 169
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,21,self._ctx)
            if la_ == 1:
                localctx = IslaLanguageParser.SexprTrueContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 136
                self.match(IslaLanguageParser.T__12)
                pass

            elif la_ == 2:
                localctx = IslaLanguageParser.SexprFalseContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 137
                self.match(IslaLanguageParser.T__13)
                pass

            elif la_ == 3:
                localctx = IslaLanguageParser.SexprNumContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 138
                self.match(IslaLanguageParser.INT)
                pass

            elif la_ == 4:
                localctx = IslaLanguageParser.SexprIdContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 139
                self.match(IslaLanguageParser.ID)
                pass

            elif la_ == 5:
                localctx = IslaLanguageParser.SexprXPathExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 140
                self.match(IslaLanguageParser.XPATHEXPR)
                pass

            elif la_ == 6:
                localctx = IslaLanguageParser.SexprFreeIdContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 141
                self.match(IslaLanguageParser.VAR_TYPE)
                pass

            elif la_ == 7:
                localctx = IslaLanguageParser.SexprStrContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 142
                self.match(IslaLanguageParser.STRING)
                pass

            elif la_ == 8:
                localctx = IslaLanguageParser.SexprOpContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 145
                self._errHandler.sync(self)
                token = self._input.LA(1)
                if token in [22]:
                    self.state = 143
                    self.match(IslaLanguageParser.SMT_NONBINARY_OP)
                    pass
                elif token in [7, 15, 16, 18, 19, 21, 25, 26, 36, 37, 38, 39, 40, 41, 42]:
                    self.state = 144
                    self.smt_binary_op()
                    pass
                else:
                    raise NoViableAltException(self)

                pass

            elif la_ == 9:
                localctx = IslaLanguageParser.SexprPrefixContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 147
                localctx.op = self.match(IslaLanguageParser.SMT_NONBINARY_OP)
                self.state = 148
                self.match(IslaLanguageParser.T__9)
                self.state = 157
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if ((_la) & ~0x3f) == 0 and ((1 << _la) & 8729385624704) != 0:
                    self.state = 149
                    self.sexpr(0)
                    self.state = 154
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)
                    while _la==11:
                        self.state = 150
                        self.match(IslaLanguageParser.T__10)
                        self.state = 151
                        self.sexpr(0)
                        self.state = 156
                        self._errHandler.sync(self)
                        _la = self._input.LA(1)



                self.state = 159
                self.match(IslaLanguageParser.T__11)
                pass

            elif la_ == 10:
                localctx = IslaLanguageParser.SepxrAppContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 160
                self.match(IslaLanguageParser.T__9)
                self.state = 161
                localctx.op = self.sexpr(0)
                self.state = 163 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while True:
                    self.state = 162
                    self.sexpr(0)
                    self.state = 165 
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)
                    if not (((_la) & ~0x3f) == 0 and ((1 << _la) & 8729385624704) != 0):
                        break

                self.state = 167
                self.match(IslaLanguageParser.T__11)
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 185
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,23,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 183
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,22,self._ctx)
                    if la_ == 1:
                        localctx = IslaLanguageParser.SexprInfixReStrContext(self, IslaLanguageParser.SexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_sexpr)
                        self.state = 171
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 172
                        localctx.op = self.match(IslaLanguageParser.SMT_INFIX_RE_STR)
                        self.state = 173
                        self.sexpr(6)
                        pass

                    elif la_ == 2:
                        localctx = IslaLanguageParser.SexprInfixMulDivContext(self, IslaLanguageParser.SexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_sexpr)
                        self.state = 174
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 175
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 68820140032) != 0):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 176
                        self.sexpr(5)
                        pass

                    elif la_ == 3:
                        localctx = IslaLanguageParser.SexprInfixPlusMinusContext(self, IslaLanguageParser.SexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_sexpr)
                        self.state = 177
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 178
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==37 or _la==38):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 179
                        self.sexpr(4)
                        pass

                    elif la_ == 4:
                        localctx = IslaLanguageParser.SexprInfixEqContext(self, IslaLanguageParser.SexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_sexpr)
                        self.state = 180
                        if not self.precpred(self._ctx, 2):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                        self.state = 181
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 8246337208448) != 0):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 182
                        self.sexpr(3)
                        pass

             
                self.state = 187
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,23,self._ctx)

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
            self.state = 188
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 1904214016) != 0):
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


    class Smt_binary_opContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def GEQ(self):
            return self.getToken(IslaLanguageParser.GEQ, 0)

        def LEQ(self):
            return self.getToken(IslaLanguageParser.LEQ, 0)

        def GT(self):
            return self.getToken(IslaLanguageParser.GT, 0)

        def LT(self):
            return self.getToken(IslaLanguageParser.LT, 0)

        def MUL(self):
            return self.getToken(IslaLanguageParser.MUL, 0)

        def DIV(self):
            return self.getToken(IslaLanguageParser.DIV, 0)

        def MOD(self):
            return self.getToken(IslaLanguageParser.MOD, 0)

        def PLUS(self):
            return self.getToken(IslaLanguageParser.PLUS, 0)

        def MINUS(self):
            return self.getToken(IslaLanguageParser.MINUS, 0)

        def SMT_INFIX_RE_STR(self):
            return self.getToken(IslaLanguageParser.SMT_INFIX_RE_STR, 0)

        def AND(self):
            return self.getToken(IslaLanguageParser.AND, 0)

        def OR(self):
            return self.getToken(IslaLanguageParser.OR, 0)

        def IMPLIES_SMT(self):
            return self.getToken(IslaLanguageParser.IMPLIES_SMT, 0)

        def XOR(self):
            return self.getToken(IslaLanguageParser.XOR, 0)

        def getRuleIndex(self):
            return IslaLanguageParser.RULE_smt_binary_op

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSmt_binary_op" ):
                listener.enterSmt_binary_op(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSmt_binary_op" ):
                listener.exitSmt_binary_op(self)




    def smt_binary_op(self):

        localctx = IslaLanguageParser.Smt_binary_opContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_smt_binary_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 190
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 8727477190784) != 0):
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
                return self.precpred(self._ctx, 5)
         

            if predIndex == 6:
                return self.precpred(self._ctx, 4)
         

            if predIndex == 7:
                return self.precpred(self._ctx, 3)
         

            if predIndex == 8:
                return self.precpred(self._ctx, 2)
         




