# Generated from bnf.g4 by ANTLR 4.11.1
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
        4,1,8,30,2,0,7,0,2,1,7,1,2,2,7,2,1,0,4,0,8,8,0,11,0,12,0,9,1,1,1,
        1,1,1,1,1,1,1,5,1,17,8,1,10,1,12,1,20,9,1,1,1,3,1,23,8,1,1,2,4,2,
        26,8,2,11,2,12,2,27,1,2,0,0,3,0,2,4,0,1,1,0,4,5,30,0,7,1,0,0,0,2,
        11,1,0,0,0,4,25,1,0,0,0,6,8,3,2,1,0,7,6,1,0,0,0,8,9,1,0,0,0,9,7,
        1,0,0,0,9,10,1,0,0,0,10,1,1,0,0,0,11,12,5,4,0,0,12,13,5,1,0,0,13,
        18,3,4,2,0,14,15,5,2,0,0,15,17,3,4,2,0,16,14,1,0,0,0,17,20,1,0,0,
        0,18,16,1,0,0,0,18,19,1,0,0,0,19,22,1,0,0,0,20,18,1,0,0,0,21,23,
        5,3,0,0,22,21,1,0,0,0,22,23,1,0,0,0,23,3,1,0,0,0,24,26,7,0,0,0,25,
        24,1,0,0,0,26,27,1,0,0,0,27,25,1,0,0,0,27,28,1,0,0,0,28,5,1,0,0,
        0,4,9,18,22,27
    ]

class bnfParser ( Parser ):

    grammarFileName = "bnf.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'::='", "'|'", "';'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "NONTERMINAL", "STRING", "ESC", "WS", "LINE_COMMENT" ]

    RULE_bnf_grammar = 0
    RULE_derivation_rule = 1
    RULE_alternative = 2

    ruleNames =  [ "bnf_grammar", "derivation_rule", "alternative" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    NONTERMINAL=4
    STRING=5
    ESC=6
    WS=7
    LINE_COMMENT=8

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.11.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class Bnf_grammarContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def derivation_rule(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(bnfParser.Derivation_ruleContext)
            else:
                return self.getTypedRuleContext(bnfParser.Derivation_ruleContext,i)


        def getRuleIndex(self):
            return bnfParser.RULE_bnf_grammar

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBnf_grammar" ):
                listener.enterBnf_grammar(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBnf_grammar" ):
                listener.exitBnf_grammar(self)




    def bnf_grammar(self):

        localctx = bnfParser.Bnf_grammarContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_bnf_grammar)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 7 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 6
                self.derivation_rule()
                self.state = 9 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==4):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Derivation_ruleContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def NONTERMINAL(self):
            return self.getToken(bnfParser.NONTERMINAL, 0)

        def alternative(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(bnfParser.AlternativeContext)
            else:
                return self.getTypedRuleContext(bnfParser.AlternativeContext,i)


        def getRuleIndex(self):
            return bnfParser.RULE_derivation_rule

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterDerivation_rule" ):
                listener.enterDerivation_rule(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitDerivation_rule" ):
                listener.exitDerivation_rule(self)




    def derivation_rule(self):

        localctx = bnfParser.Derivation_ruleContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_derivation_rule)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 11
            self.match(bnfParser.NONTERMINAL)
            self.state = 12
            self.match(bnfParser.T__0)
            self.state = 13
            self.alternative()
            self.state = 18
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2:
                self.state = 14
                self.match(bnfParser.T__1)
                self.state = 15
                self.alternative()
                self.state = 20
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 22
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==3:
                self.state = 21
                self.match(bnfParser.T__2)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class AlternativeContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def STRING(self, i:int=None):
            if i is None:
                return self.getTokens(bnfParser.STRING)
            else:
                return self.getToken(bnfParser.STRING, i)

        def NONTERMINAL(self, i:int=None):
            if i is None:
                return self.getTokens(bnfParser.NONTERMINAL)
            else:
                return self.getToken(bnfParser.NONTERMINAL, i)

        def getRuleIndex(self):
            return bnfParser.RULE_alternative

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterAlternative" ):
                listener.enterAlternative(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitAlternative" ):
                listener.exitAlternative(self)




    def alternative(self):

        localctx = bnfParser.AlternativeContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_alternative)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 25 
            self._errHandler.sync(self)
            _alt = 1
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt == 1:
                    self.state = 24
                    _la = self._input.LA(1)
                    if not(_la==4 or _la==5):
                        self._errHandler.recoverInline(self)
                    else:
                        self._errHandler.reportMatch(self)
                        self.consume()

                else:
                    raise NoViableAltException(self)
                self.state = 27 
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,3,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





