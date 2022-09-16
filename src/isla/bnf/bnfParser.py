# Generated from bnf.g4 by ANTLR 4.7.1
# encoding: utf-8
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys

def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\n")
        buf.write(" \4\2\t\2\4\3\t\3\4\4\t\4\3\2\6\2\n\n\2\r\2\16\2\13\3")
        buf.write("\3\3\3\3\3\3\3\3\3\7\3\23\n\3\f\3\16\3\26\13\3\3\3\5\3")
        buf.write("\31\n\3\3\4\6\4\34\n\4\r\4\16\4\35\3\4\2\2\5\2\4\6\2\3")
        buf.write("\3\2\6\7\2 \2\t\3\2\2\2\4\r\3\2\2\2\6\33\3\2\2\2\b\n\5")
        buf.write("\4\3\2\t\b\3\2\2\2\n\13\3\2\2\2\13\t\3\2\2\2\13\f\3\2")
        buf.write("\2\2\f\3\3\2\2\2\r\16\7\6\2\2\16\17\7\3\2\2\17\24\5\6")
        buf.write("\4\2\20\21\7\4\2\2\21\23\5\6\4\2\22\20\3\2\2\2\23\26\3")
        buf.write("\2\2\2\24\22\3\2\2\2\24\25\3\2\2\2\25\30\3\2\2\2\26\24")
        buf.write("\3\2\2\2\27\31\7\5\2\2\30\27\3\2\2\2\30\31\3\2\2\2\31")
        buf.write("\5\3\2\2\2\32\34\t\2\2\2\33\32\3\2\2\2\34\35\3\2\2\2\35")
        buf.write("\33\3\2\2\2\35\36\3\2\2\2\36\7\3\2\2\2\6\13\24\30\35")
        return buf.getvalue()


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
        self.checkVersion("4.7.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None



    class Bnf_grammarContext(ParserRuleContext):

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
                if not (_la==bnfParser.NONTERMINAL):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class Derivation_ruleContext(ParserRuleContext):

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
            while _la==bnfParser.T__1:
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
            if _la==bnfParser.T__2:
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
                    if not(_la==bnfParser.NONTERMINAL or _la==bnfParser.STRING):
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





