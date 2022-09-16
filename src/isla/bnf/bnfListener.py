# Generated from bnf.g4 by ANTLR 4.11.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .bnfParser import bnfParser
else:
    from bnfParser import bnfParser

# This class defines a complete listener for a parse tree produced by bnfParser.
class bnfListener(ParseTreeListener):

    # Enter a parse tree produced by bnfParser#bnf_grammar.
    def enterBnf_grammar(self, ctx:bnfParser.Bnf_grammarContext):
        pass

    # Exit a parse tree produced by bnfParser#bnf_grammar.
    def exitBnf_grammar(self, ctx:bnfParser.Bnf_grammarContext):
        pass


    # Enter a parse tree produced by bnfParser#derivation_rule.
    def enterDerivation_rule(self, ctx:bnfParser.Derivation_ruleContext):
        pass

    # Exit a parse tree produced by bnfParser#derivation_rule.
    def exitDerivation_rule(self, ctx:bnfParser.Derivation_ruleContext):
        pass


    # Enter a parse tree produced by bnfParser#alternative.
    def enterAlternative(self, ctx:bnfParser.AlternativeContext):
        pass

    # Exit a parse tree produced by bnfParser#alternative.
    def exitAlternative(self, ctx:bnfParser.AlternativeContext):
        pass



del bnfParser