# Generated from MexprParser.g4 by ANTLR 4.11.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .MexprParser import MexprParser
else:
    from MexprParser import MexprParser

# This class defines a complete listener for a parse tree produced by MexprParser.
class MexprParserListener(ParseTreeListener):

    # Enter a parse tree produced by MexprParser#matchExpr.
    def enterMatchExpr(self, ctx:MexprParser.MatchExprContext):
        pass

    # Exit a parse tree produced by MexprParser#matchExpr.
    def exitMatchExpr(self, ctx:MexprParser.MatchExprContext):
        pass


    # Enter a parse tree produced by MexprParser#MatchExprVar.
    def enterMatchExprVar(self, ctx:MexprParser.MatchExprVarContext):
        pass

    # Exit a parse tree produced by MexprParser#MatchExprVar.
    def exitMatchExprVar(self, ctx:MexprParser.MatchExprVarContext):
        pass


    # Enter a parse tree produced by MexprParser#MatchExprOptional.
    def enterMatchExprOptional(self, ctx:MexprParser.MatchExprOptionalContext):
        pass

    # Exit a parse tree produced by MexprParser#MatchExprOptional.
    def exitMatchExprOptional(self, ctx:MexprParser.MatchExprOptionalContext):
        pass


    # Enter a parse tree produced by MexprParser#MatchExprChars.
    def enterMatchExprChars(self, ctx:MexprParser.MatchExprCharsContext):
        pass

    # Exit a parse tree produced by MexprParser#MatchExprChars.
    def exitMatchExprChars(self, ctx:MexprParser.MatchExprCharsContext):
        pass


    # Enter a parse tree produced by MexprParser#varType.
    def enterVarType(self, ctx:MexprParser.VarTypeContext):
        pass

    # Exit a parse tree produced by MexprParser#varType.
    def exitVarType(self, ctx:MexprParser.VarTypeContext):
        pass



del MexprParser