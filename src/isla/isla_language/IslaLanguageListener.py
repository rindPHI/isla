# Generated from IslaLanguage.g4 by ANTLR 4.11.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .IslaLanguageParser import IslaLanguageParser
else:
    from IslaLanguageParser import IslaLanguageParser

# This class defines a complete listener for a parse tree produced by IslaLanguageParser.
class IslaLanguageListener(ParseTreeListener):

    # Enter a parse tree produced by IslaLanguageParser#start.
    def enterStart(self, ctx:IslaLanguageParser.StartContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#start.
    def exitStart(self, ctx:IslaLanguageParser.StartContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#constDecl.
    def enterConstDecl(self, ctx:IslaLanguageParser.ConstDeclContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#constDecl.
    def exitConstDecl(self, ctx:IslaLanguageParser.ConstDeclContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#ExistsMexpr.
    def enterExistsMexpr(self, ctx:IslaLanguageParser.ExistsMexprContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#ExistsMexpr.
    def exitExistsMexpr(self, ctx:IslaLanguageParser.ExistsMexprContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#Negation.
    def enterNegation(self, ctx:IslaLanguageParser.NegationContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#Negation.
    def exitNegation(self, ctx:IslaLanguageParser.NegationContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#Implication.
    def enterImplication(self, ctx:IslaLanguageParser.ImplicationContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#Implication.
    def exitImplication(self, ctx:IslaLanguageParser.ImplicationContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#ForallMexpr.
    def enterForallMexpr(self, ctx:IslaLanguageParser.ForallMexprContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#ForallMexpr.
    def exitForallMexpr(self, ctx:IslaLanguageParser.ForallMexprContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#ExistsInt.
    def enterExistsInt(self, ctx:IslaLanguageParser.ExistsIntContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#ExistsInt.
    def exitExistsInt(self, ctx:IslaLanguageParser.ExistsIntContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#Disjunction.
    def enterDisjunction(self, ctx:IslaLanguageParser.DisjunctionContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#Disjunction.
    def exitDisjunction(self, ctx:IslaLanguageParser.DisjunctionContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#PredicateAtom.
    def enterPredicateAtom(self, ctx:IslaLanguageParser.PredicateAtomContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#PredicateAtom.
    def exitPredicateAtom(self, ctx:IslaLanguageParser.PredicateAtomContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SMTFormula.
    def enterSMTFormula(self, ctx:IslaLanguageParser.SMTFormulaContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SMTFormula.
    def exitSMTFormula(self, ctx:IslaLanguageParser.SMTFormulaContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#Equivalence.
    def enterEquivalence(self, ctx:IslaLanguageParser.EquivalenceContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#Equivalence.
    def exitEquivalence(self, ctx:IslaLanguageParser.EquivalenceContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#Exists.
    def enterExists(self, ctx:IslaLanguageParser.ExistsContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#Exists.
    def exitExists(self, ctx:IslaLanguageParser.ExistsContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#Conjunction.
    def enterConjunction(self, ctx:IslaLanguageParser.ConjunctionContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#Conjunction.
    def exitConjunction(self, ctx:IslaLanguageParser.ConjunctionContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#ParFormula.
    def enterParFormula(self, ctx:IslaLanguageParser.ParFormulaContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#ParFormula.
    def exitParFormula(self, ctx:IslaLanguageParser.ParFormulaContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#Forall.
    def enterForall(self, ctx:IslaLanguageParser.ForallContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#Forall.
    def exitForall(self, ctx:IslaLanguageParser.ForallContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#ExclusiveOr.
    def enterExclusiveOr(self, ctx:IslaLanguageParser.ExclusiveOrContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#ExclusiveOr.
    def exitExclusiveOr(self, ctx:IslaLanguageParser.ExclusiveOrContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#ForallInt.
    def enterForallInt(self, ctx:IslaLanguageParser.ForallIntContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#ForallInt.
    def exitForallInt(self, ctx:IslaLanguageParser.ForallIntContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprInfixReStr.
    def enterSexprInfixReStr(self, ctx:IslaLanguageParser.SexprInfixReStrContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprInfixReStr.
    def exitSexprInfixReStr(self, ctx:IslaLanguageParser.SexprInfixReStrContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprNum.
    def enterSexprNum(self, ctx:IslaLanguageParser.SexprNumContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprNum.
    def exitSexprNum(self, ctx:IslaLanguageParser.SexprNumContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprXPathExpr.
    def enterSexprXPathExpr(self, ctx:IslaLanguageParser.SexprXPathExprContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprXPathExpr.
    def exitSexprXPathExpr(self, ctx:IslaLanguageParser.SexprXPathExprContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprOp.
    def enterSexprOp(self, ctx:IslaLanguageParser.SexprOpContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprOp.
    def exitSexprOp(self, ctx:IslaLanguageParser.SexprOpContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprInfixPlusMinus.
    def enterSexprInfixPlusMinus(self, ctx:IslaLanguageParser.SexprInfixPlusMinusContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprInfixPlusMinus.
    def exitSexprInfixPlusMinus(self, ctx:IslaLanguageParser.SexprInfixPlusMinusContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprTrue.
    def enterSexprTrue(self, ctx:IslaLanguageParser.SexprTrueContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprTrue.
    def exitSexprTrue(self, ctx:IslaLanguageParser.SexprTrueContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprFreeId.
    def enterSexprFreeId(self, ctx:IslaLanguageParser.SexprFreeIdContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprFreeId.
    def exitSexprFreeId(self, ctx:IslaLanguageParser.SexprFreeIdContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SepxrApp.
    def enterSepxrApp(self, ctx:IslaLanguageParser.SepxrAppContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SepxrApp.
    def exitSepxrApp(self, ctx:IslaLanguageParser.SepxrAppContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprInfixMulDiv.
    def enterSexprInfixMulDiv(self, ctx:IslaLanguageParser.SexprInfixMulDivContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprInfixMulDiv.
    def exitSexprInfixMulDiv(self, ctx:IslaLanguageParser.SexprInfixMulDivContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprId.
    def enterSexprId(self, ctx:IslaLanguageParser.SexprIdContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprId.
    def exitSexprId(self, ctx:IslaLanguageParser.SexprIdContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprPrefix.
    def enterSexprPrefix(self, ctx:IslaLanguageParser.SexprPrefixContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprPrefix.
    def exitSexprPrefix(self, ctx:IslaLanguageParser.SexprPrefixContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprStr.
    def enterSexprStr(self, ctx:IslaLanguageParser.SexprStrContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprStr.
    def exitSexprStr(self, ctx:IslaLanguageParser.SexprStrContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprInfixEq.
    def enterSexprInfixEq(self, ctx:IslaLanguageParser.SexprInfixEqContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprInfixEq.
    def exitSexprInfixEq(self, ctx:IslaLanguageParser.SexprInfixEqContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#SexprFalse.
    def enterSexprFalse(self, ctx:IslaLanguageParser.SexprFalseContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#SexprFalse.
    def exitSexprFalse(self, ctx:IslaLanguageParser.SexprFalseContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#predicateArg.
    def enterPredicateArg(self, ctx:IslaLanguageParser.PredicateArgContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#predicateArg.
    def exitPredicateArg(self, ctx:IslaLanguageParser.PredicateArgContext):
        pass


    # Enter a parse tree produced by IslaLanguageParser#smt_binary_op.
    def enterSmt_binary_op(self, ctx:IslaLanguageParser.Smt_binary_opContext):
        pass

    # Exit a parse tree produced by IslaLanguageParser#smt_binary_op.
    def exitSmt_binary_op(self, ctx:IslaLanguageParser.Smt_binary_opContext):
        pass



del IslaLanguageParser