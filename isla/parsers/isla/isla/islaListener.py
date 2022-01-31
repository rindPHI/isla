# Generated from isla.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .islaParser import islaParser
else:
    from islaParser import islaParser

# This class defines a complete listener for a parse tree produced by islaParser.
class islaListener(ParseTreeListener):

    # Enter a parse tree produced by islaParser#start.
    def enterStart(self, ctx:islaParser.StartContext):
        pass

    # Exit a parse tree produced by islaParser#start.
    def exitStart(self, ctx:islaParser.StartContext):
        pass


    # Enter a parse tree produced by islaParser#constDecl.
    def enterConstDecl(self, ctx:islaParser.ConstDeclContext):
        pass

    # Exit a parse tree produced by islaParser#constDecl.
    def exitConstDecl(self, ctx:islaParser.ConstDeclContext):
        pass


    # Enter a parse tree produced by islaParser#ExistsMexpr.
    def enterExistsMexpr(self, ctx:islaParser.ExistsMexprContext):
        pass

    # Exit a parse tree produced by islaParser#ExistsMexpr.
    def exitExistsMexpr(self, ctx:islaParser.ExistsMexprContext):
        pass


    # Enter a parse tree produced by islaParser#Negation.
    def enterNegation(self, ctx:islaParser.NegationContext):
        pass

    # Exit a parse tree produced by islaParser#Negation.
    def exitNegation(self, ctx:islaParser.NegationContext):
        pass


    # Enter a parse tree produced by islaParser#Implication.
    def enterImplication(self, ctx:islaParser.ImplicationContext):
        pass

    # Exit a parse tree produced by islaParser#Implication.
    def exitImplication(self, ctx:islaParser.ImplicationContext):
        pass


    # Enter a parse tree produced by islaParser#ForallMexpr.
    def enterForallMexpr(self, ctx:islaParser.ForallMexprContext):
        pass

    # Exit a parse tree produced by islaParser#ForallMexpr.
    def exitForallMexpr(self, ctx:islaParser.ForallMexprContext):
        pass


    # Enter a parse tree produced by islaParser#ExistsInt.
    def enterExistsInt(self, ctx:islaParser.ExistsIntContext):
        pass

    # Exit a parse tree produced by islaParser#ExistsInt.
    def exitExistsInt(self, ctx:islaParser.ExistsIntContext):
        pass


    # Enter a parse tree produced by islaParser#Disjunction.
    def enterDisjunction(self, ctx:islaParser.DisjunctionContext):
        pass

    # Exit a parse tree produced by islaParser#Disjunction.
    def exitDisjunction(self, ctx:islaParser.DisjunctionContext):
        pass


    # Enter a parse tree produced by islaParser#PredicateAtom.
    def enterPredicateAtom(self, ctx:islaParser.PredicateAtomContext):
        pass

    # Exit a parse tree produced by islaParser#PredicateAtom.
    def exitPredicateAtom(self, ctx:islaParser.PredicateAtomContext):
        pass


    # Enter a parse tree produced by islaParser#SMTFormula.
    def enterSMTFormula(self, ctx:islaParser.SMTFormulaContext):
        pass

    # Exit a parse tree produced by islaParser#SMTFormula.
    def exitSMTFormula(self, ctx:islaParser.SMTFormulaContext):
        pass


    # Enter a parse tree produced by islaParser#Equivalence.
    def enterEquivalence(self, ctx:islaParser.EquivalenceContext):
        pass

    # Exit a parse tree produced by islaParser#Equivalence.
    def exitEquivalence(self, ctx:islaParser.EquivalenceContext):
        pass


    # Enter a parse tree produced by islaParser#Exists.
    def enterExists(self, ctx:islaParser.ExistsContext):
        pass

    # Exit a parse tree produced by islaParser#Exists.
    def exitExists(self, ctx:islaParser.ExistsContext):
        pass


    # Enter a parse tree produced by islaParser#Conjunction.
    def enterConjunction(self, ctx:islaParser.ConjunctionContext):
        pass

    # Exit a parse tree produced by islaParser#Conjunction.
    def exitConjunction(self, ctx:islaParser.ConjunctionContext):
        pass


    # Enter a parse tree produced by islaParser#ParFormula.
    def enterParFormula(self, ctx:islaParser.ParFormulaContext):
        pass

    # Exit a parse tree produced by islaParser#ParFormula.
    def exitParFormula(self, ctx:islaParser.ParFormulaContext):
        pass


    # Enter a parse tree produced by islaParser#Forall.
    def enterForall(self, ctx:islaParser.ForallContext):
        pass

    # Exit a parse tree produced by islaParser#Forall.
    def exitForall(self, ctx:islaParser.ForallContext):
        pass


    # Enter a parse tree produced by islaParser#ExclusiveOr.
    def enterExclusiveOr(self, ctx:islaParser.ExclusiveOrContext):
        pass

    # Exit a parse tree produced by islaParser#ExclusiveOr.
    def exitExclusiveOr(self, ctx:islaParser.ExclusiveOrContext):
        pass


    # Enter a parse tree produced by islaParser#ForallInt.
    def enterForallInt(self, ctx:islaParser.ForallIntContext):
        pass

    # Exit a parse tree produced by islaParser#ForallInt.
    def exitForallInt(self, ctx:islaParser.ForallIntContext):
        pass


    # Enter a parse tree produced by islaParser#varType.
    def enterVarType(self, ctx:islaParser.VarTypeContext):
        pass

    # Exit a parse tree produced by islaParser#varType.
    def exitVarType(self, ctx:islaParser.VarTypeContext):
        pass


    # Enter a parse tree produced by islaParser#SexprTrue.
    def enterSexprTrue(self, ctx:islaParser.SexprTrueContext):
        pass

    # Exit a parse tree produced by islaParser#SexprTrue.
    def exitSexprTrue(self, ctx:islaParser.SexprTrueContext):
        pass


    # Enter a parse tree produced by islaParser#SexprFalse.
    def enterSexprFalse(self, ctx:islaParser.SexprFalseContext):
        pass

    # Exit a parse tree produced by islaParser#SexprFalse.
    def exitSexprFalse(self, ctx:islaParser.SexprFalseContext):
        pass


    # Enter a parse tree produced by islaParser#SexprNum.
    def enterSexprNum(self, ctx:islaParser.SexprNumContext):
        pass

    # Exit a parse tree produced by islaParser#SexprNum.
    def exitSexprNum(self, ctx:islaParser.SexprNumContext):
        pass


    # Enter a parse tree produced by islaParser#SexprId.
    def enterSexprId(self, ctx:islaParser.SexprIdContext):
        pass

    # Exit a parse tree produced by islaParser#SexprId.
    def exitSexprId(self, ctx:islaParser.SexprIdContext):
        pass


    # Enter a parse tree produced by islaParser#SexprStr.
    def enterSexprStr(self, ctx:islaParser.SexprStrContext):
        pass

    # Exit a parse tree produced by islaParser#SexprStr.
    def exitSexprStr(self, ctx:islaParser.SexprStrContext):
        pass


    # Enter a parse tree produced by islaParser#SepxrApp.
    def enterSepxrApp(self, ctx:islaParser.SepxrAppContext):
        pass

    # Exit a parse tree produced by islaParser#SepxrApp.
    def exitSepxrApp(self, ctx:islaParser.SepxrAppContext):
        pass


    # Enter a parse tree produced by islaParser#predicateArg.
    def enterPredicateArg(self, ctx:islaParser.PredicateArgContext):
        pass

    # Exit a parse tree produced by islaParser#predicateArg.
    def exitPredicateArg(self, ctx:islaParser.PredicateArgContext):
        pass


