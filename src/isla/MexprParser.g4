parser grammar MexprParser;

options { tokenVocab=MexprLexer; }

matchExpr: matchExprElement + ;

matchExprElement:
    BRAOP varType ID BRACL # MatchExprVar
  | OPTOP OPTTXT OPTCL     # MatchExprOptional
  | TEXT                   # MatchExprChars
  ;

varType : LT ID GT ;
