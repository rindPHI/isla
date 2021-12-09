parser grammar MexprParser;

options { tokenVocab=MexprLexer; }

matchExpr: matchExprElement + ;

matchExprElement:
    BRAOP ID BRACL     # MatchExprVar
  | OPTOP OPTTXT OPTCL # MatchExprOptional
  | TEXT               # MatchExprChars
  ;