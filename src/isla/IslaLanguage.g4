grammar IslaLanguage;

start: constDecl? formula;

constDecl: 'const' ID ':' VAR_TYPE ';' ;

formula:
    'forall' (boundVarType=VAR_TYPE) (varId=ID) ?            ('in' (inId=ID | inVarType=VAR_TYPE)) ? ':' formula  # Forall
  | 'exists' (boundVarType=VAR_TYPE) (varId=ID) ?            ('in' (inId=ID | inVarType=VAR_TYPE)) ? ':' formula  # Exists
  | 'forall' (boundVarType=VAR_TYPE) (varId=ID) ? '=' STRING ('in' (inId=ID | inVarType=VAR_TYPE)) ? ':' formula  # ForallMexpr
  | 'exists' (boundVarType=VAR_TYPE) (varId=ID) ? '=' STRING ('in' (inId=ID | inVarType=VAR_TYPE)) ? ':' formula  # ExistsMexpr
  | 'exists' 'int' ID ':' formula                                  # ExistsInt
  | 'forall' 'int' ID ':' formula                                  # ForallInt
  | 'not' formula                                                  # Negation
  | formula 'and' formula                                          # Conjunction
  | formula 'or' formula                                           # Disjunction
  | formula 'xor' formula                                          # ExclusiveOr
  | formula 'implies' formula                                      # Implication
  | formula 'iff' formula                                          # Equivalence
  | ID '(' predicateArg (',' predicateArg) * ')'                   # PredicateAtom
  | sexpr                                                          # SMTFormula
  | '(' formula ')'                                                # ParFormula
  ;

sexpr:
    'true'          # SexprTrue
  | 'false'         # SexprFalse
  | INT             # SexprNum
  | ID              # SexprId
  | XPATHEXPR       # SexprXPathExpr
  | VAR_TYPE         # SexprFreeId
  | STRING          # SexprStr
  | ('re.+' | 're.*' | 're.++' | 'str.++' | '=' | DIV | MUL | PLUS | MINUS | GEQ | LEQ | GT | LT)
                    # SexprOp
  | '(' op=sexpr sexpr + ')' # SepxrApp
  ;

predicateArg: ID | VAR_TYPE | INT | STRING ;

XPATHEXPR: (ID | VAR_TYPE) XPATHSEGMENT + ;

fragment XPATHSEGMENT:
      DOT VAR_TYPE
    | DOT VAR_TYPE BROP INT BRCL
    | TWODOTS VAR_TYPE
    ;

VAR_TYPE : LT ID GT ;

STRING: '"' (ESC|.) *? '"';
ID: ID_LETTER (ID_LETTER | DIGIT) * ;
INT : DIGIT+ ;
ESC : '\\' [btnr"\\] ;

DOT : '.' ;
TWODOTS : '..' ;
BROP : '[' ;
BRCL : ']' ;

DIV: '/' ;
MUL: '*' ;
PLUS: '+' ;
MINUS: '-' ;
GEQ: '>=' ;
LEQ: '<=' ;
GT: '>' ;
LT: '<' ;

WS : [ \t\n\r]+ -> skip ;
LINE_COMMENT : '#' .*? '\n' -> skip ;

fragment ID_LETTER : 'a'..'z'|'A'..'Z' | [_\-.^] ;
fragment DIGIT : '0'..'9' ;

