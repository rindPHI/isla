grammar IslaLanguage;

start: constDecl? formula;

constDecl: 'const' ID ':' varType ';' ;

formula:
    'forall' varType varId=ID            'in' inId=ID ':' formula  # Forall
  | 'exists' varType varId=ID            'in' inId=ID ':' formula  # Exists
  | 'forall' varType varId=ID '=' STRING 'in' inId=ID ':' formula  # ForallMexpr
  | 'exists' varType varId=ID '=' STRING 'in' inId=ID ':' formula  # ExistsMexpr
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

varType : LT ID GT ;

sexpr:
    'true'                                                                          # SexprTrue
  | 'false'                                                                         # SexprFalse
  | INT                                                                             # SexprNum
  | ID                                                                              # SexprId
  | STRING                                                                          # SexprStr
  | '(' op=(ID | '=' | DIV | MUL | PLUS | MINUS | GEQ | LEQ | GT | LT)  sexpr + ')' # SepxrApp
  ;

predicateArg: ID | INT | STRING ;

STRING: '"' (ESC|.) *? '"';
ID: ID_LETTER (ID_LETTER | DIGIT) * ;
INT : DIGIT+ ;
ESC : '\\' [btnr"\\] ;

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

fragment ID_LETTER : 'a'..'z'|'A'..'Z' | [_\-.] ;
fragment DIGIT : '0'..'9' ;

