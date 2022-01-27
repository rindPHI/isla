grammar isla;

start: constDecl varDecls constraint;

constDecl: 'const' cid=ID ':' LT ntid=ID GT ';' ;

varDecls: 'vars' '{' varDecl + '}' ;
varDecl: ID (',' ID) *':' varType ';' ;
varType : LT ID GT | 'NUM' ;

constraint: 'constraint' '{' formula '}' ;

formula:
    'forall' varId=ID            'in' inId=ID ':' formula  # Forall
  | 'exists' varId=ID            'in' inId=ID ':' formula  # Exists
  | 'forall' varId=ID '=' STRING 'in' inId=ID ':' formula  # ForallMexpr
  | 'exists' varId=ID '=' STRING 'in' inId=ID ':' formula  # ExistsMexpr
  | 'exists' 'int' ID ':' formula                          # ExistsInt
  | 'forall' 'int' ID ':' formula                          # ForallInt
  | 'not' formula                                          # Negation
  | formula 'and' formula                                  # Conjunction
  | formula 'or' formula                                   # Disjunction
  | formula 'xor' formula                                  # ExclusiveOr
  | formula 'implies' formula                              # Implication
  | formula 'iff' formula                                  # Equivalence
  | ID '(' predicateArg (',' predicateArg) * ')'           # PredicateAtom
  | sexpr                                                  # SMTFormula
  | '(' formula ')'                                        # ParFormula
  ;

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

