grammar isla;

start: constDecl varDecls constraint;

constDecl: 'const' cid=ID ':' LT ntid=ID GT ';' ;

varDecls: 'vars' '{' varDecl + '}' ;
varDecl: ID (',' ID) *':' varType ';' ;
varType : LT ID GT | 'NUM' ;

constraint: 'constraint' '{' formula '}' ;

formula:
    ('forall' | 'exists') varId=ID '=' STRING 'in' inId=ID ':' formula # QfdFormulaMexpr
  | ('forall' | 'exists') varId=ID            'in' inId=ID ':' formula # QfdFormula
  | 'not' formula                                                      # Negation
  | formula 'and' formula                                              # Conjunction
  | formula 'or' formula                                               # Disjunction
  | 'num' ID ':' formula                                               # NumIntro
  | ID '(' predicateArg (',' predicateArg) * ')'                       # PredicateAtom
  | sexpr                                                              # SMTFormula
  | '(' formula ')'                                                    # ParFormula
  ;

sexpr:
    'true'                                                                       # SexprTrue
  | 'false'                                                                      # SexprFalse
  | INT                                                                          # SexprNum
  | ID                                                                           # SexprId
  | STRING                                                                       # SexprStr
  | '(' (ID | '=' | DIV | MUL | PLUS | MINUS | GEQ | LEQ | GT | LT)  sexpr + ')' # SepxrApp
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

// Have to exclude everything but [a-zA-Z_] for normal identifiers.
// '-' is OK for function symbols (sexpr) and nonterminal identifiers,
// all other special characters only OK for function symbols.
// We are more permissive here to avoid overlapping lexer rules.
fragment ID_LETTER : 'a'..'z'|'A'..'Z' | [_\-.] ;
fragment DIGIT : '0'..'9' ;

