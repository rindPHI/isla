grammar IslaLanguage;

start: constDecl? formula;

constDecl: 'const' ID ':' varType ';' ;

formula:
    'forall' (boundVarType=varType) (varId=ID) ?            'in' (inId=ID | inVarType=varType) ':' formula  # Forall
  | 'exists' (boundVarType=varType) (varId=ID) ?            'in' (inId=ID | inVarType=varType) ':' formula  # Exists
  | 'forall' (boundVarType=varType) (varId=ID) ? '=' STRING 'in' (inId=ID | inVarType=varType) ':' formula  # ForallMexpr
  | 'exists' (boundVarType=varType) (varId=ID) ? '=' STRING 'in' (inId=ID | inVarType=varType) ':' formula  # ExistsMexpr
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
    'true'          # SexprTrue
  | 'false'         # SexprFalse
  | INT             # SexprNum
  | ID              # SexprId
  | varType         # SexprFreeId
  | STRING          # SexprStr
  | ('re.+' | 're.*' | 're.++' | 'str.++' | '=' | DIV | MUL | PLUS | MINUS | GEQ | LEQ | GT | LT)
                    # SexprOp
  | '(' op=sexpr sexpr + ')' # SepxrApp
  ;

predicateArg: ID | varType | INT | STRING ;

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

fragment ID_LETTER : 'a'..'z'|'A'..'Z' | [_\-.^] ;
fragment DIGIT : '0'..'9' ;

