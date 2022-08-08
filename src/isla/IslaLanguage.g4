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
  | formula AND formula                                          # Conjunction
  | formula OR formula                                           # Disjunction
  | formula XOR formula                                          # ExclusiveOr
  | formula IMPLIES_ISLA formula                                      # Implication
  | formula 'iff' formula                                          # Equivalence
  | ID '(' predicateArg (',' predicateArg) * ')'                   # PredicateAtom
  | sexpr                                                          # SMTFormula
  | '(' formula ')'                                                # ParFormula
  ;

sexpr:
    'true'                                     # SexprTrue
  | 'false'                                    # SexprFalse
  | INT                                        # SexprNum
  | ID                                         # SexprId
  | XPATHEXPR                                  # SexprXPathExpr
  | VAR_TYPE                                   # SexprFreeId
  | STRING                                     # SexprStr
  | (SMT_NONBINARY_OP | smt_binary_op)         # SexprOp
  | op=SMT_NONBINARY_OP '(' ( sexpr ( ',' sexpr ) * ) ? ')' # SexprPrefix
  | sexpr op=SMT_INFIX_RE_STR sexpr            # SexprInfixReStr
  | sexpr op=(PLUS | MINUS) sexpr              # SexprInfixPlusMinus
  | sexpr op=(MUL | DIV | MOD) sexpr           # SexprInfixMulDiv
  | sexpr op=('=' | GEQ | LEQ | GT | LT) sexpr # SexprInfixEq
  | '(' sexpr ')'                              # SepxrParen
  | '(' op=sexpr sexpr + ')'                   # SepxrApp
  ;

predicateArg: ID | VAR_TYPE | INT | STRING | XPATHEXPR ;

smt_binary_op:
  '=' | GEQ | LEQ | GT | LT | MUL | DIV | MOD | PLUS | MINUS | SMT_INFIX_RE_STR | AND | OR | IMPLIES_SMT | XOR;

SMT_INFIX_RE_STR:
      're.++'
    | 'str.++'
    | 'str.<='
    ;

SMT_NONBINARY_OP:
      ABS
    | 're.+'
    | 're.*'
    | 'str.len'
    | 'str.in_re'
    | 'str.to_re'
    | 're.none'
    | 're.all'
    | 're.allchar'
    | 'str.at'
    | 'str.substr'
    | 'str.prefixof'
    | 'str.suffixof'
    | 'str.contains'
    | 'str.indexof'
    | 'str.replace'
    | 'str.replace_all'
    | 'str.replace_re'
    | 'str.replace_re_all'
    | 're.comp'
    | 're.diff'
    | 're.opt'
    | 're.range'
    | 're.loop'
    | 'str.is_digit'
    | 'str.to_code'
    | 'str.from_code'
    | 'str.to.int'
    | 'str.from_int'
    ;

XPATHEXPR: (ID | VAR_TYPE) XPATHSEGMENT + ;

fragment XPATHSEGMENT:
      DOT VAR_TYPE
    | DOT VAR_TYPE BROP INT BRCL
    | TWODOTS VAR_TYPE
    ;

VAR_TYPE : LT ID GT ;

AND: 'and' ;
OR: 'or' ;
NOT: 'not' ;

XOR: 'xor' ;
IMPLIES_SMT: '=>' ;
IMPLIES_ISLA: 'implies' ;

DIV: 'div' ;
MOD: 'mod' ;
ABS: 'abs' ;

STRING: '"' (ESC|.) *? '"';
ID: ID_LETTER (ID_LETTER | DIGIT) * ;
INT : DIGIT+ ;
ESC : '\\' [btnr"\\] ;

DOT : '.' ;
TWODOTS : '..' ;
BROP : '[' ;
BRCL : ']' ;

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

