grammar bnf;

bnf_grammar: derivation_rule + ;

derivation_rule: NONTERMINAL '::=' alternative ( '|' alternative ) * ';' ;

alternative: ( STRING | NONTERMINAL ) + ;

NONTERMINAL: '<' ~[<>] + '>' ;

STRING: '"' (ESC|.) *? '"';
ESC : '\\' [btnr"\\] ;

WS : [ \t\n\r]+ -> skip ;
LINE_COMMENT : '#' .*? '\n' -> skip ;
