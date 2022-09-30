// Copyright © 2022 CISPA Helmholtz Center for Information Security.
// Author: Dominic Steinhöfel
//
// This file is part of ISLa.
//
// ISLa is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// ISLa is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

lexer grammar MexprLexer;

BRAOP : '{' -> pushMode(VAR_DECL) ;

OPTOP : '[' -> pushMode(OPTIONAL) ;

TEXT : (~ [{[]) + ;

NL : '\n' + -> skip ;

mode VAR_DECL;
BRACL : '}' -> popMode ;
ID: ID_LETTER (ID_LETTER | DIGIT) * ;
fragment ID_LETTER : 'a'..'z'|'A'..'Z' | [_\-.] ;
fragment DIGIT : '0'..'9' ;
GT: '>' ;
LT: '<' ;
WS : [ \t\n\r]+ -> skip ;

mode OPTIONAL;
OPTCL : ']' -> popMode ;
OPTTXT : (~ ']') + ;