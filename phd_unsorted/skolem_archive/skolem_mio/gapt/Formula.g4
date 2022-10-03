grammar Formula;

formula : expression+ EOF;

expression
    : ID '(' term (',' term)* ')'                               # doPredicate
    | '(' expression ')'                                        # doParenthesis
    | '~' expression                                            # doNot
    | expression '=>' expression                                # doThen
    | expression '<=>' expression                               # doIFF
    | expression '<=' expression                                # doIF
    | expression '?' expression ':' expression                  # doITE
    | expression '&' expression                                 # doAnd
    | expression '|' expression                                 # doOr
    | expression '^' expression                                 # doXor
    | 'forall' VAR 'in' (range_expr | set_expr)  expression     # doExpandAnd
    | 'exists' VAR 'in' (range_expr | set_expr)  expression     # doExpandOr
    | TRUE                                                      # newTrueBoolean
    | FALSE                                                     # newFalseBoolean
    | VAR                                                       # newVariable
    | ID                                                        # newIdentifier
    ;

term
    : ID                                              # newTermID
    | VAR                                             # newTermVar
    | int_expr                                        # doIntExpr
    ;

int_expr
    : '(' int_expr ')'                                # parenthesizedIntExpression
    | '|' int_expr '|'                                # absValueExpression
    | '-' int_expr                                    # unaryMinusExpression
    | int_expr op=( '*' | '/' | '%' ) int_expr        # multiplicativeExpression
    | int_expr op=( '+' | '-' ) int_expr              # additiveExpression
    | VAR                                             # newIntVariable
    | NUMBER                                          # newInteger
    ;

range_expr 
    : '{' (int_expr '..' int_expr) '}' ;

set_expr 
    : '{' term (',' term)*  '}' ;

// Fragments
fragment DIGIT    : '0' .. '9';  
fragment UPPER    : 'A' .. 'Z';
fragment LOWER    : 'a' .. 'z';
fragment LETTER   : LOWER | UPPER;
fragment WORD     : LETTER | '_' | '$' | '#' | '.';
fragment ALPHANUM : WORD | DIGIT;  

// Tokens
ID              : LETTER ALPHANUM*;
VAR             : '_' LETTER ALPHANUM*;
NUMBER          : DIGIT+;
TRUE            : 'True';
FALSE           : 'False';

// Drops whitespaces and comments
WS              : [ \t\n\r]+ -> skip ;
COMMENTS        : ('/*' .*? '*/' | '//' ~'\n'* '\n' ) -> skip;

