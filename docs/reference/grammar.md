# Grammar

This EBNF describes the **surface syntax** (S-expressions) produced by the parser.

```ebnf
program ::= expression*

expression ::= atom
             | list
             | braced_list
             | quote
             | quasiquote
             | unquote
             | unquote_splicing
             | index_expr

atom ::= INTEGER | STRING | SYMBOL | HOLE

list ::= '(' expression* ')'

braced_list ::= '{' expression* '}'

quote ::= "'" expression

quasiquote ::= "`" expression

unquote ::= "," expression

unquote_splicing ::= ",@" expression

index_expr ::= expression '[' expression ']' 
/* Parsed as (kind: Index, expr, index) */

INTEGER ::= [0-9]+
STRING  ::= '"' (CHARS | ESCAPE)* '"'
HOLE    ::= "_"
SYMBOL  ::= [^ \t\n\r()\[\]{}"',`]+  /* excluding HOLE */
```
