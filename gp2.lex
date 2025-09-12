type pos = (int * int);
type arg = int;

open Tokens;

type lexresult  = (svalue, pos) token

val linestart_pos = ref 0;

fun mkTok f text pos line =
  (f text, ((pos - !linestart_pos) - String.size text, line),
            (pos - !linestart_pos, line));

fun mkMtTok text pos line =
  (((pos - !linestart_pos) - String.size text, line),
    (pos - !linestart_pos, line));

fun eof () = EOF ((~1,~1), (~1,~1));

fun I x = x;

exception LexicalError of string * int * int;

fun lexError msg text pos line =
  (raise (LexicalError (text, pos, line)))

%%
%full
%header (functor GP2LexFun(structure Tokens : GP2_TOKENS));
%count

newline=(\010 | \013 | "\013\010");
qstring = "\"" [^ `\"`]* "\"";
num = [0-9]+;
dnum = [-+]?[0-9]*\.[0-9]+([eE][-+]?[0-9]+)?;
ws = [\ \t];
procid = [A-Z][a-zA-Z0-9_]{0,63};
id = [a-z][a-zA-Z0-9_]{0,63};
%%


{newline} => (((linestart_pos := yypos); continue ()));
{ws} => (continue ());
"//".* => (continue());

"Main" => (MAIN (mkMtTok yytext yypos (!yylineno)));

"if" => (IF (mkMtTok yytext yypos (!yylineno)));
"try" => (TRY (mkMtTok yytext yypos (!yylineno)));
"then" => (THENN (mkMtTok yytext yypos (!yylineno)));
"else" => (ELSE (mkMtTok yytext yypos (!yylineno)));
"skip" => (SKIP (mkMtTok yytext yypos (!yylineno)));
"fail" => (FAIL (mkMtTok yytext yypos (!yylineno)));
"break" => (BREAK (mkMtTok yytext yypos (!yylineno)));
"where" => (WHERE (mkMtTok yytext yypos (!yylineno)));
"and" => (AND (mkMtTok yytext yypos (!yylineno)));
"or" => (OR (mkMtTok yytext yypos (!yylineno)));
"not" => (NOT (mkMtTok yytext yypos (!yylineno)));
"edge" => (EDGE (mkMtTok yytext yypos (!yylineno)));
"indeg" => (INDEG (mkMtTok yytext yypos (!yylineno)));
"outdeg" => (OUTDEG (mkMtTok yytext yypos (!yylineno)));
"interface" => (INTERFACE (mkMtTok yytext yypos (!yylineno)));
"empty" => (EMPTY (mkMtTok yytext yypos (!yylineno)));
"length" => (LENGTH (mkMtTok yytext yypos (!yylineno)));

"red" =>  (RED (mkMtTok yytext yypos (!yylineno)));
"green" => (GREEN (mkMtTok yytext yypos (!yylineno)));
"blue" => (BLUE (mkMtTok yytext yypos (!yylineno)));
"grey" => (GREY (mkMtTok yytext yypos (!yylineno)));
"dashed" => (DASHED (mkMtTok yytext yypos (!yylineno)));
"any" => (ANY (mkMtTok yytext yypos (!yylineno)));

"int" => (INT (mkMtTok yytext yypos (!yylineno)));
"char" => (CHARACTER (mkMtTok yytext yypos (!yylineno)));
"string" => (STRING (mkMtTok yytext yypos (!yylineno)));
"atom" => (ATOM (mkMtTok yytext yypos (!yylineno)));
"list" => (LIST (mkMtTok yytext yypos (!yylineno)));

"(" => (LPAREN (mkMtTok yytext yypos (!yylineno)));
")" => (RPAREN (mkMtTok yytext yypos (!yylineno)));
"{" => (LCURLY (mkMtTok yytext yypos (!yylineno)));
"}" => (RCURLY (mkMtTok yytext yypos (!yylineno)));
"[" => (LBRACKET (mkMtTok yytext yypos (!yylineno)));
"]" => (RBRACKET (mkMtTok yytext yypos (!yylineno)));
"|" => (PIPE (mkMtTok yytext yypos (!yylineno)));
"," => (COMMA (mkMtTok yytext yypos (!yylineno)));
";" => (SEMICOLON (mkMtTok yytext yypos (!yylineno)));
"!" => (EXCLAMATION (mkMtTok yytext yypos (!yylineno)));
"." => (DOT (mkMtTok yytext yypos (!yylineno)));
":" => (COLON (mkMtTok yytext yypos (!yylineno)));
"+" => (ADD (mkMtTok yytext yypos (!yylineno)));
"-" => (SUB (mkMtTok yytext yypos (!yylineno)));
"*" => (MULT (mkMtTok yytext yypos (!yylineno)));
"/" => (DIV (mkMtTok yytext yypos (!yylineno)));
">" => (RANGLE (mkMtTok yytext yypos (!yylineno)));
"<" => (LANGLE (mkMtTok yytext yypos (!yylineno)));
"=" => (EQ (mkMtTok yytext yypos (!yylineno)));
"#" => (HASH (mkMtTok yytext yypos (!yylineno)));

"=>" => (ARROW (mkMtTok yytext yypos (!yylineno)));
"(R)" => (ROOT (mkMtTok yytext yypos (!yylineno)));
"(B)" => (BIDIRECTIONAL (mkMtTok yytext yypos (!yylineno)));
"!=" => (NEQ (mkMtTok yytext yypos (!yylineno)));
">=" => (GTEQ (mkMtTok yytext yypos (!yylineno)));
"<=" => (LTEQ (mkMtTok yytext yypos (!yylineno)));

{procid} => (PROCID (mkTok I yytext yypos (!yylineno)));
{id} => (ID (mkTok I yytext yypos (!yylineno)));
{num} => (NUM (mkTok (fn s => (valOf(Int.fromString s))) yytext yypos (!yylineno)));
{qstring} => (STR (mkTok (fn s => String.substring(s,1,String.size s -2)) yytext yypos (!yylineno)));
{dnum} => (DNUM (mkTok (fn s => (valOf(Real.fromString s))) yytext yypos (!yylineno)));

. =>
  ( lexError "ill-formed token" yytext yypos (!yylineno) );
