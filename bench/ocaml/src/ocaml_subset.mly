/* The grammar of thys/OCaml_Parser.thy, production for production: the same
   nonterminals, the same levels instead of %left/%right/%prec, and the same
   actions on the types exported from the theory (Names.P).  Both parsers
   then run one grammar, and `make check` compares their trees.  Keep the two
   in sync: no %inline, no parameterised nonterminals, no precedences. */

%{
open Names
open P
%}

%token <Names.P.char list> LIDENT UIDENT INT FLOAT STRING CHAR
%token <Names.P.char list> INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3
%token LET REC AND IN FUN FUNCTION MATCH WITH TRY WHEN AS IF THEN ELSE
%token BEGIN END TYPE OF MUTABLE OPEN TRUE FALSE
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token SEMI COMMA BAR MINUSGREATER EQUAL MINUS STAR COLON COLONCOLON
%token COLONEQUAL DOT LESSMINUS UNDERSCORE QUOTE AMPERAMPER BARBAR BANG EOF

%start <Names.P.structure_item list> implementation

%type <Names.P.structure_item list> structure_items
%type <Names.P.structure_item> structure_item
%type <Names.P.rec_flag * Names.P.value_binding list> let_bindings
%type <Names.P.rec_flag> rec_flag
%type <Names.P.value_binding> let_binding
%type <Names.P.pattern list> params fun_params pattern_comma pattern_semi_list
%type <Names.P.type_declaration list> type_decls
%type <Names.P.type_declaration> type_decl
%type <Names.P.char list list> type_params type_vars
%type <Names.P.char list> type_var val_ident
%type <(Names.P.char list * Names.P.core_type list) list> constructors
%type <Names.P.char list * Names.P.core_type list> ctor_decl
%type <Names.P.core_type list> ctor_args star_types type_list
%type <(Names.P.mutable_flag * (Names.P.char list * Names.P.core_type)) list> label_decls
%type <Names.P.mutable_flag * (Names.P.char list * Names.P.core_type)> label_decl
%type <Names.P.mutable_flag> mutable_flag
%type <Names.P.core_type> core_type tuple_type app_type atomic_type
%type <Names.P.longident> type_longident mod_longident constr_longident val_longident
%type <Names.P.pattern> pattern pattern_or pattern_tuple pattern_cons pattern_app
%type <Names.P.pattern> simple_pattern simple_pattern_not_ident
%type <(Names.P.char list * Names.P.pattern) list> field_pats
%type <Names.P.char list * Names.P.pattern> field_pat
%type <Names.P.expression> seq_expr seq_expr_c else_tail else_tail_c expr expr_m assign_expr tuple_expr
%type <Names.P.expression> or_expr and_expr cmp_expr concat_expr cons_expr add_expr
%type <Names.P.expression> mul_expr unary_expr app_expr simple_expr simple_expr_nc atom
%type <Names.P.match_case list> match_cases case_list case_list_c
%type <Names.P.match_case> match_case match_case_c
%type <Names.P.expression list> expr_comma app_args expr_semi_list
%type <(Names.P.char list * Names.P.expression) list> record_fields
%type <Names.P.char list * Names.P.expression> record_field
%type <Names.P.pconstant> const

%%

/* structure */

implementation:
  s = structure_items EOF                     { List.rev s }

structure_items:
  /* empty */                                 { [] }
| s = structure_items i = structure_item       { i :: s }

structure_item:
  rb = let_bindings                           { let (r, bs) = rb in Pstr_value (r, List.rev bs) }
| TYPE ds = type_decls                        { Pstr_type (List.rev ds) }
| OPEN m = mod_longident                      { Pstr_open m }

let_bindings:
  LET r = rec_flag b = let_binding            { (r, [b]) }
| rb = let_bindings AND b = let_binding       { let (r, bs) = rb in (r, b :: bs) }

rec_flag:
  /* empty */                                 { Nonrecursive }
| REC                                         { Recursive }

let_binding:
  x = val_ident ps = params EQUAL e = seq_expr
                                              { Pvb (Ppat_var x, mk_fun (List.rev ps) e) }
| x = val_ident ps = params COLON t = core_type EQUAL e = seq_expr
                                              { Pvb (Ppat_var x, mk_fun (List.rev ps) (Pexp_constraint (e, t))) }
| p = simple_pattern_not_ident EQUAL e = seq_expr
                                              { Pvb (p, e) }
| ps = pattern_comma EQUAL e = seq_expr       { Pvb (Ppat_tuple (List.rev ps), e) }

params:
  /* empty */                                 { [] }
| ps = params p = simple_pattern              { p :: ps }

fun_params:
  p = simple_pattern                          { [p] }
| ps = fun_params p = simple_pattern          { p :: ps }

/* type declarations */

type_decls:
  d = type_decl                               { [d] }
| ds = type_decls AND d = type_decl           { d :: ds }

type_decl:
  ps = type_params n = LIDENT                 { Ptype (ps, n, Ptype_abstract, None) }
| ps = type_params n = LIDENT EQUAL t = core_type
                                              { Ptype (ps, n, Ptype_abstract, Some t) }
| ps = type_params n = LIDENT EQUAL cs = constructors
                                              { Ptype (ps, n, Ptype_variant (List.rev cs), None) }
| ps = type_params n = LIDENT EQUAL LBRACE ls = label_decls RBRACE
                                              { Ptype (ps, n, Ptype_record ls, None) }

type_params:
  /* empty */                                 { [] }
| v = type_var                                { [v] }
| LPAREN vs = type_vars RPAREN                { List.rev vs }

type_vars:
  v = type_var                                { [v] }
| vs = type_vars COMMA v = type_var           { v :: vs }

type_var:
  QUOTE x = LIDENT                            { x }

constructors:
  c = ctor_decl                               { [c] }
| BAR c = ctor_decl                           { [c] }
| cs = constructors BAR c = ctor_decl         { c :: cs }

ctor_decl:
  c = UIDENT                                  { (c, []) }
| c = UIDENT OF ts = ctor_args                { (c, List.rev ts) }

ctor_args:
  t = app_type                                { [t] }
| ts = ctor_args STAR t = app_type            { t :: ts }

label_decls:
  l = label_decl                              { [l] }
| l = label_decl SEMI                         { [l] }
| l = label_decl SEMI ls = label_decls        { l :: ls }

label_decl:
  m = mutable_flag x = LIDENT COLON t = core_type
                                              { (m, (x, t)) }

mutable_flag:
  /* empty */                                 { Immutable }
| MUTABLE                                     { Mutable }

/* types */

core_type:
  t = tuple_type                              { t }
| a = tuple_type MINUSGREATER b = core_type   { Ptyp_arrow (a, b) }

tuple_type:
  t = app_type                                { t }
| ts = star_types                             { Ptyp_tuple (List.rev ts) }

star_types:
  a = app_type STAR b = app_type              { [b; a] }
| ts = star_types STAR t = app_type           { t :: ts }

app_type:
  t = atomic_type                             { t }
| t = app_type c = type_longident             { Ptyp_constr (c, [t]) }
| LPAREN t = core_type COMMA ts = type_list RPAREN c = type_longident
                                              { Ptyp_constr (c, t :: List.rev ts) }

type_list:
  t = core_type                               { [t] }
| ts = type_list COMMA t = core_type          { t :: ts }

atomic_type:
  v = type_var                                { Ptyp_var v }
| c = type_longident                          { Ptyp_constr (c, []) }
| LPAREN t = core_type RPAREN                 { t }

type_longident:
  x = LIDENT                                  { Lident x }
| m = mod_longident DOT x = LIDENT            { Ldot (m, x) }

mod_longident:
  x = UIDENT                                  { Lident x }
| m = mod_longident DOT x = UIDENT            { Ldot (m, x) }

/* as in OCaml, true, false, () and [] are constructors */
constr_longident:
  c = mod_longident                           { c }
| TRUE                                        { Lident true_ }
| FALSE                                       { Lident false_ }
| LPAREN RPAREN                               { Lident unit }
| LBRACKET RBRACKET                           { Lident nil }

/* patterns */

pattern:
  p = pattern_or                              { p }
| p = pattern AS x = val_ident                { Ppat_alias (p, x) }

pattern_or:
  p = pattern_tuple                           { p }
| a = pattern_or BAR b = pattern_tuple        { Ppat_or (a, b) }

pattern_tuple:
  p = pattern_cons                            { p }
| ps = pattern_comma                          { Ppat_tuple (List.rev ps) }

pattern_comma:
  a = pattern_cons COMMA b = pattern_cons     { [b; a] }
| ps = pattern_comma COMMA p = pattern_cons   { p :: ps }

pattern_cons:
  p = pattern_app                             { p }
| a = pattern_app COLONCOLON b = pattern_cons { cons_pat a b }

pattern_app:
  p = simple_pattern                          { p }
| c = constr_longident p = simple_pattern     { Ppat_construct (c, Some p) }

simple_pattern:
  x = val_ident                               { Ppat_var x }
| p = simple_pattern_not_ident                { p }

simple_pattern_not_ident:
  UNDERSCORE                                  { Ppat_any }
| c = const                                   { Ppat_constant c }
| c = constr_longident                        { Ppat_construct (c, None) }
| LPAREN p = pattern RPAREN                   { p }
| LPAREN p = pattern COLON t = core_type RPAREN
                                              { Ppat_constraint (p, t) }
| LBRACKET ps = pattern_semi_list RBRACKET    { list_pat (List.rev ps) }
| LBRACE fs = field_pats RBRACE               { Ppat_record (List.rev fs, Closed) }
| LBRACE fs = field_pats SEMI UNDERSCORE RBRACE
                                              { Ppat_record (List.rev fs, Open) }

pattern_semi_list:
  p = pattern                                 { [p] }
| ps = pattern_semi_list SEMI p = pattern     { p :: ps }

field_pats:
  f = field_pat                               { [f] }
| fs = field_pats SEMI f = field_pat          { f :: fs }

field_pat:
  l = LIDENT EQUAL p = pattern                { (l, p) }
| l = LIDENT                                  { (l, Ppat_var l) }

/* expressions: a match, function or try takes every case after it, so one
   in a case that is not the last needs parentheses; _c is the sequence
   that does not end in one */

seq_expr:
  e = expr                                    { e }
| a = expr SEMI b = seq_expr                  { Pexp_sequence (a, b) }
| rb = let_bindings IN e = seq_expr           { let (r, bs) = rb in Pexp_let (r, List.rev bs, e) }
| FUN ps = fun_params MINUSGREATER e = seq_expr
                                              { Pexp_fun (List.rev ps, e) }
| MATCH e = seq_expr WITH cs = match_cases    { Pexp_match (e, List.rev cs) }
| FUNCTION cs = match_cases                   { Pexp_function (List.rev cs) }
| TRY e = seq_expr WITH cs = match_cases      { Pexp_try (e, List.rev cs) }
| IF c = seq_expr THEN a = expr_m ELSE b = else_tail
                                              { Pexp_ifthenelse (c, a, Some b) }

seq_expr_c:
  e = expr                                    { e }
| a = expr SEMI b = seq_expr_c                { Pexp_sequence (a, b) }
| rb = let_bindings IN e = seq_expr_c         { let (r, bs) = rb in Pexp_let (r, List.rev bs, e) }
| FUN ps = fun_params MINUSGREATER e = seq_expr_c
                                              { Pexp_fun (List.rev ps, e) }
| IF c = seq_expr THEN a = expr_m ELSE b = else_tail_c
                                              { Pexp_ifthenelse (c, a, Some b) }

/* an else-branch that takes the rest of the sequence: the if-then-else
   then stands where a sequence can */
else_tail:
  rb = let_bindings IN e = seq_expr           { let (r, bs) = rb in Pexp_let (r, List.rev bs, e) }
| FUN ps = fun_params MINUSGREATER e = seq_expr
                                              { Pexp_fun (List.rev ps, e) }
| MATCH e = seq_expr WITH cs = match_cases    { Pexp_match (e, List.rev cs) }
| FUNCTION cs = match_cases                   { Pexp_function (List.rev cs) }
| TRY e = seq_expr WITH cs = match_cases      { Pexp_try (e, List.rev cs) }
| IF c = seq_expr THEN a = expr_m ELSE b = else_tail
                                              { Pexp_ifthenelse (c, a, Some b) }

else_tail_c:
  rb = let_bindings IN e = seq_expr_c         { let (r, bs) = rb in Pexp_let (r, List.rev bs, e) }
| FUN ps = fun_params MINUSGREATER e = seq_expr_c
                                              { Pexp_fun (List.rev ps, e) }
| IF c = seq_expr THEN a = expr_m ELSE b = else_tail_c
                                              { Pexp_ifthenelse (c, a, Some b) }

match_cases:
  cs = case_list                              { cs }
| BAR cs = case_list                          { cs }

case_list:
  c = match_case                              { [c] }
| cs = case_list_c BAR c = match_case         { c :: cs }

case_list_c:
  c = match_case_c                            { [c] }
| cs = case_list_c BAR c = match_case_c       { c :: cs }

match_case:
  p = pattern MINUSGREATER e = seq_expr       { Pcase (p, None, e) }
| p = pattern WHEN g = seq_expr MINUSGREATER e = seq_expr
                                              { Pcase (p, Some g, e) }

match_case_c:
  p = pattern MINUSGREATER e = seq_expr_c     { Pcase (p, None, e) }
| p = pattern WHEN g = seq_expr MINUSGREATER e = seq_expr_c
                                              { Pcase (p, Some g, e) }

/* if-then without else: the then-branch of an if-then-else is _m, matched */

expr:
  e = assign_expr                             { e }
| IF c = seq_expr THEN a = expr               { Pexp_ifthenelse (c, a, None) }
| IF c = seq_expr THEN a = expr_m ELSE b = expr
                                              { Pexp_ifthenelse (c, a, Some b) }

expr_m:
  e = assign_expr                             { e }
| IF c = seq_expr THEN a = expr_m ELSE b = expr_m
                                              { Pexp_ifthenelse (c, a, Some b) }

assign_expr:
  e = tuple_expr                              { e }
| a = simple_expr_nc DOT l = LIDENT LESSMINUS b = assign_expr
                                              { Pexp_setfield (a, l, b) }
| a = tuple_expr COLONEQUAL b = assign_expr   { binop colonequal a b }

tuple_expr:
  e = or_expr                                 { e }
| es = expr_comma                             { Pexp_tuple (List.rev es) }

expr_comma:
  a = or_expr COMMA b = or_expr               { [b; a] }
| es = expr_comma COMMA e = or_expr           { e :: es }

or_expr:
  e = and_expr                                { e }
| a = and_expr BARBAR b = or_expr             { binop barbar a b }

and_expr:
  e = cmp_expr                                { e }
| a = cmp_expr AMPERAMPER b = and_expr        { binop amperamper a b }

cmp_expr:
  e = concat_expr                             { e }
| a = cmp_expr EQUAL b = concat_expr          { binop eq a b }
| a = cmp_expr o = INFIXOP0 b = concat_expr   { binop o a b }

concat_expr:
  e = cons_expr                               { e }
| a = cons_expr o = INFIXOP1 b = concat_expr  { binop o a b }

cons_expr:
  e = add_expr                                { e }
| a = add_expr COLONCOLON b = cons_expr       { cons_exp a b }

add_expr:
  e = mul_expr                                { e }
| a = add_expr MINUS b = mul_expr             { binop minus a b }
| a = add_expr o = INFIXOP2 b = mul_expr      { binop o a b }

mul_expr:
  e = unary_expr                              { e }
| a = mul_expr STAR b = unary_expr            { binop star a b }
| a = mul_expr o = INFIXOP3 b = unary_expr    { binop o a b }

unary_expr:
  e = app_expr                                { e }
| MINUS e = unary_expr                        { Pexp_apply (Pexp_ident (Lident neg), [e]) }

app_expr:
  e = simple_expr                             { e }
| f = simple_expr_nc xs = app_args            { Pexp_apply (f, List.rev xs) }
| c = constr_longident e = simple_expr        { Pexp_construct (c, Some e) }

app_args:
  e = simple_expr                             { [e] }
| es = app_args e = simple_expr               { e :: es }

simple_expr:
  e = simple_expr_nc                          { e }
| c = constr_longident                        { Pexp_construct (c, None) }

simple_expr_nc:
  e = atom                                    { e }
| e = simple_expr_nc DOT l = LIDENT           { Pexp_field (e, l) }

atom:
  x = val_longident                           { Pexp_ident x }
| c = const                                   { Pexp_constant c }
| LPAREN e = seq_expr RPAREN                  { e }
| LPAREN e = seq_expr COLON t = core_type RPAREN
                                              { Pexp_constraint (e, t) }
| BEGIN e = seq_expr END                      { e }
| LBRACKET es = expr_semi_list RBRACKET       { list_exp es }
| LBRACE fs = record_fields RBRACE            { Pexp_record (fs, None) }
| LBRACE e = simple_expr WITH fs = record_fields RBRACE
                                              { Pexp_record (fs, Some e) }
| BANG e = atom                               { Pexp_apply (Pexp_ident (Lident bang), [e]) }

expr_semi_list:
  e = expr                                    { [e] }
| e = expr SEMI                               { [e] }
| e = expr SEMI es = expr_semi_list           { e :: es }

record_fields:
  f = record_field                            { [f] }
| f = record_field SEMI                       { [f] }
| f = record_field SEMI fs = record_fields    { f :: fs }

record_field:
  l = LIDENT EQUAL e = expr                   { (l, e) }
| l = LIDENT                                  { (l, Pexp_ident (Lident l)) }

val_longident:
  x = val_ident                               { Lident x }
| m = mod_longident DOT x = LIDENT            { Ldot (m, x) }

val_ident:
  x = LIDENT                                  { x }

const:
  n = INT                                     { Pconst_integer n }
| x = FLOAT                                   { Pconst_float x }
| s = STRING                                  { Pconst_string s }
| c = CHAR                                    { Pconst_char c }
