theory OCaml_Parser
  imports LR_Parser.LR_Parser
begin

section \<open>A subset of the OCaml grammar\<close>

text \<open>A subset of OCaml 5's \<^verbatim>\<open>parsing/parser.mly\<close>, it has:
  \<^item> top-level \<open>let\<close>, \<open>type\<close> (variants, records, aliases, type parameters) and
    \<open>open\<close>;
  \<^item> \<open>let\<close>-\<open>in\<close>, \<open>fun\<close>, \<open>function\<close>, \<open>match\<close>, \<open>try\<close>, \<open>when\<close> guards, \<open>if\<close> with
    and without \<open>else\<close>, \<open>;\<close>, tuples, lists, records with \<open>with\<close>, field access
    and assignment, \<open>:=\<close> and \<open>!\<close>, type constraints, module paths;
  \<^item> the operators by OCaml's precedence levels, from \<open>||\<close> to unary \<open>-\<close>;
  \<^item> patterns with \<open>as\<close>, \<open>|\<close>, tuples, \<open>::\<close>, constructors, lists, records and
    constraints.

  The harness's Menhir grammar \<^file>\<open>../src/ocaml_subset.mly\<close> has the same
  productions and actions. Menhir finds no conflicts in it, also with
  \<^verbatim>\<open>--lalr\<close>. Nonterminals keep the names they have in \<^verbatim>\<open>parser.mly\<close>
  where they mean the same thing.

  The \<open>grammar\<close> command has no \<open>%left\<close>/\<open>%prec\<close>. Where Menhir resolves a
  conflict by precedence, this grammar has one nonterminal per level or a
  smaller language:
  \<^item> The binary operators are levels, loosest first: \<open>||\<close> and \<open>&&\<close> (right),
    \<open>=\<close> and \<open>INFIXOP0\<close> (left), \<open>INFIXOP1\<close> (right), \<open>::\<close> (right), \<open>-\<close> and
    \<open>INFIXOP2\<close> (left), \<open>*\<close> and \<open>INFIXOP3\<close> (left), then unary \<open>-\<close>. The lexer
    classes \<open><\<close> and \<open>>\<close> as \<open>INFIXOP0\<close> and \<open>+\<close> as \<open>INFIXOP2\<close>.
  \<^item> \<open>let\<close>, \<open>fun\<close>, \<open>match\<close>, \<open>function\<close> and \<open>try\<close> stand only where a sequence
    can: at the end of a \<open>;\<close> chain, a binding, a branch of a case, or in
    parentheses. A \<open>match\<close>, \<open>function\<close> or \<open>try\<close> takes all the cases after
    it, so it can end only the last case of an enclosing one. The suffix
    \<open>_c\<close> marks a sequence that does not end in one.
  \<^item> \<open>if\<close> stands where a sequence's items can. The then-branch of an
    \<open>if\<close>-\<open>then\<close>-\<open>else\<close> is \<open>expr_m\<close>, where every \<open>if\<close> has an \<open>else\<close>, so an \<open>else\<close>
    belongs to the nearest \<open>if\<close>. An else-branch can also be one of the
    forms that take the rest of the sequence (\<open>else_tail\<close>); that
    \<open>if\<close>-\<open>then\<close>-\<open>else\<close> stands where a sequence can.
  \<^item> A constructor applied to an argument cannot be applied further (OCaml
    rejects that at typing), and the head of an application is not a
    constructor.
  \<^item> A let-binding binds a name, with parameters and a result type, or a
    pattern that is not a name: a simple one, or a tuple.\<close>

subsection \<open>Tokens\<close>

text \<open>The constructors are the Menhir token names with a \<open>T_\<close> prefix (\<open>INT\<close>,
  \<open>OF\<close>, \<open>THE\<close>, \<dots> are HOL syntax). A token's payload is its text: an
  identifier, a constant (a string's or a character's contents without the
  quotes, as lexed) or an operator.\<close>

datatype ocaml_tok
  = T_LET | T_REC | T_AND | T_IN | T_FUN | T_FUNCTION | T_MATCH | T_WITH | T_TRY
  | T_WHEN | T_AS | T_IF | T_THEN | T_ELSE | T_BEGIN | T_END | T_TYPE | T_OF
  | T_MUTABLE | T_OPEN | T_TRUE | T_FALSE
  | T_LPAREN | T_RPAREN | T_LBRACKET | T_RBRACKET | T_LBRACE | T_RBRACE
  | T_SEMI | T_COMMA | T_BAR | T_MINUSGREATER | T_EQUAL | T_MINUS | T_STAR
  | T_COLON | T_COLONCOLON | T_COLONEQUAL | T_DOT | T_LESSMINUS | T_UNDERSCORE
  | T_QUOTE | T_AMPERAMPER | T_BARBAR | T_BANG
  | T_INFIXOP0 | T_INFIXOP1 | T_INFIXOP2 | T_INFIXOP3
  | T_LIDENT | T_UIDENT | T_INT | T_FLOAT | T_STRING | T_CHAR
  | T_EOF

type_synonym ocaml_token = \<open>(ocaml_tok, char) token\<close>

definition tok_text :: \<open>ocaml_token \<Rightarrow> string\<close> where
  \<open>tok_text t = s_txt (span t)\<close>

subsection \<open>Parsetree\<close>

text \<open>The fragment of OCaml's \<^verbatim>\<open>Parsetree\<close> the subset builds, with OCaml's
  constructor names. As in OCaml, an operator is the application of an
  identifier, a list is built from \<open>::\<close> and \<open>[]\<close>, and \<open>true\<close>, \<open>false\<close>
  and \<open>()\<close> are constructors. A function binding \<open>let f x = e\<close> binds \<open>f\<close> to
  \<open>fun x -> e\<close>.\<close>

datatype longident = Lident string | Ldot longident string

datatype pconstant =
  Pconst_integer string | Pconst_char string | Pconst_string string | Pconst_float string

datatype rec_flag = Nonrecursive | Recursive

datatype mutable_flag = Immutable | Mutable

datatype closed_flag = Closed | Open

datatype core_type
  = Ptyp_var string
  | Ptyp_arrow core_type core_type
  | Ptyp_tuple \<open>core_type list\<close>
  | Ptyp_constr longident \<open>core_type list\<close>

datatype pattern
  = Ppat_any
  | Ppat_var string
  | Ppat_alias pattern string
  | Ppat_constant pconstant
  | Ppat_tuple \<open>pattern list\<close>
  | Ppat_construct longident \<open>pattern option\<close>
  | Ppat_record \<open>(string \<times> pattern) list\<close> closed_flag
  | Ppat_or pattern pattern
  | Ppat_constraint pattern core_type

datatype expression
  = Pexp_ident longident
  | Pexp_constant pconstant
  | Pexp_let rec_flag \<open>value_binding list\<close> expression
  | Pexp_function \<open>match_case list\<close>
  | Pexp_fun \<open>pattern list\<close> expression
  | Pexp_apply expression \<open>expression list\<close>
  | Pexp_match expression \<open>match_case list\<close>
  | Pexp_try expression \<open>match_case list\<close>
  | Pexp_tuple \<open>expression list\<close>
  | Pexp_construct longident \<open>expression option\<close>
  | Pexp_record \<open>(string \<times> expression) list\<close> \<open>expression option\<close>
  | Pexp_field expression string
  | Pexp_setfield expression string expression
  | Pexp_ifthenelse expression expression \<open>expression option\<close>
  | Pexp_sequence expression expression
  | Pexp_constraint expression core_type
and match_case = Pcase pattern \<open>expression option\<close> expression
and value_binding = Pvb pattern expression

datatype type_kind
  = Ptype_abstract
  | Ptype_variant \<open>(string \<times> core_type list) list\<close>
  | Ptype_record \<open>(mutable_flag \<times> string \<times> core_type) list\<close>

datatype type_declaration = Ptype \<open>string list\<close> string type_kind \<open>core_type option\<close>

datatype structure_item
  = Pstr_value rec_flag \<open>value_binding list\<close>
  | Pstr_type \<open>type_declaration list\<close>
  | Pstr_open longident

definition binop :: \<open>string \<Rightarrow> expression \<Rightarrow> expression \<Rightarrow> expression\<close> where
  \<open>binop p a b = Pexp_apply (Pexp_ident (Lident p)) [a, b]\<close>

definition mk_fun :: \<open>pattern list \<Rightarrow> expression \<Rightarrow> expression\<close> where
  \<open>mk_fun ps e = (case ps of [] \<Rightarrow> e | _ \<Rightarrow> Pexp_fun ps e)\<close>

definition cons_exp :: \<open>expression \<Rightarrow> expression \<Rightarrow> expression\<close> where
  \<open>cons_exp a b = Pexp_construct (Lident ''::'') (Some (Pexp_tuple [a, b]))\<close>

definition list_exp :: \<open>expression list \<Rightarrow> expression\<close> where
  \<open>list_exp es = foldr cons_exp es (Pexp_construct (Lident ''[]'') None)\<close>

definition cons_pat :: \<open>pattern \<Rightarrow> pattern \<Rightarrow> pattern\<close> where
  \<open>cons_pat a b = Ppat_construct (Lident ''::'') (Some (Ppat_tuple [a, b]))\<close>

definition list_pat :: \<open>pattern list \<Rightarrow> pattern\<close> where
  \<open>list_pat ps = foldr cons_pat ps (Ppat_construct (Lident ''[]'') None)\<close>

subsection \<open>Grammar\<close>

text \<open>Lists are built reversed by left recursion and flipped once, as Menhir's
  \<open>reversed_*\<close> nonterminals do. A list with an optional trailing \<open>;\<close> is
  right-recursive.\<close>

grammar ocaml =
  tokens \<open>ocaml_token\<close>
  terminals
    "let" = T_LET and "rec" = T_REC and "and" = T_AND and "in" = T_IN and
    "fun" = T_FUN and "function" = T_FUNCTION and "match" = T_MATCH and
    "with" = T_WITH and "try" = T_TRY and "when" = T_WHEN and "as" = T_AS and
    "if" = T_IF and "then" = T_THEN and "else" = T_ELSE and
    "begin" = T_BEGIN and "end" = T_END and "type" = T_TYPE and "of" = T_OF and
    "mutable" = T_MUTABLE and "open" = T_OPEN and "true" = T_TRUE and "false" = T_FALSE and
    "(" = T_LPAREN and ")" = T_RPAREN and "[" = T_LBRACKET and "]" = T_RBRACKET and
    "{" = T_LBRACE and "}" = T_RBRACE and ";" = T_SEMI and "," = T_COMMA and
    "|" = T_BAR and "->" = T_MINUSGREATER and "=" = T_EQUAL and "-" = T_MINUS and
    "*" = T_STAR and ":" = T_COLON and "::" = T_COLONCOLON and ":=" = T_COLONEQUAL and
    "." = T_DOT and "<-" = T_LESSMINUS and "_" = T_UNDERSCORE and "'" = T_QUOTE and
    "&&" = T_AMPERAMPER and "||" = T_BARBAR and "!" = T_BANG and "<EOF>" = T_EOF
  productions
      implementation :: \<open>structure_item list\<close>
        = structure_items "<EOF>"               \<Rightarrow> \<open>\<lambda>s. rev s\<close>
    and
      structure_items :: \<open>structure_item list\<close>
        =                                       \<Rightarrow> \<open>[]\<close>
        | structure_items structure_item        \<Rightarrow> \<open>\<lambda>s i. i # s\<close>
    and
      structure_item :: \<open>structure_item\<close>
        = let_bindings                          \<Rightarrow> \<open>\<lambda>(r, bs). Pstr_value r (rev bs)\<close>
        | "type" type_decls                     \<Rightarrow> \<open>\<lambda>ds. Pstr_type (rev ds)\<close>
        | "open" mod_longident                  \<Rightarrow> \<open>\<lambda>m. Pstr_open m\<close>
    and
      let_bindings :: \<open>rec_flag \<times> value_binding list\<close>
        = "let" rec_flag let_binding            \<Rightarrow> \<open>\<lambda>r b. (r, [b])\<close>
        | let_bindings "and" let_binding        \<Rightarrow> \<open>\<lambda>(r, bs) b. (r, b # bs)\<close>
    and
      rec_flag :: \<open>rec_flag\<close>
        =                                       \<Rightarrow> \<open>Nonrecursive\<close>
        | "rec"                                 \<Rightarrow> \<open>Recursive\<close>
    and
      let_binding :: \<open>value_binding\<close>
        = val_ident params "=" seq_expr         \<Rightarrow> \<open>\<lambda>x ps e. Pvb (Ppat_var x) (mk_fun (rev ps) e)\<close>
        | val_ident params ":" core_type "=" seq_expr
                                                \<Rightarrow> \<open>\<lambda>x ps t e. Pvb (Ppat_var x) (mk_fun (rev ps) (Pexp_constraint e t))\<close>
        | simple_pattern_not_ident "=" seq_expr \<Rightarrow> \<open>\<lambda>p e. Pvb p e\<close>
        | pattern_comma "=" seq_expr            \<Rightarrow> \<open>\<lambda>ps e. Pvb (Ppat_tuple (rev ps)) e\<close>
    and
      params :: \<open>pattern list\<close>
        =                                       \<Rightarrow> \<open>[]\<close>
        | params simple_pattern                 \<Rightarrow> \<open>\<lambda>ps p. p # ps\<close>
    and
      fun_params :: \<open>pattern list\<close>
        = simple_pattern                        \<Rightarrow> \<open>\<lambda>p. [p]\<close>
        | fun_params simple_pattern             \<Rightarrow> \<open>\<lambda>ps p. p # ps\<close>
    and
      type_decls :: \<open>type_declaration list\<close>
        = type_decl                             \<Rightarrow> \<open>\<lambda>d. [d]\<close>
        | type_decls "and" type_decl            \<Rightarrow> \<open>\<lambda>ds d. d # ds\<close>
    and
      type_decl :: \<open>type_declaration\<close>
        = type_params T_LIDENT                  \<Rightarrow> \<open>\<lambda>ps n. Ptype ps (tok_text n) Ptype_abstract None\<close>
        | type_params T_LIDENT "=" core_type    \<Rightarrow> \<open>\<lambda>ps n t. Ptype ps (tok_text n) Ptype_abstract (Some t)\<close>
        | type_params T_LIDENT "=" constructors \<Rightarrow> \<open>\<lambda>ps n cs. Ptype ps (tok_text n) (Ptype_variant (rev cs)) None\<close>
        | type_params T_LIDENT "=" "{" label_decls "}"
                                                \<Rightarrow> \<open>\<lambda>ps n ls. Ptype ps (tok_text n) (Ptype_record ls) None\<close>
    and
      type_params :: \<open>string list\<close>
        =                                       \<Rightarrow> \<open>[]\<close>
        | type_var                              \<Rightarrow> \<open>\<lambda>v. [v]\<close>
        | "(" type_vars ")"                     \<Rightarrow> \<open>\<lambda>vs. rev vs\<close>
    and
      type_vars :: \<open>string list\<close>
        = type_var                              \<Rightarrow> \<open>\<lambda>v. [v]\<close>
        | type_vars "," type_var                \<Rightarrow> \<open>\<lambda>vs v. v # vs\<close>
    and
      type_var :: \<open>string\<close>
        = "'" T_LIDENT                          \<Rightarrow> \<open>\<lambda>x. tok_text x\<close>
    and
      constructors :: \<open>(string \<times> core_type list) list\<close>
        = ctor_decl                             \<Rightarrow> \<open>\<lambda>c. [c]\<close>
        | "|" ctor_decl                         \<Rightarrow> \<open>\<lambda>c. [c]\<close>
        | constructors "|" ctor_decl            \<Rightarrow> \<open>\<lambda>cs c. c # cs\<close>
    and
      ctor_decl :: \<open>string \<times> core_type list\<close>
        = T_UIDENT                              \<Rightarrow> \<open>\<lambda>c. (tok_text c, [])\<close>
        | T_UIDENT "of" ctor_args               \<Rightarrow> \<open>\<lambda>c ts. (tok_text c, rev ts)\<close>
    and
      ctor_args :: \<open>core_type list\<close>
        = app_type                              \<Rightarrow> \<open>\<lambda>t. [t]\<close>
        | ctor_args "*" app_type                \<Rightarrow> \<open>\<lambda>ts t. t # ts\<close>
    and
      label_decls :: \<open>(mutable_flag \<times> string \<times> core_type) list\<close>
        = label_decl                            \<Rightarrow> \<open>\<lambda>l. [l]\<close>
        | label_decl ";"                        \<Rightarrow> \<open>\<lambda>l. [l]\<close>
        | label_decl ";" label_decls            \<Rightarrow> \<open>\<lambda>l ls. l # ls\<close>
    and
      label_decl :: \<open>mutable_flag \<times> string \<times> core_type\<close>
        = mutable_flag T_LIDENT ":" core_type   \<Rightarrow> \<open>\<lambda>m x t. (m, tok_text x, t)\<close>
    and
      mutable_flag :: \<open>mutable_flag\<close>
        =                                       \<Rightarrow> \<open>Immutable\<close>
        | "mutable"                             \<Rightarrow> \<open>Mutable\<close>
    and
      core_type :: \<open>core_type\<close>
        = tuple_type                            \<Rightarrow> \<open>\<lambda>t. t\<close>
        | tuple_type "->" core_type             \<Rightarrow> \<open>\<lambda>a b. Ptyp_arrow a b\<close>
    and
      tuple_type :: \<open>core_type\<close>
        = app_type                              \<Rightarrow> \<open>\<lambda>t. t\<close>
        | star_types                            \<Rightarrow> \<open>\<lambda>ts. Ptyp_tuple (rev ts)\<close>
    and
      star_types :: \<open>core_type list\<close>
        = app_type "*" app_type                 \<Rightarrow> \<open>\<lambda>a b. [b, a]\<close>
        | star_types "*" app_type               \<Rightarrow> \<open>\<lambda>ts t. t # ts\<close>
    and
      app_type :: \<open>core_type\<close>
        = atomic_type                           \<Rightarrow> \<open>\<lambda>t. t\<close>
        | app_type type_longident               \<Rightarrow> \<open>\<lambda>t c. Ptyp_constr c [t]\<close>
        | "(" core_type "," type_list ")" type_longident
                                                \<Rightarrow> \<open>\<lambda>t ts c. Ptyp_constr c (t # rev ts)\<close>
    and
      type_list :: \<open>core_type list\<close>
        = core_type                             \<Rightarrow> \<open>\<lambda>t. [t]\<close>
        | type_list "," core_type               \<Rightarrow> \<open>\<lambda>ts t. t # ts\<close>
    and
      atomic_type :: \<open>core_type\<close>
        = type_var                              \<Rightarrow> \<open>\<lambda>v. Ptyp_var v\<close>
        | type_longident                        \<Rightarrow> \<open>\<lambda>c. Ptyp_constr c []\<close>
        | "(" core_type ")"                     \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      type_longident :: \<open>longident\<close>
        = T_LIDENT                              \<Rightarrow> \<open>\<lambda>x. Lident (tok_text x)\<close>
        | mod_longident "." T_LIDENT            \<Rightarrow> \<open>\<lambda>m x. Ldot m (tok_text x)\<close>
    and
      mod_longident :: \<open>longident\<close>
        = T_UIDENT                              \<Rightarrow> \<open>\<lambda>x. Lident (tok_text x)\<close>
        | mod_longident "." T_UIDENT            \<Rightarrow> \<open>\<lambda>m x. Ldot m (tok_text x)\<close>
    and
      constr_longident :: \<open>longident\<close>
        = mod_longident                         \<Rightarrow> \<open>\<lambda>c. c\<close>
        | "true"                                \<Rightarrow> \<open>Lident ''true''\<close>
        | "false"                               \<Rightarrow> \<open>Lident ''false''\<close>
        | "(" ")"                               \<Rightarrow> \<open>Lident ''()''\<close>
        | "[" "]"                               \<Rightarrow> \<open>Lident ''[]''\<close>
    and
      pattern :: \<open>pattern\<close>
        = pattern_or                            \<Rightarrow> \<open>\<lambda>p. p\<close>
        | pattern "as" val_ident                \<Rightarrow> \<open>\<lambda>p x. Ppat_alias p x\<close>
    and
      pattern_or :: \<open>pattern\<close>
        = pattern_tuple                         \<Rightarrow> \<open>\<lambda>p. p\<close>
        | pattern_or "|" pattern_tuple          \<Rightarrow> \<open>\<lambda>a b. Ppat_or a b\<close>
    and
      pattern_tuple :: \<open>pattern\<close>
        = pattern_cons                          \<Rightarrow> \<open>\<lambda>p. p\<close>
        | pattern_comma                         \<Rightarrow> \<open>\<lambda>ps. Ppat_tuple (rev ps)\<close>
    and
      pattern_comma :: \<open>pattern list\<close>
        = pattern_cons "," pattern_cons         \<Rightarrow> \<open>\<lambda>a b. [b, a]\<close>
        | pattern_comma "," pattern_cons        \<Rightarrow> \<open>\<lambda>ps p. p # ps\<close>
    and
      pattern_cons :: \<open>pattern\<close>
        = pattern_app                           \<Rightarrow> \<open>\<lambda>p. p\<close>
        | pattern_app "::" pattern_cons         \<Rightarrow> \<open>\<lambda>a b. cons_pat a b\<close>
    and
      pattern_app :: \<open>pattern\<close>
        = simple_pattern                        \<Rightarrow> \<open>\<lambda>p. p\<close>
        | constr_longident simple_pattern       \<Rightarrow> \<open>\<lambda>c p. Ppat_construct c (Some p)\<close>
    and
      simple_pattern :: \<open>pattern\<close>
        = val_ident                             \<Rightarrow> \<open>\<lambda>x. Ppat_var x\<close>
        | simple_pattern_not_ident              \<Rightarrow> \<open>\<lambda>p. p\<close>
    and
      simple_pattern_not_ident :: \<open>pattern\<close>
        = "_"                                   \<Rightarrow> \<open>Ppat_any\<close>
        | const                                 \<Rightarrow> \<open>\<lambda>c. Ppat_constant c\<close>
        | constr_longident                      \<Rightarrow> \<open>\<lambda>c. Ppat_construct c None\<close>
        | "(" pattern ")"                       \<Rightarrow> \<open>\<lambda>p. p\<close>
        | "(" pattern ":" core_type ")"         \<Rightarrow> \<open>\<lambda>p t. Ppat_constraint p t\<close>
        | "[" pattern_semi_list "]"             \<Rightarrow> \<open>\<lambda>ps. list_pat (rev ps)\<close>
        | "{" field_pats "}"                    \<Rightarrow> \<open>\<lambda>fs. Ppat_record (rev fs) Closed\<close>
        | "{" field_pats ";" "_" "}"            \<Rightarrow> \<open>\<lambda>fs. Ppat_record (rev fs) Open\<close>
    and
      pattern_semi_list :: \<open>pattern list\<close>
        = pattern                               \<Rightarrow> \<open>\<lambda>p. [p]\<close>
        | pattern_semi_list ";" pattern         \<Rightarrow> \<open>\<lambda>ps p. p # ps\<close>
    and
      field_pats :: \<open>(string \<times> pattern) list\<close>
        = field_pat                             \<Rightarrow> \<open>\<lambda>f. [f]\<close>
        | field_pats ";" field_pat              \<Rightarrow> \<open>\<lambda>fs f. f # fs\<close>
    and
      field_pat :: \<open>string \<times> pattern\<close>
        = T_LIDENT "=" pattern                  \<Rightarrow> \<open>\<lambda>l p. (tok_text l, p)\<close>
        | T_LIDENT                              \<Rightarrow> \<open>\<lambda>l. (tok_text l, Ppat_var (tok_text l))\<close>
    and
      seq_expr :: \<open>expression\<close>
        = expr                                  \<Rightarrow> \<open>\<lambda>e. e\<close>
        | expr ";" seq_expr                     \<Rightarrow> \<open>\<lambda>a b. Pexp_sequence a b\<close>
        | let_bindings "in" seq_expr            \<Rightarrow> \<open>\<lambda>(r, bs) e. Pexp_let r (rev bs) e\<close>
        | "fun" fun_params "->" seq_expr        \<Rightarrow> \<open>\<lambda>ps e. Pexp_fun (rev ps) e\<close>
        | "match" seq_expr "with" match_cases   \<Rightarrow> \<open>\<lambda>e cs. Pexp_match e (rev cs)\<close>
        | "function" match_cases                \<Rightarrow> \<open>\<lambda>cs. Pexp_function (rev cs)\<close>
        | "try" seq_expr "with" match_cases     \<Rightarrow> \<open>\<lambda>e cs. Pexp_try e (rev cs)\<close>
        | "if" seq_expr "then" expr_m "else" else_tail
                                                \<Rightarrow> \<open>\<lambda>c a b. Pexp_ifthenelse c a (Some b)\<close>
    and
      seq_expr_c :: \<open>expression\<close>
        = expr                                  \<Rightarrow> \<open>\<lambda>e. e\<close>
        | expr ";" seq_expr_c                   \<Rightarrow> \<open>\<lambda>a b. Pexp_sequence a b\<close>
        | let_bindings "in" seq_expr_c          \<Rightarrow> \<open>\<lambda>(r, bs) e. Pexp_let r (rev bs) e\<close>
        | "fun" fun_params "->" seq_expr_c      \<Rightarrow> \<open>\<lambda>ps e. Pexp_fun (rev ps) e\<close>
        | "if" seq_expr "then" expr_m "else" else_tail_c
                                                \<Rightarrow> \<open>\<lambda>c a b. Pexp_ifthenelse c a (Some b)\<close>
    and
      else_tail :: \<open>expression\<close>
        = let_bindings "in" seq_expr            \<Rightarrow> \<open>\<lambda>(r, bs) e. Pexp_let r (rev bs) e\<close>
        | "fun" fun_params "->" seq_expr        \<Rightarrow> \<open>\<lambda>ps e. Pexp_fun (rev ps) e\<close>
        | "match" seq_expr "with" match_cases   \<Rightarrow> \<open>\<lambda>e cs. Pexp_match e (rev cs)\<close>
        | "function" match_cases                \<Rightarrow> \<open>\<lambda>cs. Pexp_function (rev cs)\<close>
        | "try" seq_expr "with" match_cases     \<Rightarrow> \<open>\<lambda>e cs. Pexp_try e (rev cs)\<close>
        | "if" seq_expr "then" expr_m "else" else_tail
                                                \<Rightarrow> \<open>\<lambda>c a b. Pexp_ifthenelse c a (Some b)\<close>
    and
      else_tail_c :: \<open>expression\<close>
        = let_bindings "in" seq_expr_c          \<Rightarrow> \<open>\<lambda>(r, bs) e. Pexp_let r (rev bs) e\<close>
        | "fun" fun_params "->" seq_expr_c      \<Rightarrow> \<open>\<lambda>ps e. Pexp_fun (rev ps) e\<close>
        | "if" seq_expr "then" expr_m "else" else_tail_c
                                                \<Rightarrow> \<open>\<lambda>c a b. Pexp_ifthenelse c a (Some b)\<close>
    and
      match_cases :: \<open>match_case list\<close>
        = case_list                             \<Rightarrow> \<open>\<lambda>cs. cs\<close>
        | "|" case_list                         \<Rightarrow> \<open>\<lambda>cs. cs\<close>
    and
      case_list :: \<open>match_case list\<close>
        = match_case                            \<Rightarrow> \<open>\<lambda>c. [c]\<close>
        | case_list_c "|" match_case            \<Rightarrow> \<open>\<lambda>cs c. c # cs\<close>
    and
      case_list_c :: \<open>match_case list\<close>
        = match_case_c                          \<Rightarrow> \<open>\<lambda>c. [c]\<close>
        | case_list_c "|" match_case_c          \<Rightarrow> \<open>\<lambda>cs c. c # cs\<close>
    and
      match_case :: \<open>match_case\<close>
        = pattern "->" seq_expr                 \<Rightarrow> \<open>\<lambda>p e. Pcase p None e\<close>
        | pattern "when" seq_expr "->" seq_expr \<Rightarrow> \<open>\<lambda>p g e. Pcase p (Some g) e\<close>
    and
      match_case_c :: \<open>match_case\<close>
        = pattern "->" seq_expr_c               \<Rightarrow> \<open>\<lambda>p e. Pcase p None e\<close>
        | pattern "when" seq_expr "->" seq_expr_c
                                                \<Rightarrow> \<open>\<lambda>p g e. Pcase p (Some g) e\<close>
    and
      expr :: \<open>expression\<close>
        = assign_expr                           \<Rightarrow> \<open>\<lambda>e. e\<close>
        | "if" seq_expr "then" expr             \<Rightarrow> \<open>\<lambda>c a. Pexp_ifthenelse c a None\<close>
        | "if" seq_expr "then" expr_m "else" expr
                                                \<Rightarrow> \<open>\<lambda>c a b. Pexp_ifthenelse c a (Some b)\<close>
    and
      expr_m :: \<open>expression\<close>
        = assign_expr                           \<Rightarrow> \<open>\<lambda>e. e\<close>
        | "if" seq_expr "then" expr_m "else" expr_m
                                                \<Rightarrow> \<open>\<lambda>c a b. Pexp_ifthenelse c a (Some b)\<close>
    and
      assign_expr :: \<open>expression\<close>
        = tuple_expr                            \<Rightarrow> \<open>\<lambda>e. e\<close>
        | simple_expr_nc "." T_LIDENT "<-" assign_expr
                                                \<Rightarrow> \<open>\<lambda>a l b. Pexp_setfield a (tok_text l) b\<close>
        | tuple_expr ":=" assign_expr           \<Rightarrow> \<open>\<lambda>a b. binop '':='' a b\<close>
    and
      tuple_expr :: \<open>expression\<close>
        = or_expr                               \<Rightarrow> \<open>\<lambda>e. e\<close>
        | expr_comma                            \<Rightarrow> \<open>\<lambda>es. Pexp_tuple (rev es)\<close>
    and
      expr_comma :: \<open>expression list\<close>
        = or_expr "," or_expr                   \<Rightarrow> \<open>\<lambda>a b. [b, a]\<close>
        | expr_comma "," or_expr                \<Rightarrow> \<open>\<lambda>es e. e # es\<close>
    and
      or_expr :: \<open>expression\<close>
        = and_expr                              \<Rightarrow> \<open>\<lambda>e. e\<close>
        | and_expr "||" or_expr                 \<Rightarrow> \<open>\<lambda>a b. binop ''||'' a b\<close>
    and
      and_expr :: \<open>expression\<close>
        = cmp_expr                              \<Rightarrow> \<open>\<lambda>e. e\<close>
        | cmp_expr "&&" and_expr                \<Rightarrow> \<open>\<lambda>a b. binop ''&&'' a b\<close>
    and
      cmp_expr :: \<open>expression\<close>
        = concat_expr                           \<Rightarrow> \<open>\<lambda>e. e\<close>
        | cmp_expr "=" concat_expr              \<Rightarrow> \<open>\<lambda>a b. binop ''='' a b\<close>
        | cmp_expr T_INFIXOP0 concat_expr       \<Rightarrow> \<open>\<lambda>a x b. binop (tok_text x) a b\<close>
    and
      concat_expr :: \<open>expression\<close>
        = cons_expr                             \<Rightarrow> \<open>\<lambda>e. e\<close>
        | cons_expr T_INFIXOP1 concat_expr      \<Rightarrow> \<open>\<lambda>a x b. binop (tok_text x) a b\<close>
    and
      cons_expr :: \<open>expression\<close>
        = add_expr                              \<Rightarrow> \<open>\<lambda>e. e\<close>
        | add_expr "::" cons_expr               \<Rightarrow> \<open>\<lambda>a b. cons_exp a b\<close>
    and
      add_expr :: \<open>expression\<close>
        = mul_expr                              \<Rightarrow> \<open>\<lambda>e. e\<close>
        | add_expr "-" mul_expr                 \<Rightarrow> \<open>\<lambda>a b. binop ''-'' a b\<close>
        | add_expr T_INFIXOP2 mul_expr          \<Rightarrow> \<open>\<lambda>a x b. binop (tok_text x) a b\<close>
    and
      mul_expr :: \<open>expression\<close>
        = unary_expr                            \<Rightarrow> \<open>\<lambda>e. e\<close>
        | mul_expr "*" unary_expr               \<Rightarrow> \<open>\<lambda>a b. binop ''*'' a b\<close>
        | mul_expr T_INFIXOP3 unary_expr        \<Rightarrow> \<open>\<lambda>a x b. binop (tok_text x) a b\<close>
    and
      unary_expr :: \<open>expression\<close>
        = app_expr                              \<Rightarrow> \<open>\<lambda>e. e\<close>
        | "-" unary_expr                        \<Rightarrow> \<open>\<lambda>e. Pexp_apply (Pexp_ident (Lident ''~-'')) [e]\<close>
    and
      app_expr :: \<open>expression\<close>
        = simple_expr                           \<Rightarrow> \<open>\<lambda>e. e\<close>
        | simple_expr_nc app_args               \<Rightarrow> \<open>\<lambda>f xs. Pexp_apply f (rev xs)\<close>
        | constr_longident simple_expr          \<Rightarrow> \<open>\<lambda>c e. Pexp_construct c (Some e)\<close>
    and
      app_args :: \<open>expression list\<close>
        = simple_expr                           \<Rightarrow> \<open>\<lambda>e. [e]\<close>
        | app_args simple_expr                  \<Rightarrow> \<open>\<lambda>es e. e # es\<close>
    and
      simple_expr :: \<open>expression\<close>
        = simple_expr_nc                        \<Rightarrow> \<open>\<lambda>e. e\<close>
        | constr_longident                      \<Rightarrow> \<open>\<lambda>c. Pexp_construct c None\<close>
    and
      simple_expr_nc :: \<open>expression\<close>
        = atom                                  \<Rightarrow> \<open>\<lambda>e. e\<close>
        | simple_expr_nc "." T_LIDENT           \<Rightarrow> \<open>\<lambda>e l. Pexp_field e (tok_text l)\<close>
    and
      atom :: \<open>expression\<close>
        = val_longident                         \<Rightarrow> \<open>\<lambda>x. Pexp_ident x\<close>
        | const                                 \<Rightarrow> \<open>\<lambda>c. Pexp_constant c\<close>
        | "(" seq_expr ")"                      \<Rightarrow> \<open>\<lambda>e. e\<close>
        | "(" seq_expr ":" core_type ")"        \<Rightarrow> \<open>\<lambda>e t. Pexp_constraint e t\<close>
        | "begin" seq_expr "end"                \<Rightarrow> \<open>\<lambda>e. e\<close>
        | "[" expr_semi_list "]"                \<Rightarrow> \<open>\<lambda>es. list_exp es\<close>
        | "{" record_fields "}"                 \<Rightarrow> \<open>\<lambda>fs. Pexp_record fs None\<close>
        | "{" simple_expr "with" record_fields "}"
                                                \<Rightarrow> \<open>\<lambda>e fs. Pexp_record fs (Some e)\<close>
        | "!" atom                              \<Rightarrow> \<open>\<lambda>e. Pexp_apply (Pexp_ident (Lident ''!'')) [e]\<close>
    and
      expr_semi_list :: \<open>expression list\<close>
        = expr                                  \<Rightarrow> \<open>\<lambda>e. [e]\<close>
        | expr ";"                              \<Rightarrow> \<open>\<lambda>e. [e]\<close>
        | expr ";" expr_semi_list               \<Rightarrow> \<open>\<lambda>e es. e # es\<close>
    and
      record_fields :: \<open>(string \<times> expression) list\<close>
        = record_field                          \<Rightarrow> \<open>\<lambda>f. [f]\<close>
        | record_field ";"                      \<Rightarrow> \<open>\<lambda>f. [f]\<close>
        | record_field ";" record_fields        \<Rightarrow> \<open>\<lambda>f fs. f # fs\<close>
    and
      record_field :: \<open>string \<times> expression\<close>
        = T_LIDENT "=" expr                     \<Rightarrow> \<open>\<lambda>l e. (tok_text l, e)\<close>
        | T_LIDENT                              \<Rightarrow> \<open>\<lambda>l. (tok_text l, Pexp_ident (Lident (tok_text l)))\<close>
    and
      val_longident :: \<open>longident\<close>
        = val_ident                             \<Rightarrow> \<open>\<lambda>x. Lident x\<close>
        | mod_longident "." T_LIDENT            \<Rightarrow> \<open>\<lambda>m x. Ldot m (tok_text x)\<close>
    and
      val_ident :: \<open>string\<close>
        = T_LIDENT                              \<Rightarrow> \<open>\<lambda>x. tok_text x\<close>
    and
      const :: \<open>pconstant\<close>
        = T_INT                                 \<Rightarrow> \<open>\<lambda>t. Pconst_integer (tok_text t)\<close>
        | T_FLOAT                               \<Rightarrow> \<open>\<lambda>t. Pconst_float (tok_text t)\<close>
        | T_STRING                              \<Rightarrow> \<open>\<lambda>t. Pconst_string (tok_text t)\<close>
        | T_CHAR                                \<Rightarrow> \<open>\<lambda>t. Pconst_char (tok_text t)\<close>

parser ocaml_implementation for ocaml

subsection \<open>Code\<close>

definition mk_token :: \<open>ocaml_tok \<Rightarrow> String.literal \<Rightarrow> ocaml_token\<close> where
  \<open>mk_token x s = \<lparr>tok = x, span = span.make 0 0 0 0 (String.explode s)\<rparr>\<close>

export_code ocaml_implementation mk_token String.implode String.explode
    binop mk_fun cons_exp list_exp cons_pat list_pat
    T_EOF Lident Pconst_integer Nonrecursive Immutable Closed Ptyp_var Ppat_any
    Pexp_ident Pcase Pvb Ptype_abstract Ptype Pstr_value
  in OCaml module_name OCaml_Parser file_prefix ocaml_parser

end
