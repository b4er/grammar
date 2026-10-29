theory Pure_Grammar
  imports LR_Parser.LR_Parser Pure_AST
begin

section \<open>PureCake's PEG as an indentation-sensitive CFG\<close>

text \<open>A transcription of \<open>purePEG\<close>:

  PureCake's IS-PEG attaches the relations \<open>lrEQ\<close>, \<open>lrGE\<close>, \<open>lrGT\<close>, \<open>lrOK\<close> to
  symbols exactly as adams2013 does; they become \<open>^=\<close>, \<open>^>=\<close>, \<open>^>\<close>, \<open>^*\<close>.
  The PEG's \<open>rpt\<close>, \<open>sepby\<close> and optional parts become left-recursive auxiliary
  nonterminals under \<open>^=\<close>, which pass the parent's indentation through unchanged; their
  values are lists in reverse.

  Where the PEG's ordered choice and greedy repetition make a CFG ambiguous, the
  grammar keeps the PEG's preferred reading:
  \<^item> \<open>do\<close> is an atomic expression only as an argument (\<open>f do\<close>), never where a
    \<open>do\<close> block can start; \<open>data\<close> is never one at the start of a declaration.
  \<^item> An operand that is an l-safe expression (\<open>\<lambda>\<close>, \<open>if\<close>, \<open>let\<close>, \<open>do\<close>, \<open>case\<close>) is the
    last operand of its infix chain: its body takes the rest of the chain.
  \<^item> A \<open>do\<close> block ends in an expression statement. A block ending in a binding or a
    \<open>let\<close> is a parse that \<open>cst_to_ast\<close> rejects; here it is no parse, which removes the
    reading of \<open>do let x = e in b\<close> as a \<open>let\<close> statement closed by an outer \<open>in\<close>.

  Lexing is PureCake's own (\<open>pure_lexer_impl\<close>, run outside Isabelle); the parser reads
  its tokens as \<open>ptok\<close> classes, with the identifier, symbol, literal or FFI
  text in the span's \<open>s_txt\<close>.\<close>

subsection \<open>Tokens\<close>

text \<open>The classes of PureCake's lexer tokens the PEG tells apart. \<open>PCap\<close> and \<open>PLc\<close>
  are \<open>capname_tok\<close> and \<open>lcname_tok\<close>, \<open>PAlpha\<close> any other \<open>AlphaT\<close> but \<open>data\<close>
  and \<open>do\<close>; \<open>PSym\<close> is a \<open>SymbolT\<close> other than those with a terminal of their own;
  \<open>POther\<close> any token the PEG never accepts.\<close>

datatype ptok =
    PLpar | PRpar | PComma | PSemi | PEquals | PLbrack | PRbrack | PLbrace | PRbrace
  | PBar | PUnder | PCase | PElse | PIf | PIn | PLet | POf | PThen
  | PCap | PLc | PAlpha | PData | PDo
  | PDColon | PArrow | PLArrow | PBacktick | PBackslash | PSym
  | PInt | PStr | PFFI | POther

type_synonym ptoken = \<open>(ptok, char) token\<close>

definition ttxt :: \<open>ptoken \<Rightarrow> string\<close> where
  \<open>ttxt t = s_txt (span t)\<close>

definition nat_of_digits :: \<open>string \<Rightarrow> nat\<close> where
  \<open>nat_of_digits s = foldl (\<lambda>n c. 10 * n + (of_char c - 48)) 0 s\<close>

definition int_of_txt :: \<open>string \<Rightarrow> int\<close> where
  \<open>int_of_txt s = (case s of c # r \<Rightarrow> if c = CHR ''-'' then - int (nat_of_digits r)
     else int (nat_of_digits s) | [] \<Rightarrow> 0)\<close>

subsection \<open>Semantic actions\<close>

text \<open>A value \<^const>\<open>None\<close> is a parse that \<open>cst_to_ast\<close> rejects (a left-hand side
  that is no pattern, a non-associative operator chain, a \<open>do\<close> block ending in a
  binding, \<dots>): PureCake's \<open>string_to_asts\<close> then returns \<open>NONE\<close>.\<close>

definition ob2 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c option) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option\<close> where
  \<open>ob2 f a b = (case a of None \<Rightarrow> None | Some x \<Rightarrow> (case b of None \<Rightarrow> None | Some y \<Rightarrow> f x y))\<close>

definition ob3 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd option) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option\<close> where
  \<open>ob3 f a b c = Option.bind (ob2 (\<lambda>x y. map_option (\<lambda>z. (x, y, z)) c) a b) (\<lambda>(x, y, z). f x y z)\<close>

definition osnoc :: \<open>'a list option \<Rightarrow> 'a option \<Rightarrow> 'a list option\<close> where
  \<open>osnoc xs x = ob2 (\<lambda>l y. Some (y # l)) xs x\<close>

definition orev :: \<open>'a list option \<Rightarrow> 'a list option\<close> where
  \<open>orev xs = map_option rev xs\<close>

definition oappend :: \<open>'a list option \<Rightarrow> 'a list option \<Rightarrow> 'a list option\<close> where
  \<open>oappend xs ys = ob2 (\<lambda>a b. Some (a @ b)) xs ys\<close>

definition tup_ty :: \<open>tyAST list \<Rightarrow> tyAST\<close> where
  \<open>tup_ty ts = (case rev ts of [t] \<Rightarrow> t | us \<Rightarrow> tyTup us)\<close>

definition paren_exp :: \<open>expAST list \<Rightarrow> expAST\<close> where
  \<open>paren_exp es = (case rev es of [e] \<Rightarrow> e | fs \<Rightarrow> expTup fs)\<close>

definition list_exp :: \<open>expAST list \<Rightarrow> expAST\<close> where
  \<open>list_exp es = foldl (\<lambda>r e. expCon ''::'' [e, r]) (expCon ''[]'' []) es\<close>

definition act_valbind :: \<open>expAST option \<Rightarrow> expAST option \<Rightarrow> declAST option\<close> where
  \<open>act_valbind l r = ob2 (\<lambda>le re. map_option (\<lambda>f. f re) (astFunPatBindf le)) l r\<close>

definition act_eqbind :: \<open>expAST option \<Rightarrow> expAST option \<Rightarrow> expdecAST option\<close> where
  \<open>act_eqbind l r = ob2 (\<lambda>le re. map_option (\<lambda>rd. case rd of
       resolve_declPattern p \<Rightarrow> expdecPatbind p re
     | resolve_declFun f ps \<Rightarrow> expdecFunbind f ps re) (resolve_decl le)) l r\<close>

definition act_iexp :: \<open>expAST option \<Rightarrow> pitem list option \<Rightarrow> expAST option\<close> where
  \<open>act_iexp f ts = ob2 (\<lambda>v l. handlePrecs (Inr v # rev l)) f ts\<close>

definition act_iexp_last ::
  \<open>expAST option \<Rightarrow> pitem list option \<Rightarrow> string \<Rightarrow> expAST option \<Rightarrow> expAST option\<close> where
  \<open>act_iexp_last f ts opr e = act_iexp f (osnoc (osnoc ts (Some (Inl opr))) (map_option Inr e))\<close>

definition act_optail :: \<open>pitem list option \<Rightarrow> string \<Rightarrow> expAST option \<Rightarrow> pitem list option\<close> where
  \<open>act_optail ts opr e = osnoc (osnoc ts (Some (Inl opr))) (map_option Inr e)\<close>

definition act_fexp :: \<open>expAST option \<Rightarrow> expAST list option \<Rightarrow> expAST option\<close> where
  \<open>act_fexp f as = ob2 (\<lambda>fe l. Some (mkApp fe (rev l))) f as\<close>

definition act_lam :: \<open>patAST list \<Rightarrow> expAST option \<Rightarrow> expAST option\<close> where
  \<open>act_lam ps e = map_option (\<lambda>b. foldl (\<lambda>r p. expAbs p r) b ps) e\<close>

definition act_if :: \<open>expAST option \<Rightarrow> expAST option \<Rightarrow> expAST option \<Rightarrow> expAST option\<close> where
  \<open>act_if a b c = ob3 (\<lambda>x y z. Some (expIf x y z)) a b c\<close>

definition act_let :: \<open>expdecAST list option \<Rightarrow> expAST option \<Rightarrow> expAST option\<close> where
  \<open>act_let ds e = ob2 (\<lambda>l b. Some (expLet l b)) ds e\<close>

text \<open>A \<open>do\<close> block's statements so far, in reverse: ending in an expression (the
  statements before it and the expression) or in a binding or \<open>let\<close>. Only the first
  kind closes a block, where \<open>cst_to_ast\<close>'s \<open>optLAST\<close> rejects the second.\<close>

type_synonym dosE = \<open>(expdostmtAST list \<times> expAST) option\<close>
type_synonym dosN = \<open>expdostmtAST list option\<close>

definition act_do_e :: \<open>dosE \<Rightarrow> expAST option \<Rightarrow> dosE\<close> where
  \<open>act_do_e ss e = ob2 (\<lambda>(l, x) y. Some (expdostmtExp x # l, y)) ss e\<close>

definition act_do_ne :: \<open>dosN \<Rightarrow> expAST option \<Rightarrow> dosE\<close> where
  \<open>act_do_ne ss e = ob2 (\<lambda>l y. Some (l, y)) ss e\<close>

definition act_do_en :: \<open>dosE \<Rightarrow> expdostmtAST option \<Rightarrow> dosN\<close> where
  \<open>act_do_en ss s = ob2 (\<lambda>(l, x) t. Some (t # expdostmtExp x # l)) ss s\<close>

definition act_do :: \<open>dosE \<Rightarrow> expAST option\<close> where
  \<open>act_do ss = map_option (\<lambda>(l, x). expDo (rev l) x) ss\<close>

definition act_case :: \<open>expAST option \<Rightarrow> (patAST \<times> expAST) list option \<Rightarrow> expAST option\<close> where
  \<open>act_case e as = ob2 (\<lambda>x l. Some (expCase x (rev l))) e as\<close>

definition act_patalt :: \<open>expAST option \<Rightarrow> expAST option \<Rightarrow> (patAST \<times> expAST) option\<close> where
  \<open>act_patalt l r = ob2 (\<lambda>pe e. map_option (\<lambda>p. (p, e)) (exp_to_pat pe)) l r\<close>

definition act_bind :: \<open>expAST option \<Rightarrow> expAST option \<Rightarrow> expdostmtAST option\<close> where
  \<open>act_bind l r = ob2 (\<lambda>pe e. map_option (\<lambda>p. expdostmtBind p e) (exp_to_pat pe)) l r\<close>

subsection \<open>The grammar\<close>

text \<open>Nonterminals are PureCake's, minus the \<open>n\<close>; \<open>File\<close> is the PEG's start
  \<open>NT nDecls I lrOK\<close>. \<open>LcArgs\<close>, \<open>TyBases\<close>, \<open>TyList\<close>, \<open>TyArr\<close>, \<open>FreeBinds\<close>, \<open>LBinds\<close> (\<open>EqBindSeq'\<close>), \<open>OpTail\<close>, \<open>Args\<close>, \<open>APats\<close>, \<open>SeqE\<close>/\<open>SeqN\<close> (\<open>DoStmtSeq\<close>), \<open>LinesE\<close>/\<open>LinesN\<close> (\<open>DoBlockLayout\<close> over \<open>DoStmtSeqEQ\<close>) and \<open>ExpList\<close> expand the PEG's \<open>rpt\<close>/\<open>sepby\<close>.\<close>

grammar (relation) pure =
  tokens \<open>ptoken\<close>
  terminals
    "(" = PLpar and ")" = PRpar and "," = PComma and ";" = PSemi and "=" = PEquals and
    "[" = PLbrack and "]" = PRbrack and "{" = PLbrace and "}" = PRbrace and "|" = PBar and
    "_" = PUnder and "case" = PCase and "else" = PElse and "if" = PIf and "in" = PIn and
    "let" = PLet and "of" = POf and "then" = PThen and "data" = PData and "do" = PDo and
    "::" = PDColon and "->" = PArrow and "<-" = PLArrow and "`" = PBacktick and
    "\<lambda>" = PBackslash
  productions
      File :: \<open>declAST list option\<close>
        = Decls\<^sup>*                                 \<Rightarrow> \<open>orev\<close>
    and
      Decls :: \<open>declAST list option\<close>
        =                                       \<Rightarrow> \<open>Some []\<close>
        | Decls\<^sup>= Decl\<^sup>=                          \<Rightarrow> \<open>osnoc\<close>
    and
      Decl :: \<open>declAST option\<close>
        = PLc\<^sup>= "::"\<^sup>> Ty\<^sup>>                     \<Rightarrow> \<open>\<lambda>x t. Some (declTysig (ttxt x) t)\<close>
        | "data"\<^sup>= PCap\<^sup>> LcArgs\<^sup>= "="\<^sup>> TyCons\<^sup>=
            \<Rightarrow> \<open>\<lambda>c as cs. Some (declData (ttxt c) (rev as) (rev cs))\<close>
        | ExpEQ\<^sup>= "="\<^sup>> Exp\<^sup>=                    \<Rightarrow> \<open>act_valbind\<close>
    and
      LcArgs :: \<open>string list\<close>
        =                                       \<Rightarrow> \<open>[]\<close>
        | LcArgs\<^sup>= PLc\<^sup>>                         \<Rightarrow> \<open>\<lambda>as a. ttxt a # as\<close>
    and
      TyCons :: \<open>(string \<times> tyAST list) list\<close>
        = TyConDecl\<^sup>>                            \<Rightarrow> \<open>\<lambda>c. [c]\<close>
        | TyCons\<^sup>= "|"\<^sup>> TyConDecl\<^sup>>             \<Rightarrow> \<open>\<lambda>cs c. c # cs\<close>
    and
      TyConDecl :: \<open>string \<times> tyAST list\<close>
        = PCap\<^sup>\<ge>                                \<Rightarrow> \<open>\<lambda>c. (ttxt c, [])\<close>
        | PCap\<^sup>\<ge> TyBases\<^sup>=                      \<Rightarrow> \<open>\<lambda>c ts. (ttxt c, rev ts)\<close>
    and
      TyBases :: \<open>tyAST list\<close>
        = TyBase\<^sup>\<ge>                              \<Rightarrow> \<open>\<lambda>t. [t]\<close>
        | TyBases\<^sup>= TyBase\<^sup>\<ge>                    \<Rightarrow> \<open>\<lambda>ts t. t # ts\<close>
    and
      TyBase :: \<open>tyAST\<close>
        = PCap\<^sup>\<ge>                                \<Rightarrow> \<open>\<lambda>c. tyOp (ttxt c) []\<close>
        | PLc\<^sup>\<ge>                                 \<Rightarrow> \<open>\<lambda>c. tyVar (ttxt c)\<close>
        | "("\<^sup>\<ge> ")"\<^sup>\<ge>                            \<Rightarrow> \<open>tyTup []\<close>
        | "("\<^sup>\<ge> TyList\<^sup>= ")"\<^sup>\<ge>                   \<Rightarrow> \<open>tup_ty\<close>
        | "["\<^sup>\<ge> Ty\<^sup>\<ge> "]"\<^sup>\<ge>                       \<Rightarrow> \<open>\<lambda>t. tyOp ''[]'' [t]\<close>
    and
      TyList :: \<open>tyAST list\<close>
        = Ty\<^sup>\<ge>                                  \<Rightarrow> \<open>\<lambda>t. [t]\<close>
        | TyList\<^sup>= ","\<^sup>\<ge> Ty\<^sup>\<ge>                    \<Rightarrow> \<open>\<lambda>ts t. t # ts\<close>
    and
      TyApp :: \<open>tyAST\<close>
        = PCap\<^sup>\<ge> TyBases\<^sup>=                      \<Rightarrow> \<open>\<lambda>c ts. tyOp (ttxt c) (rev ts)\<close>
        | TyBase\<^sup>\<ge>                              \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      Ty :: \<open>tyAST\<close>
        = TyArr\<^sup>=                                \<Rightarrow> \<open>\<lambda>ts. mkFunTy (rev ts)\<close>
    and
      TyArr :: \<open>tyAST list\<close>
        = TyApp\<^sup>\<ge>                               \<Rightarrow> \<open>\<lambda>t. [t]\<close>
        | TyArr\<^sup>= "->"\<^sup>\<ge> TyApp\<^sup>\<ge>                 \<Rightarrow> \<open>\<lambda>ts t. t # ts\<close>
    and
      EqBindSeq :: \<open>expdecAST list option\<close>
        = "{"\<^sup>> "}"\<^sup>*                            \<Rightarrow> \<open>Some []\<close>
        | "{"\<^sup>> ";"\<^sup>* "}"\<^sup>*                       \<Rightarrow> \<open>None\<close>
        | "{"\<^sup>> FreeBinds\<^sup>* "}"\<^sup>*                 \<Rightarrow> \<open>orev\<close>
        | "{"\<^sup>> FreeBinds\<^sup>* ";"\<^sup>* "}"\<^sup>*            \<Rightarrow> \<open>orev\<close>
        | LBinds\<^sup>>                              \<Rightarrow> \<open>orev\<close>
    and
      FreeBinds :: \<open>expdecAST list option\<close>
        = FreeEqBind\<^sup>*                          \<Rightarrow> \<open>\<lambda>b. osnoc (Some []) b\<close>
        | FreeBinds\<^sup>* ";"\<^sup>* FreeEqBind\<^sup>*          \<Rightarrow> \<open>osnoc\<close>
    and
      LBinds :: \<open>expdecAST list option\<close>
        =                                       \<Rightarrow> \<open>Some []\<close>
        | LBinds\<^sup>= EqBind\<^sup>=                      \<Rightarrow> \<open>osnoc\<close>
    and
      FreeEqBind :: \<open>expdecAST option\<close>
        = Exp\<^sup>* "="\<^sup>* Exp\<^sup>*                      \<Rightarrow> \<open>act_eqbind\<close>
        | PLc\<^sup>* "::"\<^sup>* Ty\<^sup>*                      \<Rightarrow> \<open>\<lambda>x t. Some (expdecTysig (ttxt x) t)\<close>
    and
      EqBind :: \<open>expdecAST option\<close>
        = ExpEQ\<^sup>= "="\<^sup>> Exp\<^sup>>                    \<Rightarrow> \<open>act_eqbind\<close>
        | PLc\<^sup>= "::"\<^sup>> Ty\<^sup>>                     \<Rightarrow> \<open>\<lambda>x t. Some (expdecTysig (ttxt x) t)\<close>
    and
      Op :: \<open>string\<close>
        = PSym\<^sup>=                                \<Rightarrow> \<open>ttxt\<close>
        | "\<lambda>"\<^sup>=                                 \<Rightarrow> \<open>[CHR 0x5C]\<close>
        | "`"\<^sup>= AnyAlpha\<^sup>\<ge> "`"\<^sup>\<ge>                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      AnyAlpha :: \<open>string\<close>
        = PCap\<^sup>=                                \<Rightarrow> \<open>ttxt\<close>
        | PLc\<^sup>=                                 \<Rightarrow> \<open>ttxt\<close>
        | PAlpha\<^sup>=                              \<Rightarrow> \<open>ttxt\<close>
        | "data"\<^sup>=                              \<Rightarrow> \<open>''data''\<close>
        | "do"\<^sup>=                                \<Rightarrow> \<open>''do''\<close>
    and
      IExp :: \<open>expAST option\<close>
        = FExp\<^sup>= OpTail\<^sup>=                       \<Rightarrow> \<open>act_iexp\<close>
        | FExp\<^sup>= OpTail\<^sup>= Op\<^sup>> LSafe\<^sup>\<ge>            \<Rightarrow> \<open>act_iexp_last\<close>
    and
      OpTail :: \<open>pitem list option\<close>
        =                                       \<Rightarrow> \<open>Some []\<close>
        | OpTail\<^sup>= Op\<^sup>> FExp\<^sup>\<ge>                   \<Rightarrow> \<open>act_optail\<close>
    and
      IExpEQ :: \<open>expAST option\<close>
        = FExpEQ\<^sup>= OpTailGE\<^sup>=                   \<Rightarrow> \<open>act_iexp\<close>
        | FExpEQ\<^sup>= OpTailGE\<^sup>= Op\<^sup>\<ge> LSafe\<^sup>\<ge>        \<Rightarrow> \<open>act_iexp_last\<close>
    and
      OpTailGE :: \<open>pitem list option\<close>
        =                                       \<Rightarrow> \<open>Some []\<close>
        | OpTailGE\<^sup>= Op\<^sup>\<ge> FExp\<^sup>\<ge>                 \<Rightarrow> \<open>act_optail\<close>
    and
      FExp :: \<open>expAST option\<close>
        = AExp\<^sup>= Args\<^sup>=                         \<Rightarrow> \<open>act_fexp\<close>
    and
      FExpEQ :: \<open>expAST option\<close>
        = AExpEQ\<^sup>= Args\<^sup>=                       \<Rightarrow> \<open>act_fexp\<close>
    and
      Args :: \<open>expAST list option\<close>
        =                                       \<Rightarrow> \<open>Some []\<close>
        | Args\<^sup>= AExp\<^sup>=                          \<Rightarrow> \<open>osnoc\<close>
        | Args\<^sup>= "do"\<^sup>>                          \<Rightarrow> \<open>\<lambda>as. osnoc as (Some (mkSym ''do''))\<close>
    and
      Exp :: \<open>expAST option\<close>
        = LSafe\<^sup>=                               \<Rightarrow> \<open>\<lambda>e. e\<close>
        | IExp\<^sup>=                                \<Rightarrow> \<open>\<lambda>e. e\<close>
    and
      ExpEQ :: \<open>expAST option\<close>
        = LSafeEQ\<^sup>=                             \<Rightarrow> \<open>\<lambda>e. e\<close>
        | IExpEQ\<^sup>=                              \<Rightarrow> \<open>\<lambda>e. e\<close>
    and
      LSafe :: \<open>expAST option\<close>
        = "\<lambda>"\<^sup>> APats\<^sup>= "->"\<^sup>> Exp\<^sup>=             \<Rightarrow> \<open>act_lam\<close>
        | "if"\<^sup>> Exp\<^sup>= "then"\<^sup>> Exp\<^sup>= "else"\<^sup>> Exp\<^sup>= \<Rightarrow> \<open>act_if\<close>
        | "let"\<^sup>> EqBindSeq\<^sup>= "in"\<^sup>> Exp\<^sup>=       \<Rightarrow> \<open>act_let\<close>
        | "do"\<^sup>> DoBlock\<^sup>=                      \<Rightarrow> \<open>\<lambda>e. e\<close>
        | "case"\<^sup>> Exp\<^sup>= "of"\<^sup>> PatAlts\<^sup>>         \<Rightarrow> \<open>act_case\<close>
    and
      LSafeEQ :: \<open>expAST option\<close>
        = "\<lambda>"\<^sup>= APats\<^sup>= "->"\<^sup>> Exp\<^sup>=             \<Rightarrow> \<open>act_lam\<close>
        | "if"\<^sup>= Exp\<^sup>= "then"\<^sup>> Exp\<^sup>= "else"\<^sup>> Exp\<^sup>= \<Rightarrow> \<open>act_if\<close>
        | "let"\<^sup>= EqBindSeq\<^sup>= "in"\<^sup>> Exp\<^sup>=       \<Rightarrow> \<open>act_let\<close>
        | "do"\<^sup>= DoBlock\<^sup>>                      \<Rightarrow> \<open>\<lambda>e. e\<close>
        | "case"\<^sup>= Exp\<^sup>= "of"\<^sup>> PatAlts\<^sup>>         \<Rightarrow> \<open>act_case\<close>
    and
      APats :: \<open>patAST list\<close>
        = APat\<^sup>=                                \<Rightarrow> \<open>\<lambda>p. [p]\<close>
        | APats\<^sup>= APat\<^sup>=                         \<Rightarrow> \<open>\<lambda>ps p. p # ps\<close>
    and
      APat :: \<open>patAST\<close>
        = PLc\<^sup>>                                 \<Rightarrow> \<open>\<lambda>x. patVar (ttxt x)\<close>
        | Lit\<^sup>=                                 \<Rightarrow> \<open>patLit\<close>
        | "_"\<^sup>>                                 \<Rightarrow> \<open>patUScore\<close>
    and
      PatAlts :: \<open>(patAST \<times> expAST) list option\<close>
        =                                       \<Rightarrow> \<open>Some []\<close>
        | PatAlts\<^sup>= PatAlt\<^sup>=                     \<Rightarrow> \<open>osnoc\<close>
    and
      PatAlt :: \<open>(patAST \<times> expAST) option\<close>
        = ExpEQ\<^sup>= "->"\<^sup>> Exp\<^sup>>                   \<Rightarrow> \<open>act_patalt\<close>
    and
      DoBlock :: \<open>expAST option\<close>
        = "{"\<^sup>> SeqE\<^sup>* "}"\<^sup>*                      \<Rightarrow> \<open>act_do\<close>
        | LinesE\<^sup>>                             \<Rightarrow> \<open>act_do\<close>
    and
      SeqE :: \<open>dosE\<close>
        = Exp\<^sup>=                                 \<Rightarrow> \<open>map_option (\<lambda>e. ([], e))\<close>
        | SeqE\<^sup>= ";"\<^sup>> Exp\<^sup>=                    \<Rightarrow> \<open>act_do_e\<close>
        | SeqN\<^sup>= ";"\<^sup>> Exp\<^sup>=                    \<Rightarrow> \<open>act_do_ne\<close>
    and
      SeqN :: \<open>dosN\<close>
        = DoBind\<^sup>=                              \<Rightarrow> \<open>\<lambda>s. osnoc (Some []) s\<close>
        | SeqE\<^sup>= ";"\<^sup>> DoBind\<^sup>=                 \<Rightarrow> \<open>act_do_en\<close>
        | SeqN\<^sup>= ";"\<^sup>> DoBind\<^sup>=                 \<Rightarrow> \<open>osnoc\<close>
    and
      LinesE :: \<open>dosE\<close>
        = ExpEQ\<^sup>=                               \<Rightarrow> \<open>map_option (\<lambda>e. ([], e))\<close>
        | LinesE\<^sup>= ExpEQ\<^sup>=                       \<Rightarrow> \<open>act_do_e\<close>
        | LinesN\<^sup>= ExpEQ\<^sup>=                       \<Rightarrow> \<open>act_do_ne\<close>
        | LinesE\<^sup>= ";"\<^sup>> Exp\<^sup>=                  \<Rightarrow> \<open>act_do_e\<close>
        | LinesN\<^sup>= ";"\<^sup>> Exp\<^sup>=                  \<Rightarrow> \<open>act_do_ne\<close>
    and
      LinesN :: \<open>dosN\<close>
        = DoBindEQ\<^sup>=                            \<Rightarrow> \<open>\<lambda>s. osnoc (Some []) s\<close>
        | LinesE\<^sup>= DoBindEQ\<^sup>=                     \<Rightarrow> \<open>act_do_en\<close>
        | LinesN\<^sup>= DoBindEQ\<^sup>=                     \<Rightarrow> \<open>osnoc\<close>
        | LinesE\<^sup>= ";"\<^sup>> DoBind\<^sup>=               \<Rightarrow> \<open>act_do_en\<close>
        | LinesN\<^sup>= ";"\<^sup>> DoBind\<^sup>=               \<Rightarrow> \<open>osnoc\<close>
    and
      DoBind :: \<open>expdostmtAST option\<close>
        = Exp\<^sup>= "<-"\<^sup>> Exp\<^sup>>                     \<Rightarrow> \<open>act_bind\<close>
        | "let"\<^sup>> LBinds\<^sup>>                      \<Rightarrow> \<open>\<lambda>ds. map_option (expdostmtLet \<circ> rev) ds\<close>
    and
      DoBindEQ :: \<open>expdostmtAST option\<close>
        = ExpEQ\<^sup>= "<-"\<^sup>> Exp\<^sup>>                   \<Rightarrow> \<open>act_bind\<close>
        | "let"\<^sup>= LBinds\<^sup>>                      \<Rightarrow> \<open>\<lambda>ds. map_option (expdostmtLet \<circ> rev) ds\<close>
    and
      AExp :: \<open>expAST option\<close>
        = Lit\<^sup>>                                 \<Rightarrow> \<open>\<lambda>l. Some (expLit l)\<close>
        | "("\<^sup>> ")"\<^sup>>                            \<Rightarrow> \<open>Some (expTup [])\<close>
        | "("\<^sup>> ExpList\<^sup>= ")"\<^sup>>                  \<Rightarrow> \<open>map_option paren_exp\<close>
        | "["\<^sup>> "]"\<^sup>>                            \<Rightarrow> \<open>Some (expCon ''[]'' [])\<close>
        | "["\<^sup>> ExpList\<^sup>= "]"\<^sup>>                  \<Rightarrow> \<open>map_option list_exp\<close>
        | Alpha\<^sup>>                               \<Rightarrow> \<open>\<lambda>a. Some (mkSym a)\<close>
        | "_"\<^sup>>                                 \<Rightarrow> \<open>Some (expVar ''_'')\<close>
        | PFFI\<^sup>>                                \<Rightarrow> \<open>\<lambda>t. Some (expOp (mkFFISym (ttxt t)) [])\<close>
    and
      AExpEQ :: \<open>expAST option\<close>
        = Lit\<^sup>=                                 \<Rightarrow> \<open>\<lambda>l. Some (expLit l)\<close>
        | "("\<^sup>= ")"\<^sup>>                            \<Rightarrow> \<open>Some (expTup [])\<close>
        | "("\<^sup>= ExpList\<^sup>= ")"\<^sup>>                  \<Rightarrow> \<open>map_option paren_exp\<close>
        | "["\<^sup>= "]"\<^sup>>                            \<Rightarrow> \<open>Some (expCon ''[]'' [])\<close>
        | "["\<^sup>= ExpList\<^sup>= "]"\<^sup>>                  \<Rightarrow> \<open>map_option list_exp\<close>
        | AlphaEQ\<^sup>=                             \<Rightarrow> \<open>\<lambda>a. Some (mkSym a)\<close>
        | "_"\<^sup>=                                 \<Rightarrow> \<open>Some (expVar ''_'')\<close>
        | PFFI\<^sup>=                                \<Rightarrow> \<open>\<lambda>t. Some (expOp (mkFFISym (ttxt t)) [])\<close>
    and
      ExpList :: \<open>expAST list option\<close>
        = Exp\<^sup>=                                 \<Rightarrow> \<open>\<lambda>e. osnoc (Some []) e\<close>
        | ExpList\<^sup>= ","\<^sup>> Exp\<^sup>=                 \<Rightarrow> \<open>osnoc\<close>
    and
      Alpha :: \<open>string\<close>
        = PCap\<^sup>=                                \<Rightarrow> \<open>ttxt\<close>
        | PLc\<^sup>=                                 \<Rightarrow> \<open>ttxt\<close>
        | PAlpha\<^sup>=                              \<Rightarrow> \<open>ttxt\<close>
        | "data"\<^sup>=                              \<Rightarrow> \<open>''data''\<close>
    and
      AlphaEQ :: \<open>string\<close>
        = PCap\<^sup>=                                \<Rightarrow> \<open>ttxt\<close>
        | PLc\<^sup>=                                 \<Rightarrow> \<open>ttxt\<close>
        | PAlpha\<^sup>=                              \<Rightarrow> \<open>ttxt\<close>
    and
      Lit :: \<open>litAST\<close>
        = PInt\<^sup>=                                \<Rightarrow> \<open>\<lambda>t. litInt (int_of_txt (ttxt t))\<close>
        | PStr\<^sup>=                                \<Rightarrow> \<open>\<lambda>t. litString (ttxt t)\<close>

parser pure_parse for pure

end
