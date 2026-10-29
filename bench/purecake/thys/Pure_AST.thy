theory Pure_AST
  imports Main
begin

section \<open>PureCake's surface AST and its CST-to-AST helpers\<close>

text \<open>A transcription of PureCake's \<open>pureAST\<close> and of the value-level helpers of \<open>cst_to_ast\<close>:
  the semantic actions of \<^theory_text>\<open>Pure_Grammar\<close> compute with these what \<open>cst_to_ast\<close>
  computes from the PEG's concrete syntax tree, so the two parsers can be compared on
  \<open>pureAST\<close> values. HOL4's \<open>string\<close> is \<^typ>\<open>string\<close>; \<open>OPT_MMAP f\<close> is \<open>those \<circ> map f\<close>.\<close>

subsection \<open>The AST\<close>

datatype tyAST = tyOp string \<open>tyAST list\<close> | tyVar string | tyTup \<open>tyAST list\<close>

datatype litAST = litInt int | litString string

datatype patAST =
    patVar string
  | patApp string \<open>patAST list\<close>
  | patTup \<open>patAST list\<close>
  | patLit litAST
  | patUScore

text \<open>The atoms of \<open>pure_config\<close> that the parser can produce: \<open>mkFFISym\<close> is their only source.\<close>

datatype atom_op =
    Len | Elem | Concat | Implode | Substring
  | StrEq | StrLt | StrLeq | StrGt | StrGeq
  | Message string

datatype expAST =
    expVar string
  | expCon string \<open>expAST list\<close>
  | expOp atom_op \<open>expAST list\<close>
  | expTup \<open>expAST list\<close>
  | expApp expAST expAST
  | expAbs patAST expAST
  | expIf expAST expAST expAST
  | expLit litAST
  | expLet \<open>expdecAST list\<close> expAST
  | expDo \<open>expdostmtAST list\<close> expAST
  | expCase expAST \<open>(patAST \<times> expAST) list\<close>
and expdecAST =
    expdecTysig string tyAST
  | expdecPatbind patAST expAST
  | expdecFunbind string \<open>patAST list\<close> expAST
and expdostmtAST =
    expdostmtExp expAST
  | expdostmtBind patAST expAST
  | expdostmtLet \<open>expdecAST list\<close>

datatype declAST =
    declTysig string tyAST
  | declData string \<open>string list\<close> \<open>(string \<times> tyAST list) list\<close>
  | declFunbind string \<open>patAST list\<close> expAST
  | declPatbind patAST expAST

subsection \<open>Characters and names\<close>

text \<open>HOL4's \<open>isUpper\<close>/\<open>isLower\<close>/\<open>isAlpha\<close> are ASCII.\<close>

definition isUpper :: \<open>char \<Rightarrow> bool\<close> where
  \<open>isUpper c \<longleftrightarrow> (let n = of_char c :: nat in 65 \<le> n \<and> n \<le> 90)\<close>

definition isLower :: \<open>char \<Rightarrow> bool\<close> where
  \<open>isLower c \<longleftrightarrow> (let n = of_char c :: nat in 97 \<le> n \<and> n \<le> 122)\<close>

definition isAlpha :: \<open>char \<Rightarrow> bool\<close> where
  \<open>isAlpha c \<longleftrightarrow> isUpper c \<or> isLower c\<close>

definition mkSym :: \<open>string \<Rightarrow> expAST\<close> where
  \<open>mkSym s = (case s of
     [] \<Rightarrow> expVar s
   | c # _ \<Rightarrow>
       if isUpper c then expCon s []
       else if isAlpha c \<or> c \<noteq> CHR '':'' then expVar s
       else if s = '':'' then expCon ''::'' []
       else expCon s [])\<close>

definition mkFFISym :: \<open>string \<Rightarrow> atom_op\<close> where
  \<open>mkFFISym s =
    (if s = ''__Len'' then Len
     else if s = ''__Elem'' then Elem
     else if s = ''__Concat'' then Concat
     else if s = ''__Implode'' then Implode
     else if s = ''__Substring'' then Substring
     else if s = ''__StrEq'' then StrEq
     else if s = ''__StrLt'' then StrLt
     else if s = ''__StrLeq'' then StrLeq
     else if s = ''__StrGt'' then StrGt
     else if s = ''__StrGeq'' then StrGeq
     else Message s)\<close>

fun mkApp :: \<open>expAST \<Rightarrow> expAST list \<Rightarrow> expAST\<close> where
  \<open>mkApp (expCon s args0) args = expCon s (args0 @ args)\<close>
| \<open>mkApp (expOp p args0) args = expOp p (args0 @ args)\<close>
| \<open>mkApp f args = foldl expApp f args\<close>

fun mkFunTy :: \<open>tyAST list \<Rightarrow> tyAST\<close> where
  \<open>mkFunTy [] = tyOp ''Bool'' []\<close>
| \<open>mkFunTy [ty] = ty\<close>
| \<open>mkFunTy (ty # rest) = tyOp ''Fun'' [ty, mkFunTy rest]\<close>

subsection \<open>Operator precedence (HOL4's \<open>precparser\<close> instantiated by \<open>handlePrecs\<close>)\<close>

datatype associativity = Left | Right | NonAssoc

text \<open>Table 4.1 of the Haskell 2010 report, as in \<open>cst_to_ast\<close>; any other operator is \<open>(9, Left)\<close>.\<close>

definition prec_table :: \<open>(string \<times> nat \<times> associativity) list\<close> where
  \<open>prec_table = [
    (''!!'', 10, Left), (''.'', 9, Right), (''^'', 8, Right), (''^^'', 8, Right),
    (''**'', 8, Right), (''*'', 7, Left), (''/'', 7, Left), (''mod'', 7, Left),
    (''div'', 7, Left), (''quot'', 7, Left), (''rem'', 7, Left), (''+'', 6, Left),
    (''-'', 6, Left), ('':'', 5, Right), (''++'', 5, Right), (''=='', 4, NonAssoc),
    (''elem'', 4, NonAssoc), (''notElem'', 4, NonAssoc), (''/='', 4, NonAssoc),
    (''<'', 4, NonAssoc), (''<='', 4, NonAssoc), (''>'', 4, NonAssoc), (''>='', 4, NonAssoc),
    (''&&'', 3, Right), (''||'', 2, Right), (''>>'', 1, Left), (''>>='', 1, Left),
    (''$'', 0, Right), (''seq'', 0, Right), (''$!'', 0, Right)]\<close>

definition tokprec :: \<open>string \<Rightarrow> nat \<times> associativity\<close> where
  \<open>tokprec s = (case map_of prec_table s of Some r \<Rightarrow> r | None \<Rightarrow> (9, Left))\<close>

datatype tokrel = Reduce | Shift

type_synonym pitem = \<open>string + expAST\<close>

fun tok_action :: \<open>pitem \<times> pitem \<Rightarrow> tokrel option\<close> where
  \<open>tok_action (Inl stk, Inl inp) =
    (case (tokprec stk, tokprec inp) of ((sp, sa), (ip, ia)) \<Rightarrow>
       if ip < sp then Some Reduce
       else if sp < ip then Some Shift
       else if sa \<noteq> ia \<or> sa = NonAssoc then None
       else if sa = Left then Some Reduce
       else Some Shift)\<close>
| \<open>tok_action _ = None\<close>

fun str_OUTL :: \<open>pitem \<Rightarrow> string\<close> where
  \<open>str_OUTL (Inl x) = x\<close>
| \<open>str_OUTL _ = ''''\<close>

fun ast_OUTR :: \<open>pitem \<Rightarrow> expAST\<close> where
  \<open>ast_OUTR (Inr x) = x\<close>
| \<open>ast_OUTR _ = expTup []\<close>

definition preduce :: \<open>expAST \<Rightarrow> pitem \<Rightarrow> expAST \<Rightarrow> expAST\<close> where
  \<open>preduce a1 opn a2 = mkApp (mkSym (str_OUTL opn)) [a1, a2]\<close>

type_synonym pstack = \<open>(pitem + expAST) list\<close>

definition precparse1 :: \<open>pstack \<times> pitem list \<Rightarrow> (pstack \<times> pitem list) option\<close> where
  \<open>precparse1 c = (case c of
     (stk, []) \<Rightarrow>
       (case stk of
          Inr tm2 # Inl opn # Inr tm1 # rest \<Rightarrow> Some (Inr (preduce tm1 opn tm2) # rest, [])
        | _ \<Rightarrow> None)
   | (stk, tk # strm_rest) \<Rightarrow>
       if isl tk then
         (case stk of
            Inr tm2 # Inl opn # Inr tm1 # stk_rest \<Rightarrow>
              (case tok_action (opn, tk) of
                 Some Shift \<Rightarrow> Some (Inl tk # stk, strm_rest)
               | Some Reduce \<Rightarrow> Some (Inr (preduce tm1 opn tm2) # stk_rest, tk # strm_rest)
               | None \<Rightarrow> None)
          | [Inr tm] \<Rightarrow> Some ([Inl tk, Inr tm], strm_rest)
          | _ \<Rightarrow> None)
       else
         (case stk of
            [] \<Rightarrow> Some ([Inr (ast_OUTR tk)], strm_rest)
          | Inr ftm # stk_rest \<Rightarrow> Some (Inr (expApp ftm (ast_OUTR tk)) # stk_rest, strm_rest)
          | Inl _ # _ \<Rightarrow> Some (Inr (ast_OUTR tk) # stk, strm_rest)))\<close>

text \<open>HOL4's \<open>precparse\<close> is well-founded on the stream and stack lengths; every step
  decreases \<open>3 * |strm| + |stk|\<close>, so that much fuel never runs out first.\<close>

fun precparse :: \<open>nat \<Rightarrow> pstack \<times> pitem list \<Rightarrow> expAST option\<close> where
  \<open>precparse n (stk, strm) =
    (case (stk, strm) of
       ([Inr tm], []) \<Rightarrow> Some tm
     | _ \<Rightarrow>
       (case n of
          0 \<Rightarrow> None
        | Suc m \<Rightarrow> (case precparse1 (stk, strm) of None \<Rightarrow> None | Some c \<Rightarrow> precparse m c)))\<close>

definition handlePrecs :: \<open>pitem list \<Rightarrow> expAST option\<close> where
  \<open>handlePrecs xs = precparse (3 * length xs + 1) ([], xs)\<close>

subsection \<open>Expressions read as patterns and declarations\<close>

fun exp_to_pat :: \<open>expAST \<Rightarrow> patAST option\<close> where
  \<open>exp_to_pat (expVar s) = Some (if s = ''_'' then patUScore else patVar s)\<close>
| \<open>exp_to_pat (expCon s es) = map_option (patApp s) (those (map exp_to_pat es))\<close>
| \<open>exp_to_pat (expTup es) = map_option patTup (those (map exp_to_pat es))\<close>
| \<open>exp_to_pat (expLit l) = Some (patLit l)\<close>
| \<open>exp_to_pat _ = None\<close>

fun strip_comb :: \<open>expAST \<Rightarrow> expAST \<times> expAST list\<close> where
  \<open>strip_comb (expApp f x) = (case strip_comb f of (h, l) \<Rightarrow> (h, l @ [x]))\<close>
| \<open>strip_comb e = (e, [])\<close>

datatype resolve_decl = resolve_declPattern patAST | resolve_declFun string \<open>patAST list\<close>

definition resolve_decl :: \<open>expAST \<Rightarrow> resolve_decl option\<close> where
  \<open>resolve_decl e = (case exp_to_pat e of
     Some (patVar s) \<Rightarrow> Some (resolve_declFun s [])
   | Some p \<Rightarrow> Some (resolve_declPattern p)
   | None \<Rightarrow>
       (case strip_comb e of
          (expVar fname, args) \<Rightarrow> map_option (resolve_declFun fname) (those (map exp_to_pat args))
        | _ \<Rightarrow> None))\<close>

definition astFunPatBindf :: \<open>expAST \<Rightarrow> (expAST \<Rightarrow> declAST) option\<close> where
  \<open>astFunPatBindf e = (case exp_to_pat e of
     Some p \<Rightarrow> Some (declPatbind p)
   | None \<Rightarrow>
       (case strip_comb e of
          (expVar fnm, args) \<Rightarrow> map_option (declFunbind fnm) (those (map exp_to_pat args))
        | _ \<Rightarrow> None))\<close>

end
