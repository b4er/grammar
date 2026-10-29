theory Pure_Bench
  imports Pure_Grammar "HOL-Library.Code_Target_Numeral"
begin

section \<open>Benchmark and differential-testing harness\<close>

text \<open>The parser reads the token stream that PureCake's own lexer produces (dumped by the
  CakeML program \<open>purebench tokens\<close>): one token per line, its class, row, column and
  payload. \<^text>\<open>mk_tok\<close> builds a parser token from those fields; the printers produce
  exactly the S-expressions of \<open>purebench ast\<close>, so the two outputs compare byte for
  byte.\<close>

subsection \<open>Tokens\<close>

definition class_of :: \<open>String.literal \<Rightarrow> ptok\<close> where
  \<open>class_of s =
    (if s = STR ''PLpar'' then PLpar else if s = STR ''PRpar'' then PRpar
     else if s = STR ''PComma'' then PComma else if s = STR ''PSemi'' then PSemi
     else if s = STR ''PEquals'' then PEquals else if s = STR ''PLbrack'' then PLbrack
     else if s = STR ''PRbrack'' then PRbrack else if s = STR ''PLbrace'' then PLbrace
     else if s = STR ''PRbrace'' then PRbrace else if s = STR ''PBar'' then PBar
     else if s = STR ''PUnder'' then PUnder else if s = STR ''PCase'' then PCase
     else if s = STR ''PElse'' then PElse else if s = STR ''PIf'' then PIf
     else if s = STR ''PIn'' then PIn else if s = STR ''PLet'' then PLet
     else if s = STR ''POf'' then POf else if s = STR ''PThen'' then PThen
     else if s = STR ''PCap'' then PCap else if s = STR ''PLc'' then PLc
     else if s = STR ''PAlpha'' then PAlpha else if s = STR ''PData'' then PData
     else if s = STR ''PDo'' then PDo else if s = STR ''PDColon'' then PDColon
     else if s = STR ''PArrow'' then PArrow else if s = STR ''PLArrow'' then PLArrow
     else if s = STR ''PBacktick'' then PBacktick else if s = STR ''PBackslash'' then PBackslash
     else if s = STR ''PSym'' then PSym else if s = STR ''PInt'' then PInt
     else if s = STR ''PStr'' then PStr else if s = STR ''PFFI'' then PFFI
     else POther)\<close>

definition mk_tok :: \<open>String.literal \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> String.literal \<Rightarrow> ptoken\<close> where
  \<open>mk_tok c r k p = \<lparr>tok = class_of c,
     span = span.make (nat_of_integer r) (nat_of_integer k) 0 0 (String.explode p)\<rparr>\<close>

subsection \<open>Printers\<close>

fun digits :: \<open>nat \<Rightarrow> string\<close> where
  \<open>digits n = (if n < 10 then [char_of (48 + n)] else digits (n div 10) @ [char_of (48 + n mod 10)])\<close>

declare digits.simps [simp del]

definition pr_num :: \<open>int \<Rightarrow> string\<close> where
  \<open>pr_num i = (if i < 0 then CHR ''-'' # digits (nat (- i)) else digits (nat i))\<close>

definition qchar :: \<open>char \<Rightarrow> string\<close> where
  \<open>qchar c =
    (if c = CHR 0x22 then [CHR 0x5C, CHR 0x22]
     else if c = CHR 0x5C then [CHR 0x5C, CHR 0x5C]
     else if of_char c < (32::nat) \<or> (126::nat) < of_char c
       then CHR 0x5C # pr_num (of_char c) @ '';''
     else [c])\<close>

definition qstr :: \<open>string \<Rightarrow> string\<close> where
  \<open>qstr s = CHR 0x22 # concat (map qchar s) @ [CHR 0x22]\<close>

fun pr_lit :: \<open>litAST \<Rightarrow> string\<close> where
  \<open>pr_lit (litInt i) = ''(int '' @ pr_num i @ '')''\<close>
| \<open>pr_lit (litString s) = ''(str '' @ qstr s @ '')''\<close>

fun pr_ty :: \<open>tyAST \<Rightarrow> string\<close> and pr_tys :: \<open>tyAST list \<Rightarrow> string\<close> where
  \<open>pr_ty (tyOp s ts) = ''(op '' @ qstr s @ pr_tys ts @ '')''\<close>
| \<open>pr_ty (tyVar s) = ''(var '' @ qstr s @ '')''\<close>
| \<open>pr_ty (tyTup ts) = ''(tup'' @ pr_tys ts @ '')''\<close>
| \<open>pr_tys [] = ''''\<close>
| \<open>pr_tys (t # ts) = '' '' @ pr_ty t @ pr_tys ts\<close>

fun pr_pat :: \<open>patAST \<Rightarrow> string\<close> and pr_pats :: \<open>patAST list \<Rightarrow> string\<close> where
  \<open>pr_pat (patVar s) = ''(pvar '' @ qstr s @ '')''\<close>
| \<open>pr_pat (patApp s ps) = ''(papp '' @ qstr s @ pr_pats ps @ '')''\<close>
| \<open>pr_pat (patTup ps) = ''(ptup'' @ pr_pats ps @ '')''\<close>
| \<open>pr_pat (patLit l) = ''(plit '' @ pr_lit l @ '')''\<close>
| \<open>pr_pat patUScore = ''(wild)''\<close>
| \<open>pr_pats [] = ''''\<close>
| \<open>pr_pats (p # ps) = '' '' @ pr_pat p @ pr_pats ps\<close>

fun pr_op :: \<open>atom_op \<Rightarrow> string\<close> where
  \<open>pr_op Len = ''Len''\<close> | \<open>pr_op Elem = ''Elem''\<close> | \<open>pr_op Concat = ''Concat''\<close>
| \<open>pr_op Implode = ''Implode''\<close> | \<open>pr_op Substring = ''Substring''\<close>
| \<open>pr_op StrEq = ''StrEq''\<close> | \<open>pr_op StrLt = ''StrLt''\<close> | \<open>pr_op StrLeq = ''StrLeq''\<close>
| \<open>pr_op StrGt = ''StrGt''\<close> | \<open>pr_op StrGeq = ''StrGeq''\<close>
| \<open>pr_op (Message s) = ''(msg '' @ qstr s @ '')''\<close>

fun pr_exp :: \<open>expAST \<Rightarrow> string\<close>
  and pr_exps :: \<open>expAST list \<Rightarrow> string\<close>
  and pr_alts :: \<open>(patAST \<times> expAST) list \<Rightarrow> string\<close>
  and pr_decs :: \<open>expdecAST list \<Rightarrow> string\<close>
  and pr_dec :: \<open>expdecAST \<Rightarrow> string\<close>
  and pr_stmts :: \<open>expdostmtAST list \<Rightarrow> string\<close>
  and pr_stmt :: \<open>expdostmtAST \<Rightarrow> string\<close> where
  \<open>pr_exp (expVar s) = ''(var '' @ qstr s @ '')''\<close>
| \<open>pr_exp (expCon s es) = ''(con '' @ qstr s @ pr_exps es @ '')''\<close>
| \<open>pr_exp (expOp p es) = ''(prim '' @ pr_op p @ pr_exps es @ '')''\<close>
| \<open>pr_exp (expTup es) = ''(tup'' @ pr_exps es @ '')''\<close>
| \<open>pr_exp (expApp f x) = ''(app '' @ pr_exp f @ '' '' @ pr_exp x @ '')''\<close>
| \<open>pr_exp (expAbs p e) = ''(abs '' @ pr_pat p @ '' '' @ pr_exp e @ '')''\<close>
| \<open>pr_exp (expIf a b c) = ''(if '' @ pr_exp a @ '' '' @ pr_exp b @ '' '' @ pr_exp c @ '')''\<close>
| \<open>pr_exp (expLit l) = ''(lit '' @ pr_lit l @ '')''\<close>
| \<open>pr_exp (expLet ds e) = ''(let ('' @ pr_decs ds @ '') '' @ pr_exp e @ '')''\<close>
| \<open>pr_exp (expDo ss e) = ''(do ('' @ pr_stmts ss @ '') '' @ pr_exp e @ '')''\<close>
| \<open>pr_exp (expCase e as) = ''(case '' @ pr_exp e @ '' ('' @ pr_alts as @ ''))''\<close>
| \<open>pr_exps [] = ''''\<close>
| \<open>pr_exps (e # es) = '' '' @ pr_exp e @ pr_exps es\<close>
| \<open>pr_alts [] = ''''\<close>
| \<open>pr_alts ((p, e) # rest) = ''('' @ pr_pat p @ '' '' @ pr_exp e @ '')'' @ pr_alts rest\<close>
| \<open>pr_decs [] = ''''\<close>
| \<open>pr_decs (d # ds) = pr_dec d @ pr_decs ds\<close>
| \<open>pr_dec (expdecTysig s t) = ''(tysig '' @ qstr s @ '' '' @ pr_ty t @ '')''\<close>
| \<open>pr_dec (expdecPatbind p e) = ''(patbind '' @ pr_pat p @ '' '' @ pr_exp e @ '')''\<close>
| \<open>pr_dec (expdecFunbind s ps e) =
    ''(funbind '' @ qstr s @ '' ('' @ pr_pats ps @ '') '' @ pr_exp e @ '')''\<close>
| \<open>pr_stmts [] = ''''\<close>
| \<open>pr_stmts (s # ss) = pr_stmt s @ pr_stmts ss\<close>
| \<open>pr_stmt (expdostmtExp e) = ''(exp '' @ pr_exp e @ '')''\<close>
| \<open>pr_stmt (expdostmtBind p e) = ''(bind '' @ pr_pat p @ '' '' @ pr_exp e @ '')''\<close>
| \<open>pr_stmt (expdostmtLet ds) = ''(let ('' @ pr_decs ds @ ''))''\<close>

fun pr_strs :: \<open>string list \<Rightarrow> string\<close> where
  \<open>pr_strs [] = ''''\<close>
| \<open>pr_strs (s # ss) = '' '' @ qstr s @ pr_strs ss\<close>

fun pr_cons :: \<open>(string \<times> tyAST list) list \<Rightarrow> string\<close> where
  \<open>pr_cons [] = ''''\<close>
| \<open>pr_cons ((c, ts) # rest) = ''('' @ qstr c @ pr_tys ts @ '')'' @ pr_cons rest\<close>

fun pr_decl :: \<open>declAST \<Rightarrow> string\<close> where
  \<open>pr_decl (declTysig s t) = ''(tysig '' @ qstr s @ '' '' @ pr_ty t @ '')''\<close>
| \<open>pr_decl (declData s args cs) =
    ''(data '' @ qstr s @ '' ('' @ pr_strs args @ '') ('' @ pr_cons cs @ ''))''\<close>
| \<open>pr_decl (declFunbind s ps e) =
    ''(funbind '' @ qstr s @ '' ('' @ pr_pats ps @ '') '' @ pr_exp e @ '')''\<close>
| \<open>pr_decl (declPatbind p e) = ''(patbind '' @ pr_pat p @ '' '' @ pr_exp e @ '')''\<close>

definition nl :: string where \<open>nl = [CHR 0x0A]\<close>

definition pr_result :: \<open>declAST list option option \<Rightarrow> String.literal\<close> where
  \<open>pr_result r = String.implode (case r of
     None \<Rightarrow> ''NOPARSE'' @ nl
   | Some None \<Rightarrow> ''NOAST'' @ nl
   | Some (Some ds) \<Rightarrow> ''(decls'' @ concat (map (\<lambda>d. nl @ '' '' @ pr_decl d) ds) @ '')'' @ nl)\<close>

subsection \<open>Entry points\<close>

definition bench_ast :: \<open>ptoken list \<Rightarrow> String.literal\<close> where
  \<open>bench_ast ts = pr_result (pure_parse ts)\<close>

definition bench_ok :: \<open>ptoken list \<Rightarrow> integer\<close> where
  \<open>bench_ok ts = (case pure_parse ts of None \<Rightarrow> 0 | Some None \<Rightarrow> 1 | Some (Some _) \<Rightarrow> 2)\<close>

export_code mk_tok bench_ast bench_ok in SML module_name Pure_Bench
  file_prefix pure_bench

end
