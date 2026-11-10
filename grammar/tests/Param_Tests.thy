theory Param_Tests
  imports TIGER_LR.LR_Prec_Parse Parser_Check
begin

section \<open>Templates and operators\<close>

text \<open>Templates \<open>P(X, \<dots>)\<close> and the operators \<open>* + ?\<close> desugar to ordinary nonterminals
  before elaboration (\<^file>\<open>../grammar_expand.ML\<close>): nothing new in HOL. The tests
  compare each against the grammar written by hand.\<close>

fun toks :: \<open>nat \<Rightarrow> 'tok list \<Rightarrow> ('tok, unit) token list\<close> where
  \<open>toks i [] = []\<close>
| \<open>toks i (x # xs) = \<lparr>tok = x, span = span.make 0 i i 1 []\<rparr> # toks (Suc (Suc i)) xs\<close>

datatype p_tok = PId | PSemi | PComma | PLB | PRB | PKw

ML \<open>
  (* terminals by token value, so that two grammars compare *)
  fun prods_of thy g =
    let
      val gr = the (Grammar_Common.get_grammar_global thy (Sign.full_bname thy g));
      fun sym (Grammar_Common.RN n) = "N " ^ n
        | sym (Grammar_Common.RC i) = "C " ^ Syntax.string_of_term_global thy (Vector.sub (#terminals gr, i))
        | sym (Grammar_Common.RT i) = "T " ^ Syntax.string_of_term_global thy (Vector.sub (#terminals gr, i));
    in map (fn {lhs, rhs, ...} => (lhs, map (fn (s, a) => (sym s, a)) rhs)) (#prods gr) end;
  fun nts_of thy g =
    Grammar_Common.nonterms_list
      (the (Grammar_Common.get_grammar_global thy (Sign.full_bname thy g)))
    |> map (fn (n, {binding, carrier, ...}) => (n, Binding.name_of binding, carrier));
  fun insensitive thy g =
    Grammar_Defs.is_indent_insensitive
      (the (Grammar_Common.get_grammar_global thy (Sign.full_bname thy g)));
\<close>


subsection \<open>Operators\<close>

grammar (relation) pstar =
  tokens \<open>p_tok\<close>
  terminals ";" = \<open>PSemi\<close>
  productions
    S :: \<open>nat list\<close> = (PId ";")* \<Rightarrow> \<open>map (\<lambda>_. 1)\<close>

grammar (relation) pstar_hand =
  tokens \<open>p_tok\<close>
  terminals ";" = \<open>PSemi\<close>
  productions
    S :: \<open>nat list\<close> = L \<Rightarrow> \<open>map (\<lambda>_. 1)\<close>
  and
    L :: \<open>(p_tok, unit) token list\<close> = \<Rightarrow> \<open>[]\<close> | L PId ";" \<Rightarrow> \<open>\<lambda>xs x1. xs @ [x1]\<close>

lemma \<open>pstar =
  is_cfg.make
   [(''S'', [(Nt ''(PId ;)*'', Any)]),
    (''(PId ;)*'', []),
    (''(PId ;)*'', [(Nt ''(PId ;)*'', Any), (Tm PId, Any), (Tm PSemi, Any)])]
   ''S'' 0\<close>
  by (simp only: pstar_def)

ML \<open>
  \<^assert> ((nts_of \<^theory> "pstar" |> map #2) = ["S", "S_1"]);
  \<^assert> (insensitive \<^theory> "pstar");
\<close>

parser pstar_parse for pstar

parser_check \<open>pstar_parse (toks 0 [PId, PSemi, PId, PSemi]) = Some [1, 1]\<close>
parser_check \<open>pstar_parse [] = Some []\<close>
parser_check \<open>pstar_parse (toks 0 [PId]) = None\<close>

text \<open>\<open>+\<close> and \<open>?\<close> over one nonterminal; \<open>";"?\<close> binds nothing.\<close>

grammar (relation) popt =
  tokens \<open>p_tok\<close>
  terminals ";" = \<open>PSemi\<close> and "," = \<open>PComma\<close>
  productions
    S :: \<open>(nat list \<times> nat option)\<close> = I+ ";"? J? \<Rightarrow> \<open>Pair\<close>
  and
    I :: \<open>nat\<close> = PId \<Rightarrow> \<open>\<lambda>_. 1\<close> | PId "," \<Rightarrow> \<open>\<lambda>_. 2\<close>
  and
    J :: \<open>nat\<close> = PKw \<Rightarrow> \<open>\<lambda>_. 3\<close>

ML \<open>
  \<^assert> ((nts_of \<^theory> "popt" |> map #2) = ["S", "I", "J", "I_list1", "S_1", "J_opt"]);
\<close>

thm popt_def

parser popt_parse for popt

parser_check \<open>popt_parse (toks 0 [PId, PId, PComma, PSemi, PKw]) = Some ([1, 2], Some 3)\<close>
parser_check \<open>popt_parse (toks 0 [PId, PSemi]) = Some ([1], None)\<close>
parser_check \<open>popt_parse (toks 0 [PId, PKw]) = Some ([1], Some 3)\<close>

text \<open>A group with two value symbols has the pair as its element.\<close>

grammar ppair =
  tokens \<open>p_tok\<close>
  terminals ";" = \<open>PSemi\<close>
  productions
    S :: \<open>(nat \<times> nat) list\<close> = (I ";" I)+
  and
    I :: \<open>nat\<close> = PId \<Rightarrow> \<open>\<lambda>_. 1\<close> | PKw \<Rightarrow> \<open>\<lambda>_. 2\<close>

parser ppair_parse for ppair

parser_check \<open>ppair_parse (toks 0 [PId, PSemi, PKw, PKw, PSemi, PId]) = Some [(1, 2), (2, 1)]\<close>


subsection \<open>Templates\<close>

text \<open>A block in braces or aligned, once as a template and once by hand
  (\<open>File\<close>/\<open>Decls\<close>/\<open>DItems\<close>).\<close>

grammar (relation) pblk =
  tokens \<open>p_tok\<close>
  terminals ";" = \<open>PSemi\<close> and "{" = \<open>PLB\<close> and "}" = \<open>PRB\<close>
  productions
    Block(X) :: \<open>'x list\<close>
      = (X\<^sup>=)+\<^sup>=
      | "{"\<^sup>= "}"\<^sup>> \<Rightarrow> \<open>[]\<close>
      | "{"\<^sup>= Sep1(X, ";") "}"\<^sup>>
      | "{"\<^sup>= Sep1(X, ";") ";" "}"\<^sup>>
  and
    File :: \<open>nat list\<close> = Block(Decl)
  and
    Decl :: \<open>nat\<close> = PId\<^sup>= \<Rightarrow> \<open>\<lambda>_. 1\<close> | PKw\<^sup>= Block(Decl)\<^sup>> \<Rightarrow> \<open>\<lambda>_ ds. sum_list ds\<close>

grammar (relation) pblk_hand =
  tokens \<open>p_tok\<close>
  terminals ";" = \<open>PSemi\<close> and "{" = \<open>PLB\<close> and "}" = \<open>PRB\<close>
  productions
    File :: \<open>nat list\<close> = Blk
  and
    Decl :: \<open>nat\<close> = PId\<^sup>= \<Rightarrow> \<open>\<lambda>_. 1\<close> | PKw\<^sup>= Blk\<^sup>> \<Rightarrow> \<open>\<lambda>_ ds. sum_list ds\<close>
  and
    Blk :: \<open>nat list\<close>
      = Decls\<^sup>=
      | "{"\<^sup>= "}"\<^sup>> \<Rightarrow> \<open>[]\<close>
      | "{"\<^sup>= DItems "}"\<^sup>>
      | "{"\<^sup>= DItems ";" "}"\<^sup>>
  and
    Decls :: \<open>nat list\<close> = Decl\<^sup>= \<Rightarrow> \<open>\<lambda>x1. [x1]\<close> | Decls\<^sup>= Decl\<^sup>= \<Rightarrow> \<open>\<lambda>xs x1. xs @ [x1]\<close>
  and
    DItems :: \<open>nat list\<close> = Decl \<Rightarrow> \<open>\<lambda>x. [x]\<close> | DItems ";" Decl \<Rightarrow> \<open>\<lambda>xs x. xs @ [x]\<close>

thm pblk_def

ML \<open>
  \<^assert> ((nts_of \<^theory> "pblk" |> map #1) =
    ["File", "Decl", "Block(Decl)", "Decl+", "Sep1(Decl, ;)"]);
  \<^assert> ((nts_of \<^theory> "pblk" |> map #2) =
    ["File", "Decl", "Block_Decl", "Decl_list1", "Sep1_Decl_x3B"]);
  (* the same productions as by hand, under a renaming *)
  val ren =
    AList.lookup (op =)
      [("File", "File"), ("Decl", "Decl"), ("Block(Decl)", "Blk"), ("Decl+", "Decls"),
       ("Sep1(Decl, ;)", "DItems")];
  fun rn (s, a) =
    if String.isPrefix "N " s then ("N " ^ the (ren (unprefix "N " s)), a) else (s, a);
  val ps = prods_of \<^theory> "pblk" |> map (fn (l, r) => (the (ren l), map rn r));
  val hs = prods_of \<^theory> "pblk_hand";
  \<^assert> (eq_set (op =) (ps, hs));
\<close>

parser pblk_parse for pblk
parser pblk_hand_parse for pblk_hand

definition \<open>w_brace = toks 0 [PLB, PId, PSemi, PKw, PLB, PId, PRB, PSemi, PRB]\<close>

parser_check \<open>pblk_parse w_brace = Some [1, 1]\<close>
parser_check \<open>pblk_hand_parse w_brace = Some [1, 1]\<close>

text \<open>Aligned: two declarations in column 0.\<close>

definition w_aligned :: \<open>(p_tok, unit) token list\<close> where \<open>w_aligned =
  [\<lparr>tok = PId, span = span.make 0 0 0 1 []\<rparr>, \<lparr>tok = PId, span = span.make 1 0 0 1 []\<rparr>]\<close>

parser_check \<open>pblk_parse w_aligned = Some [1, 1]\<close>
parser_check \<open>pblk_hand_parse w_aligned = Some [1, 1]\<close>

text \<open>The relation of an instance is the hand-written one.\<close>

term pblk_Block_Decl
thm pblk.intros


subsection \<open>The prelude\<close>

grammar plist =
  tokens \<open>p_tok\<close>
  terminals "," = \<open>PComma\<close> and ";" = \<open>PSemi\<close> and "{" = \<open>PLB\<close> and "}" = \<open>PRB\<close>
  productions
    S :: \<open>nat list list\<close> = "{" Sep(Sep1(I, ","), ";") "}"
  and
    I :: \<open>nat\<close> = PId \<Rightarrow> \<open>\<lambda>_. 1\<close> | PKw \<Rightarrow> \<open>\<lambda>_. 2\<close>

ML \<open>
  \<^assert> ((nts_of \<^theory> "plist" |> map #1) =
    ["S", "I", "Sep1(I, ,)", "Sep(Sep1(I, ,), ;)", "Sep1(Sep1(I, ,), ;)"]);
\<close>


subsection \<open>Layout\<close>

text \<open>\<open>(Stmt\<^sup>=)+\<close> is the aligned block written by hand: the recursive occurrence copies
  the annotation of the group's first symbol.\<close>

grammar (relation) psuite =
  tokens \<open>p_tok\<close>
  terminals ":" = \<open>PSemi\<close>
  productions
    Prog :: \<open>nat\<close> = (Stmt\<^sup>=)+ \<Rightarrow> \<open>sum_list\<close>
  and
    Stmt :: \<open>nat\<close> = PId\<^sup>= \<Rightarrow> \<open>\<lambda>_. 1\<close> | PKw\<^sup>= ":"\<^sup>> (Stmt\<^sup>=)+\<^sup>> \<Rightarrow> \<open>\<lambda>_ ns. sum_list ns + 1\<close>

grammar (relation) psuite_hand =
  tokens \<open>p_tok\<close>
  terminals ":" = \<open>PSemi\<close>
  productions
    Prog :: \<open>nat\<close> = Blk \<Rightarrow> \<open>sum_list\<close>
  and
    Stmt :: \<open>nat\<close> = PId\<^sup>= \<Rightarrow> \<open>\<lambda>_. 1\<close> | PKw\<^sup>= ":"\<^sup>> Blk\<^sup>> \<Rightarrow> \<open>\<lambda>_ ns. sum_list ns + 1\<close>
  and
    Blk :: \<open>nat list\<close> = Stmt\<^sup>= \<Rightarrow> \<open>\<lambda>x1. [x1]\<close> | Blk\<^sup>= Stmt\<^sup>= \<Rightarrow> \<open>\<lambda>xs x1. xs @ [x1]\<close>

ML \<open>
  val ren = AList.lookup (op =) [("Prog", "Prog"), ("Stmt", "Stmt"), ("Stmt+", "Blk")];
  fun rn (s, a) =
    if String.isPrefix "N " s then ("N " ^ the (ren (unprefix "N " s)), a) else (s, a);
  \<^assert> (eq_set (op =)
    (prods_of \<^theory> "psuite" |> map (fn (l, r) => (the (ren l), map rn r)),
     prods_of \<^theory> "psuite_hand"));
  \<^assert> (not (insensitive \<^theory> "psuite"));
  \<^assert> (insensitive \<^theory> "ppair");
\<close>

parser psuite_parse for psuite
parser psuite_hand_parse for psuite_hand

definition w_suite :: \<open>(p_tok, unit) token list\<close> where \<open>w_suite =
  [\<lparr>tok = PKw, span = span.make 0 0 0 1 []\<rparr>, \<lparr>tok = PSemi, span = span.make 0 1 1 1 []\<rparr>,
   \<lparr>tok = PId, span = span.make 1 2 2 1 []\<rparr>, \<lparr>tok = PId, span = span.make 2 2 2 1 []\<rparr>,
   \<lparr>tok = PId, span = span.make 3 0 0 1 []\<rparr>]\<close>

parser_check \<open>psuite_parse w_suite = Some 4\<close>
parser_check \<open>psuite_hand_parse w_suite = Some 4\<close>

text \<open>The parser's soundness for a grammar with instances, stated over the relation of
  the generated nonterminal's parent.\<close>

lemma \<open>psuite_parse w = Some n \<Longrightarrow> psuite_Prog 0 w n\<close>
  using psuite_parse.sound by blast


subsection \<open>Messages\<close>

parser (diagnostics) pstar_diag for pstar

parser_check \<open>(case pstar_diag_diag (toks 0 [PId, PId]) of
    Inl e \<Rightarrow> pmsg_lines (perr_message pstar_diag_info (\<lambda>_. []) e) | Inr _ \<Rightarrow> []) =
  [''0:2: syntax error at '' @ squote ''PId'',
   ''  expected: '' @ squote '';'']\<close>

text \<open>A generated list or option shows as its element in messages, a group as its first
  symbol (a terminal quoted, without article); an element and a list of it are listed once.
  After \<open>MKw\<close> the kernel has the dot before \<open>Item+\<close>, \<open>Item\<close> and \<open>(, Item)+\<close>.\<close>

datatype m_tok = MA | MB | MC | MD | ME | MF | MKw | MSemi | MComma

grammar pmsg =
  tokens \<open>m_tok\<close>
  terminals ";" = \<open>MSemi\<close> and "," = \<open>MComma\<close>
  productions
    S :: \<open>nat\<close>
      = MKw Item+ ";" \<Rightarrow> \<open>\<lambda>_ xs. length xs\<close>
      | MKw Item "," \<Rightarrow> \<open>\<lambda>_ _. 0\<close>
      | MKw ("," Item)+ ";" \<Rightarrow> \<open>\<lambda>_ xs. length xs\<close>
  and
    Item :: \<open>nat\<close>
      = MA \<Rightarrow> \<open>\<lambda>_. 1\<close> | MB \<Rightarrow> \<open>\<lambda>_. 1\<close> | MC \<Rightarrow> \<open>\<lambda>_. 1\<close>
      | MD \<Rightarrow> \<open>\<lambda>_. 1\<close> | ME \<Rightarrow> \<open>\<lambda>_. 1\<close> | MF \<Rightarrow> \<open>\<lambda>_. 1\<close>

parser (diagnostics) pmsg_diag for pmsg

parser_check \<open>(case pmsg_diag_diag (toks 0 [MKw, MSemi]) of
    Inl e \<Rightarrow> pmsg_lines (perr_message pmsg_diag_info (\<lambda>_. []) e) | Inr _ \<Rightarrow> []) =
  [''0:2: syntax error at '' @ squote '';'',
   ''  expected: an Item or '' @ squote '','']\<close>
  and \<open>(case pmsg_diag_diag (toks 0 [MKw, MA, MB, MComma]) of
    Inl e \<Rightarrow> pmsg_lines (perr_message pmsg_diag_info (\<lambda>_. []) e) | Inr _ \<Rightarrow> []) =
  [''0:6: syntax error at '' @ squote '','',
   ''  expected: an Item or '' @ squote '';'',
   ''  up to here: an Item was recognised'']\<close>
  and \<open>(case pmsg_diag_diag (toks 0 [MKw, MComma, MA, MComma, MA, MA]) of
    Inl e \<Rightarrow> pmsg_lines (perr_message pmsg_diag_info (\<lambda>_. []) e) | Inr _ \<Rightarrow> []) =
  [''0:10: syntax error at '' @ squote ''MA'',
   ''  expected: '' @ squote '';'' @ '' or '' @ squote '','',
   ''  up to here: an Item was recognised'']\<close>

text \<open>Under composition: a copied nonterminal in a list template of the prelude.\<close>

grammar pmsg_sep =
  tokens \<open>m_tok\<close>
  terminals ";" = \<open>MSemi\<close> and "," = \<open>MComma\<close>
  productions
    T :: \<open>nat\<close> = MKw Sep1(pmsg.Item, ",") ";"? \<Rightarrow> \<open>\<lambda>_ xs. length xs\<close>

ML \<open>
  \<^assert> ((nts_of \<^theory> "pmsg_sep" |> map #1) = ["T", "Sep1(pmsg.Item, ,)", ";?", "pmsg.Item"]);
\<close>

parser (diagnostics) pmsg_sep_diag for pmsg_sep

parser_check \<open>(case pmsg_sep_diag_diag (toks 0 [MKw, MSemi]) of
    Inl e \<Rightarrow> pmsg_lines (perr_message pmsg_sep_diag_info (\<lambda>_. []) e) | Inr _ \<Rightarrow> []) =
  [''0:2: syntax error at '' @ squote '';'', ''  expected: an Item'']\<close>

subsection \<open>Composition\<close>

text \<open>A reference to a grammar with instances copies them; a template of another grammar
  brings that grammar's nonterminals and spellings.\<close>

grammar (relation) pcomp =
  tokens \<open>p_tok\<close>
  productions
    Top :: \<open>nat list list\<close> = pblk.File+

ML \<open>
  \<^assert> ((nts_of \<^theory> "pcomp" |> map #1) =
    ["Top", "pblk.File+", "pblk.File", "pblk.Block(Decl)", "pblk.Decl+", "pblk.Decl",
     "pblk.Sep1(Decl, ;)"]);
  \<^assert> ((nts_of \<^theory> "pcomp" |> map #2) =
    ["Top", "pblk_File_list1", "pblk_File", "pblk_Block_Decl", "pblk_Decl_list1", "pblk_Decl",
     "pblk_Sep1_Decl_x3B"]);
\<close>

thm pcomp.pblk_File_iff

grammar ptmpl =
  tokens \<open>p_tok\<close>
  productions
    Top :: \<open>nat list\<close> = PKw pblk.Block(Item) \<Rightarrow> \<open>\<lambda>_ xs. xs\<close>
  and
    Item :: \<open>nat\<close> = PComma \<Rightarrow> \<open>\<lambda>_. 7\<close> | pblk.Decl\<^sup>=

ML \<open>
  \<^assert> ((nts_of \<^theory> "ptmpl" |> map #1) =
    ["Top", "Item", "Block(Item)", "Item+", "Sep1(Item, ;)", "pblk.Decl", "pblk.Block(Decl)",
     "pblk.Decl+", "pblk.Sep1(Decl, ;)"]);
\<close>

parser ptmpl_parse for ptmpl

parser_check \<open>ptmpl_parse (toks 0 [PKw, PLB, PComma, PSemi, PKw, PLB, PRB, PRB]) = Some [7, 0]\<close>


subsection \<open>Errors\<close>

ML \<open>
fun command_error src =
  let val thy = \<^theory> in
    (fold Toplevel.command_exception (Outer_Syntax.parse_text thy (K {skip_theory = false, theory = thy}) Position.none src)
       (Toplevel.make_state (SOME (Context.Theory thy))); NONE)
    handle Runtime.EXCURSION_FAIL (exn, _) => SOME (Runtime.exn_message exn)
  end;

fun rejected frag src =
  (case command_error src of
    NONE => error ("accepted: " ^ src)
  | SOME msg =>
      if String.isSubstring frag msg then () else error ("unexpected: " ^ msg));
\<close>

ML_val \<open>
  val _ = \<^assert> (is_none (command_error
    "grammar ok = tokens p_tok productions S :: \<open>nat list\<close> = List(I) and I :: nat = PId \<Rightarrow> \<open>\<lambda>_. 1\<close>"));
  val _ = rejected "Undefined template \"Lst\""
    "grammar bad = tokens p_tok productions S :: \<open>nat list\<close> = Lst(I) and I :: nat = PId \<Rightarrow> \<open>\<lambda>_. 1\<close>";
  val _ = rejected "has 2 parameter(s), applied to 1"
    "grammar bad = tokens p_tok productions S :: \<open>nat list\<close> = Sep(I) and I :: nat = PId \<Rightarrow> \<open>\<lambda>_. 1\<close>";
  val _ = rejected "An annotation of a group"
    "grammar bad = tokens p_tok productions S :: nat = (PId PId)\<^sup>= \<Rightarrow> \<open>\<lambda>_ _. 1\<close>";
  val _ = rejected "is not a template"
    "grammar bad = tokens p_tok productions P(X) :: nat = X(PId) | PId \<Rightarrow> \<open>\<lambda>_. 1\<close> and S :: nat = P(PId)";
  val _ = rejected "does not terminate"
    "grammar bad = tokens p_tok productions P(X) :: nat = P(List(X)) | PId \<Rightarrow> \<open>\<lambda>_. 1\<close> and S :: nat = P(PId)";
  val _ = rejected "parameter \"X\" twice"
    "grammar bad = tokens p_tok productions P(X, X) :: nat = PId \<Rightarrow> \<open>\<lambda>_. 1\<close> and S :: nat = P(PId, PId)";
  val _ = rejected "Carrier inference"
    "grammar bad = tokens p_tok productions S :: \<open>nat list\<close> = PId* \<Rightarrow> \<open>\<lambda>xs. xs\<close>";
  val _ = rejected "templates only; an option"
    "grammar (relation) bad = productions P(X) = X";
\<close>

end
