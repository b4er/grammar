(* Author: Basil Fürer *)

theory Same_Terms
  imports Regression_Tests Prec_Surface_Tests
begin

section \<open>The generated terms and theorems do not drift\<close>

text \<open>The guard for refactorings of the command layer: every fact that the
  \<^theory_text>\<open>grammar\<close> and \<^theory_text>\<open>parser\<close> commands emit for a few grammars of
  \<^file>\<open>Regression_Tests.thy\<close> and \<^file>\<open>Prec_Surface_Tests.thy\<close> is compared, as
  the SHA-1 of its exact internal term, against \<^file>\<open>same_terms.txt\<close>. A change that
  is meant (a new fact, a different encoding) is recorded by running this theory once with
  \<open>[[same_terms_update]]\<close> and committing the new file.\<close>

ML \<open>
structure Same_Terms =
struct

val update = Attrib.setup_config_bool \<^binding>\<open>same_terms_update\<close> (K false);

(* grammar or parser names, with the theory that defines them *)
val roots =
  [("Regression_Tests", ["do", "do_parse2", "toy", "toy_parse", "toy_parse_ty",
     "toy_parse_file", "lay", "lay_parse"]),
   ("Prec_Surface_Tests", ["ep", "ep_parse", "er", "er_parse"])];

fun owned thy_name roots name =
  (case try (unprefix (thy_name ^ ".")) name of
    NONE => false
  | SOME base =>
      exists (fn r => base = r ^ "_def" orelse
        exists (fn sep => String.isPrefix (r ^ sep) base) [".", "_", "__"]) roots
      andalso not (String.isSubstring "_tok." base));

fun entries thy =
  let
    val facts = Global_Theory.facts_of thy;
    fun of_thy (thy_name, rs) =
      Facts.fold_static (fn (n, _) => owned thy_name rs n ? cons n) facts [];
    val names = sort_strings (maps of_thy roots);
  in
    names |> maps (fn n =>
      map_index (fn (i, th) =>
          (n ^ "(" ^ string_of_int i ^ ")",
           (Message_Digest.rep (SHA1.digest (ML_Syntax.print_term (Thm.full_prop_of th))), th)))
        (Global_Theory.get_thms thy n))
  end;

fun render es = cat_lines (map (fn (k, (d, _)) => k ^ " " ^ d) es) ^ "\n";

fun parse text =
  split_lines text |> filter_out (fn l => l = "")
  |> map (fn l => (case space_explode " " l of [k, d] => (k, d)
       | _ => error ("same_terms.txt: bad line " ^ quote l)));

fun check ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val path = Path.append (Resources.master_directory thy) \<^path>\<open>same_terms.txt\<close>;
    val es = entries thy;
  in
    if Config.get ctxt update orelse not (File.exists path) then
      (File.write path (render es);
       warning ("same_terms: wrote " ^ string_of_int (length es) ^ " theorems to " ^
         Path.print path ^ "; commit it as the new reference"))
    else
      let
        val stored = parse (File.read path);
        val now = map (apsnd fst) es;
        val missing = filter_out (AList.defined (op =) now o fst) stored;
        val added = filter_out (AList.defined (op =) stored o fst) now;
        val changed =
          filter (fn (k, d) => (case AList.lookup (op =) stored k of
            SOME d' => d <> d' | NONE => false)) now;
        fun show (k, _) =
          k ^ ": " ^ Syntax.string_of_term ctxt
            (Thm.full_prop_of (snd (the (AList.lookup (op =) es k))));
      in
        if null missing andalso null added andalso null changed then
          writeln ("same_terms: " ^ string_of_int (length now) ^ " theorems unchanged")
        else
          error (cat_lines
            (["same_terms: the generated theorems drifted"] @
             map (fn (k, _) => "  missing: " ^ k) missing @
             map (fn (k, _) => "  added:   " ^ k) added @
             map (fn (k, _) => "  changed: " ^ k) changed @
             (case changed @ added of [] => [] | e :: _ => ["first of them now:", show e])))
      end
  end;

end;
\<close>

ML \<open>Same_Terms.check \<^context>\<close>

end
