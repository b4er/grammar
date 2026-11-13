(* Author: Basil Fürer *)

(* which states of an LR automaton can detect an error, each with a shortest sentence
   \<^cite>\<open>\<open>Sect.~3\<close> in "pottier2016-lr1-reachability"\<close>: the facts and edge facts of
   Fig.~4 by the algorithm of Fig.~5, with the filter of Sect.~3.4, then the Dijkstra
   of Sect.~3.5 over (state, lookahead).  Nothing here is proved, and nothing downstream
   depends on it but warnings and the skeleton of an errors block.

   The input is a plain view of the tables, so another backend only provides that view.
   The terminals are 0, ..., nterms - 1, and nterms is the end of the input, which has no
   transition.  A symbol is a terminal, or nterms + 1 + A for the nonterminal A.  A
   nondeterministic table is read as "may": a run takes any of the actions, which is what
   a layout grammar needs of the column-blind table. *)

signature LR_REACH =
sig
  type view =
   {nstates: int, nterms: int, nnts: int, start: int, finals: int list,
    trans: (int * int * int) list,          (* state, symbol, target *)
    prods: (int * int list) list,           (* nonterminal, symbols *)
    reds: (int * int * int) list}           (* state, production, lookahead *)

  type vertex = {state: int, look: int, dist: int, word: int list}

  type result =
   {complete: bool,                         (* false: the time ran out *)
    nodes: int, facts: int, edges: int,
    errors: vertex list,                    (* no action on the lookahead *)
    reached: vertex list}                   (* an action on it *)

  (* hide: a terminal no lexer produces; seconds: the budget *)
  val run: {hide: int option, seconds: real} -> view -> result

  (* the driver on terminals with their columns: [] for an accepted word, else the
     state, the terminal, the state after the last shift, the index of the token and
     the depth of the stack *)
  type driver = (int * int) list -> int list

  (* a sentence with its columns, NONE for the default layout *)
  type hit = {state: int, look: int, word: (int * int option) list}

  (* each target in the default layout; with columns also in every layout of its word up
     to the order of the columns, up to a number of runs per target.  Every error met on
     the way is a hit. *)
  val confirm: {driver: driver, nterms: int, widths: int vector, columns: bool, seconds: real} ->
    (int * int * int list) list -> hit list

  (* the anchors of the vector driver: per production the relation of each symbol (0 =,
     1 >, 2 >=, 3 any), per state its kernel (production, dot; the number of productions
     for the start item), and the reduce cells (state, production, dot, lookahead, wrel:
     0 =, 1 >=, 2 >, 3 <=, 4 <, 5 any) *)
  type anchors =
   {rels: int list list, kernels: (int * int) list list,
    cells: (int * int * int * int * int) list}

  (* which pairs of a state and a lookahead may fail on the columns: false only if no
     layout makes the vector driver stop there; NONE if the time ran out *)
  val column_errors: {seconds: real} -> view -> anchors -> (int * int -> bool) option
end;

(* the evaluation of the tables with the driver and the words of an errors block *)
structure LR_Reach_Cookie = Proof_Data
(
  type T = unit -> (int list list * (int list -> int list)) * int list list;
  fun init _ () = error "LR_Reach_Cookie";
);

structure LR_Reach: LR_REACH =
struct

type view =
 {nstates: int, nterms: int, nnts: int, start: int, finals: int list,
  trans: (int * int * int) list,
  prods: (int * int list) list,
  reds: (int * int * int) list};

type vertex = {state: int, look: int, dist: int, word: int list};

type result =
 {complete: bool,
  nodes: int, facts: int, edges: int,
  errors: vertex list,
  reached: vertex list};

(* sentences share their parts; a sentence of a fact is mostly a concatenation of two
   sentences that are already there.  Pottier hash-conses whole sentences
   \<^cite>\<open>\<open>Sect.~3.3\<close> in "pottier2016-lr1-reachability"\<close>; here they share as trees of
   concatenations *)
datatype sentence =
  Eps
| One of int
| App of int * int * sentence * sentence;   (* length, first terminal *)

fun len Eps = 0
  | len (One _) = 1
  | len (App (n, _, _, _)) = n;

fun first_of Eps z = z
  | first_of (One a) _ = a
  | first_of (App (_, a, _, _)) _ = a;

fun app Eps w = w
  | app w Eps = w
  | app u w = App (len u + len w, first_of u 0, u, w);

fun words s =
  let
    fun go Eps acc = acc
      | go (One a) acc = a :: acc
      | go (App (_, _, u, w)) acc = go u (go w acc);
  in go s [] end;

(* an integer map by open addressing: keys are nonnegative, values are lengths *)
structure Tab =
struct
  type T = {keys: int array Unsynchronized.ref, vals: int array Unsynchronized.ref,
    size: int Unsynchronized.ref};

  fun make n : T =
    {keys = Unsynchronized.ref (Array.array (n, ~1)), vals = Unsynchronized.ref (Array.array (n, 0)),
     size = Unsynchronized.ref 0};

  fun slot keys k =
    let
      val cap = Array.length keys;
      fun probe i =
        let val x = Array.sub (keys, i)
        in if x = ~1 orelse x = k then i else probe (if i + 1 = cap then 0 else i + 1) end;
    in probe (((k * 40503) div 256) mod cap) end;

  fun grow ({keys, vals, ...}: T) =
    let
      val old = ! keys;
      val oldv = ! vals;
      val cap = 2 * Array.length old + 1;
      val ks = Array.array (cap, ~1);
      val vs = Array.array (cap, 0);
    in
      Array.appi (fn (i, k) =>
        if k = ~1 then ()
        else
          let val j = slot ks k
          in Array.update (ks, j, k); Array.update (vs, j, Array.sub (oldv, i)) end) old;
      keys := ks;
      vals := vs
    end;

  fun get ({keys, vals, ...}: T) k =
    let val i = slot (! keys) k
    in if Array.sub (! keys, i) = k then SOME (Array.sub (! vals, i)) else NONE end;

  fun set (t as {keys, vals, size}: T) k v =
    let val _ = if 2 * ! size >= Array.length (! keys) then grow t else ()
        val i = slot (! keys) k
    in
      if Array.sub (! keys, i) = k then ()
      else (Array.update (! keys, i, k); size := ! size + 1);
      Array.update (! vals, i, v)
    end;
end;

(* a queue of lists by priority, at most a few dozen in practice; an array indexed by
   priority, as in \<^cite>\<open>\<open>Sect.~3.3\<close> in "pottier2016-lr1-reachability"\<close> *)
structure Queue =
struct
  type 'a T = {cells: 'a list array Unsynchronized.ref, at: int Unsynchronized.ref};

  fun make () : 'a T = {cells = Unsynchronized.ref (Array.array (64, [])), at = Unsynchronized.ref 0};

  fun put ({cells, ...}: 'a T) p x =
    let
      val _ =
        if p < Array.length (! cells) then ()
        else
          let
            val bigger = Array.array (2 * p + 2, []);
          in Array.appi (fn (i, l) => Array.update (bigger, i, l)) (! cells); cells := bigger end;
    in Array.update (! cells, p, x :: Array.sub (! cells, p)) end;

  (* the next element at least as far as any taken before *)
  fun take ({cells, at}: 'a T) =
    let
      val n = Array.length (! cells);
      fun go () =
        if ! at >= n then NONE
        else
          (case Array.sub (! cells, ! at) of
            x :: rest => (Array.update (! cells, ! at, rest); SOME (! at, x))
          | [] => (at := ! at + 1; go ()));
    in go () end;
end;

type node =
 {st: int, root: int,
  tkids: (int * int) list Unsynchronized.ref,            (* terminal, node *)
  nkids: (int * int) list Unsynchronized.ref,            (* nonterminal, node *)
  ends: int list Unsynchronized.ref};                    (* productions *)

fun run {hide, seconds} ({nstates, nterms, nnts, start, finals, trans, prods, reds}: view) =
  let
    val zcount = nterms + 1;
    val eof = nterms;
    val visible = fn z => hide <> SOME z;
    val zs = filter visible (0 upto nterms);
    fun is_term x = x < nterms;
    fun nt_of x = x - nterms - 1;

    (* the tables *)
    val tout = Array.array (nstates, []: (int * int) list);
    val nout = Array.array (nstates, []: (int * int) list);
    val goto = Array.array (nstates * nnts, ~1);
    val _ =
      List.app (fn (s, x, t) =>
        if is_term x then
          (if visible x then Array.update (tout, s, (x, t) :: Array.sub (tout, s)) else ())
        else
          (Array.update (nout, s, (nt_of x, t) :: Array.sub (nout, s));
           Array.update (goto, s * nnts + nt_of x, t))) trans;
    val reduces = Array.array (nstates * zcount, []: int list);
    val action = Array.array (nstates * zcount, false);
    val _ =
      List.app (fn (s, p, z) =>
        if visible z then
          (Array.update (reduces, s * zcount + z, p :: Array.sub (reduces, s * zcount + z));
           Array.update (action, s * zcount + z, true))
        else ()) reds;
    val _ =
      Array.appi (fn (s, ts) =>
        List.app (fn (a, _) => Array.update (action, s * zcount + a, true)) ts) tout;
    val _ = List.app (fn s => Array.update (action, s * zcount + eof, true)) finals;
    fun acts s z = Array.sub (action, s * zcount + z);

    val prodv = Vector.fromList prods;
    val by_lhs = Array.array (nnts, []: int list);
    val _ =
      Vector.appi (fn (p, (a, _)) => Array.update (by_lhs, a, p :: Array.sub (by_lhs, a))) prodv;

    (* the stars of \<^cite>\<open>\<open>Sect.~2.4\<close> in "pottier2016-lr1-reachability"\<close> as tries *)
    val count = Unsynchronized.ref 0;
    val store = Unsynchronized.ref (Array.array (4096, NONE: node option));
    fun node i = the (Array.sub (! store, i));
    fun new st root =
      let
        val i = ! count;
        val _ =
          if i < Array.length (! store) then ()
          else
            let val bigger = Array.array (2 * i, NONE)
            in Array.appi (fn (j, x) => Array.update (bigger, j, x)) (! store); store := bigger end;
        val n =
          {st = st, root = root, tkids = Unsynchronized.ref [], nkids = Unsynchronized.ref [],
           ends = Unsynchronized.ref []};
      in Array.update (! store, i, SOME n); count := i + 1; i end;
    fun child i x =
      let
        val n = node i;
        val kids = if is_term x then #tkids n else #nkids n;
        val sym = if is_term x then x else nt_of x;
      in
        (case AList.lookup (op =) (! kids) sym of
          SOME j => SOME j
        | NONE =>
            (case AList.lookup (op =) (Array.sub (if is_term x then tout else nout, #st n)) sym of
              NONE => NONE
            | SOME t =>
                let val j = new t (#root n)
                in kids := (sym, j) :: ! kids; SOME j end))
      end;
    fun walk i [] p = #ends (node i) := p :: ! (#ends (node i))
      | walk i (x :: xs) p =
          (case child i x of
            NONE => ()                      (* no such path out of this state *)
          | SOME j => walk j xs p);
    fun star s =
      let val r = new s s in
        List.app (fn (a, _) =>
          List.app (fn p => walk r (snd (Vector.sub (prodv, p))) p) (Array.sub (by_lhs, a)))
          (Array.sub (nout, s));
        r
      end;
    val roots = map star (0 upto nstates - 1);
    val nnodes = ! count;

    (* the nodes with an edge on a nonterminal, by the state and the nonterminal *)
    val parents = Array.array (nstates * nnts, []: (int * int) list);
    val _ =
      List.app (fn i =>
        List.app (fn (a, c) =>
          let val k = #st (node i) * nnts + a
          in Array.update (parents, k, (i, c) :: Array.sub (parents, k)) end) (! (#nkids (node i))))
        (0 upto nnodes - 1);

    (* F and E, by what the rules ask of them; an edge is a state and a nonterminal *)
    val facts_at = Array.array (nnodes * zcount, []: sentence list);
    val edges_at = Array.array (nstates * nnts * zcount, []: (sentence * int) list);
    val pushed = Tab.make 65537;
    val seen_e = Tab.make 65537;
    val queue: (int * int * sentence) Queue.T = Queue.make ();
    val nfacts = Unsynchronized.ref 0;
    val nedges = Unsynchronized.ref 0;

    fun fact_key n z f = (n * zcount + z) * zcount + f;
    fun push n z w =
      if acts (#st (node n)) z then
        let
          val k = fact_key n z (first_of w z);
          val l = len w;
        in
          (case Tab.get pushed k of
            SOME x => if x <= l then () else (Tab.set pushed k l; Queue.put queue l (n, z, w))
          | NONE => (Tab.set pushed k l; Queue.put queue l (n, z, w)))
        end
      else ();

    fun step_terminal n z w =
      (case AList.lookup (op =) (! (#tkids (node n))) z of
        NONE => ()
      | SOME c => List.app (fn z' => push c z' (app w (One z))) zs);
    fun step_nonterminal_left n z w =
      List.app (fn (a, c) =>
        List.app (fn (w', z') => push c z' (app w w'))
          (Array.sub (edges_at, (#st (node n) * nnts + a) * zcount + z))) (! (#nkids (node n)));
    fun step_nonterminal_right s a w' z' =
      List.app (fn (m, c) =>
        List.app (fn w => push c z' (app w w'))
          (Array.sub (facts_at, m * zcount + first_of w' z')))
        (Array.sub (parents, s * nnts + a));
    fun reduce n z w =
      let val {st, root, ends, ...} = node n in
        List.app (fn p =>
          if member (op =) (Array.sub (reduces, st * zcount + z)) p then
            let
              val a = fst (Vector.sub (prodv, p));
              val f = first_of w z;
              val e = (root * nnts + a) * zcount + z;
              val k = e * zcount + f;
            in
              (case Tab.get seen_e k of
                SOME _ => ()
              | NONE =>
                  (Tab.set seen_e k 0;
                   nedges := ! nedges + 1;
                   Array.update (edges_at, (root * nnts + a) * zcount + f,
                     (w, z) :: Array.sub (edges_at, (root * nnts + a) * zcount + f));
                   step_nonterminal_right root a w z))
            end
          else ()) (! ends)
      end;

    val t0 = Time.now ();
    fun out_of_time () = Time.toReal (Time.now () - t0) > seconds;
    val done_tab = Tab.make 65537;

    fun loop i =
      if i mod 4096 = 0 andalso out_of_time () then false
      else
        (case Queue.take queue of
          NONE => true
        | SOME (_, (n, z, w)) =>
            let val k = fact_key n z (first_of w z) in
              (case Tab.get done_tab k of
                SOME _ => loop i
              | NONE =>
                  (Tab.set done_tab k 0;
                   nfacts := ! nfacts + 1;
                   Array.update (facts_at, n * zcount + z, w :: Array.sub (facts_at, n * zcount + z));
                   step_terminal n z w;
                   step_nonterminal_left n z w;
                   reduce n z w;
                   loop (i + 1)))
            end);

    val _ = List.app (fn r => List.app (fn z => push r z Eps) zs) roots;
    val complete = loop 1;

    (* \<^cite>\<open>\<open>Sect.~3.5\<close> in "pottier2016-lr1-reachability"\<close> *)
    val nv = nstates * zcount;
    val dist = Array.array (nv, ~1);
    val from = Array.array (nv, NONE: (int * sentence) option);
    val fin = Array.array (nv, false);
    val vq: int Queue.T = Queue.make ();
    fun relax v d p w =
      if Array.sub (dist, v) >= 0 andalso Array.sub (dist, v) <= d then ()
      else
        (Array.update (dist, v, d);
         Array.update (from, v, SOME (p, w));
         Queue.put vq d v);
    val _ =
      List.app (fn z =>
        (Array.update (dist, start * zcount + z, 0); Queue.put vq 0 (start * zcount + z))) zs;
    fun dijkstra () =
      (case Queue.take vq of
        NONE => ()
      | SOME (d, v) =>
          (if Array.sub (fin, v) orelse Array.sub (dist, v) <> d then ()
           else
             let
               val s = v div zcount;
               val z = v mod zcount;
             in
               Array.update (fin, v, true);
               if not (acts s z) then ()
               else
                 ((case AList.lookup (op =) (Array.sub (tout, s)) z of
                    NONE => ()
                  | SOME t =>
                      List.app (fn z' => relax (t * zcount + z') (d + 1) v (One z)) zs);
                  List.app (fn (a, t) =>
                    List.app (fn (w, z') => relax (t * zcount + z') (d + len w) v w)
                      (Array.sub (edges_at, (s * nnts + a) * zcount + z)))
                    (Array.sub (nout, s)))
             end;
           dijkstra ()));
    val _ = dijkstra ();

    fun word v =
      let
        fun go v acc =
          (case Array.sub (from, v) of
            NONE => acc
          | SOME (p, w) => go p (words w @ acc));
      in go v [] end;
    val (errors, reached) =
      fold_rev (fn v => fn (es, rs) =>
        if Array.sub (dist, v) < 0 then (es, rs)
        else
          let
            val s = v div zcount;
            val z = v mod zcount;
            val x = {state = s, look = z, dist = Array.sub (dist, v), word = word v};
          in if acts s z then (es, x :: rs) else (x :: es, rs) end) (0 upto nv - 1) ([], []);
  in
    {complete = complete, nodes = nnodes, facts = ! nfacts, edges = ! nedges,
     errors = errors, reached = reached}
  end;

(** the sentences against the driver **)

type driver = (int * int) list -> int list;
type hit = {state: int, look: int, word: (int * int option) list};

(* the columns of a word up to their order: the distinct values to 0, 2, 4, ... or to
   2, 4, ..., so that 0, the start anchor, stays 0 and there is room between them *)
fun normal (w: (int * int) list) =
  let
    val vs = sort_distinct int_ord (map snd w);
    val base = if not (null vs) andalso hd vs = 0 then 0 else 1;
    val tab = fold (fn (i, v) => Inttab.update (v, 2 * (i + base))) (map_index I vs) Inttab.empty;
  in map (fn (t, c) => (t, the (Inttab.lookup tab c))) w end;

fun confirm {driver, nterms, widths, columns, seconds} targets =
  let
    val timer = Timer.startRealTimer ();
    fun out_of_time () = Time.toReal (Timer.checkRealTimer timer) > seconds;
    val key = fn (s, z) => s * (nterms + 2) + z;
    val hits = Unsynchronized.ref Inttab.empty;
    fun default_cols w =
      let
        fun go _ [] = []
          | go at (t :: ts) = at :: go (at + Vector.sub (widths, t) + 1) ts;
      in go 0 w end;
    (* one run; true if the word stopped before its end of input *)
    fun try given w =
      (case driver w of
        [] => false
      | st :: tk :: _ :: idx :: _ =>
          let
            val len = if tk >= nterms then idx else idx + 1;
            val word =
              if given then map (fn (t, c) => (t, SOME c)) (take len w)
              else map (fn (t, _) => (t, NONE)) (take len w);
            val k = key (st, tk);
            fun shorter (h: hit) = length word < length (#word h);
            val _ =
              if tk > nterms then ()
              else
                hits := Inttab.map_default (k, {state = st, look = tk, word = word})
                  (fn h => if shorter h then {state = st, look = tk, word = word} else h) (!hits);
          in tk <> nterms orelse idx < length w end
      | _ => raise Fail \<^unchecked_name>\<open>LR_Reach.confirm\<close>);
    fun found s z = Inttab.defined (!hits) (key (s, z));
    val node_limit = 512;
    (* a run on columns, memoised: targets share their prefixes *)
    val memo = Unsynchronized.ref (Symtab.empty: bool Symtab.table);
    fun try_memo w =
      let val k = space_implode "," (map (fn (t, c) => string_of_int t ^ "@" ^ string_of_int c) w) in
        (case Symtab.lookup (!memo) k of
          SOME b => b
        | NONE => let val b = try true w in memo := Symtab.update (k, b) (!memo); b end)
      end;
    (* the columns of w one by one, each in every position of the order of the columns
       before it (the driver only compares columns, and 0 is the start anchor); a prefix
       the driver stops on is not extended *)
    fun layouts s z w =
      let
        val nodes = Unsynchronized.ref 0;
        fun choices [] = [0, 2]
          | choices done =
              let val vs = sort_distinct int_ord (map snd done) in
                vs @ map (fn v => v + 1) vs @ (if hd vs > 0 then [0, hd vs - 1] else [])
              end;
        fun go _ [] = ()
          | go done (t :: ts) =
              List.app (fn c =>
                if found s z orelse !nodes >= node_limit orelse out_of_time () then ()
                else
                  let
                    val _ = nodes := !nodes + 1;
                    val prefix = normal (done @ [(t, c)]);
                  in if try_memo prefix then () else go prefix ts end)
                (choices done);
      in go [] w end;
    fun full z w = if z >= nterms then w else w @ [z];
    fun default (s, z, w) =
      if found s z orelse out_of_time () then ()
      else (try false (full z w ~~ default_cols (full z w)); ());
    fun other (s, z, w) =
      if found s z orelse out_of_time () then () else layouts s z (full z w);
    (* all in the default layout first, which is cheap *)
    val _ = List.app default targets;
    val _ = if columns then List.app other targets else ();
  in map #2 (Inttab.dest (!hits)) end;


(** the pairs that may fail on columns: an abstract interpretation of the vector driver **)

(* A frame of the vector driver holds an anchor set for each item of its state (LR_Vec).
   Here a set is 0 (empty), 1 (nonempty), 2 (nonempty with an up-set) or 3 (all columns),
   and a frame is the values of its kernel positions, each with a class: positions of one
   class hold the same set.  The sets of the slots follow from the kernel by the effects
   of the closure.  A configuration is a state, a frame, the lookahead it was entered
   with by a goto (NONE after a shift, where the lookahead is free), and what is known of
   that lookahead: for a kernel position, the relations of which one holds between the
   column of the lookahead and exactly its set.  The configurations are an upper bound
   of the frames on top of the stack over all layouts; a pair fails only if one of its
   configurations has no action that surely holds.

   The facts used: a goto after a reduction never fails (the set of the completed item is
   in the set of the slot below, and each anchor of that came through an item with the
   nonterminal after the dot, a kernel item of the target); a shift or a reduction holds
   if a relation it needs is implied by what is known. *)

type anchors =
 {rels: int list list, kernels: (int * int) list list,
  cells: (int * int * int * int * int) list};

exception Out_Of_Time;

(* the effect of a closure step on a set S: (S if i) | up (min S + s) | up c, S nonempty *)
type eff = bool * int option * int option;

datatype sid = SSig of (int * eff) list | SK of int;
datatype key = Key of int * sid | Uniq of int;

fun column_errors {seconds} ({nstates, nterms = nt, nnts, finals, trans, prods, ...}: view)
    ({rels, kernels, cells}: anchors) =
  let
    val timer = Timer.startRealTimer ();
    fun tick () =
      if Time.toReal (Timer.checkRealTimer timer) > seconds then raise Out_Of_Time else ();
    (* relations of items: 0 =, 1 >, 2 >=, 3 any, ~1 the start item *)
    val (EQ, GT, GE, ANY) = (0, 1, 2, 3);
    val np = length prods;
    val prodv = Vector.fromList (map (fn (a, sy) => (a, Vector.fromList sy)) prods);
    val relv = Vector.fromList (map Vector.fromList rels);
    fun lhs p = #1 (Vector.sub (prodv, p));
    fun rhs p = #2 (Vector.sub (prodv, p));
    fun rel p m = Vector.sub (Vector.sub (relv, p), m);
    fun nonterm x = if x > nt then SOME (x - nt - 1) else NONE;
    fun is_slot (p, m) = m = 0 andalso p < np;
    fun nxt (p, m) =
      if p >= np orelse m >= Vector.length (rhs p) then NONE else SOME (Vector.sub (rhs p, m));
    val nsym = nt + 1 + nnts;
    val gotos = fold (fn (a, x, b) => Inttab.update (a * nsym + x, b)) trans Inttab.empty;
    fun goto j x = Inttab.lookup gotos (j * nsym + x);
    val out_tab = fold (fn (a, x, _) => Inttab.cons_list (a, x)) trans Inttab.empty;
    fun out_of j = Inttab.lookup_list out_tab j;
    val by_lhs = Array.array (nnts, []: int list);
    val _ = List.app (fn p => Array.update (by_lhs, lhs p, p :: Array.sub (by_lhs, lhs p)))
      (np - 1 downto 0);
    fun first_nt p =
      if Vector.length (rhs p) = 0 then NONE else nonterm (Vector.sub (rhs p, 0));

    (* the items of each state: its kernel, then the slots of the nonterminals that are
       left corners of those after the dot of the kernel (for the start item, the
       nonterminal whose goto is final, or all) *)
    val final_set = Inttab.make_set finals;
    fun closure j kernel =
      let
        val reach = Array.array (nnts, false);
        fun visit A =
          if Array.sub (reach, A) then ()
          else
            (Array.update (reach, A, true);
             List.app (fn p => Option.app visit (first_nt p)) (Array.sub (by_lhs, A)));
        fun seeds (p, m) =
          if p >= np then
            if m <> 0 then []
            else
              (case filter (fn A => (case goto j (nt + 1 + A) of
                  SOME b => Inttab.defined final_set b | NONE => false)) (0 upto nnts - 1) of
                [] => 0 upto nnts - 1
              | As => As)
          else the_list (Option.mapPartial nonterm (nxt (p, m)));
        val _ = List.app visit (maps seeds kernel);
        val slots = map_filter (fn p => if Array.sub (reach, lhs p) then SOME (p, 0) else NONE)
          (0 upto np - 1);
      in Vector.fromList (kernel @ slots) end;
    val itemv = Vector.fromList (map_index (fn (j, k) => closure j k) kernels);
    fun items j = Vector.sub (itemv, j);
    fun item j k = Vector.sub (items j, k);
    val width = 2 + fold (fn (_, sy) => Integer.max (length sy)) prods 0;
    val idxv = Vector.map (fn its =>
      Vector.foldli (fn (k, (p, m), tab) => Inttab.update (p * width + m, k) tab) Inttab.empty its)
      itemv;
    fun idx j (p, m) = Inttab.lookup (Vector.sub (idxv, j)) (p * width + m);
    val kposv = Vector.map (fn its =>
      filter (fn k => not (is_slot (Vector.sub (its, k)))) (0 upto Vector.length its - 1)) itemv;
    fun kpos j = Vector.sub (kposv, j);
    fun sym p m = Vector.sub (rhs p, m);

    (* the reduce cells by (state, lookahead), and their relations by (state, production,
       lookahead) *)
    fun ckey j z = j * (nt + 1) + z;
    val cell_tab = fold (fn (j, p, m, z, t) => Inttab.cons_list (ckey j z, (p, m, t)))
      (rev cells) Inttab.empty;
    fun cells_of j z = Inttab.lookup_list cell_tab (ckey j z);
    fun tkey j p z = (j * (np + 1) + p) * (nt + 1) + z;
    val tc_tab = fold (fn (j, p, _, z, t) => Inttab.map_default (tkey j p z, [])
      (insert (op =) t)) cells Inttab.empty;
    fun tc j p z = Inttab.lookup_list tc_tab (tkey j p z);

    (* the closure transfer of a relation on a set *)
    fun tr_rel q v =
      if v = 0 then 0 else if q = ANY then 3 else if q = EQ then v
      else if q = GE then (if v = 3 then 3 else 2) else 2;
    (* a frame: (position, value, class), sorted by position, every value nonzero *)
    fun values j (f: (int * int * int) list) =
      let
        val its = items j;
        val nv = Array.array (nnts, 0);
        fun raise_to B w = if w > Array.sub (nv, B) then (Array.update (nv, B, w); true) else false;
        val _ =
          if exists (fn (k, v, _) => v > 0 andalso Vector.sub (its, k) = (np, 0)) f then
            Array.modify (K 1) nv
          else
            let
              val _ = List.app (fn (k, v, _) =>
                let val (p, m) = Vector.sub (its, k) in
                  (case Option.mapPartial nonterm (nxt (p, m)) of
                    SOME B => if v > 0 then ignore (raise_to B (tr_rel (rel p m) v)) else ()
                  | NONE => ())
                end) f;
              fun loop () =
                let
                  val changed = fold (fn A => fn ch =>
                    if Array.sub (nv, A) = 0 then ch
                    else
                      fold (fn p => fn ch =>
                        (case first_nt p of
                          SOME B => raise_to B (tr_rel (rel p 0) (Array.sub (nv, A))) orelse ch
                        | NONE => ch)) (Array.sub (by_lhs, A)) ch) (0 upto nnts - 1) false;
                in if changed then loop () else () end;
            in loop () end;
        val vals = Array.tabulate (Vector.length its, fn k =>
          let val it = Vector.sub (its, k) in
            if is_slot it then Array.sub (nv, lhs (#1 it)) else 0
          end);
        val _ = List.app (fn (k, v, _) => Array.update (vals, k, v)) f;
      in vals end;
    fun fkey f = space_implode ";" (map (fn (k, v, c) =>
      string_of_int k ^ "," ^ string_of_int v ^ "," ^ string_of_int c) f);
    val vcache = Unsynchronized.ref (Symtab.empty: int array Symtab.table);
    fun V j f =
      let val key = string_of_int j ^ ":" ^ fkey f in
        (case Symtab.lookup (!vcache) key of
          SOME a => a
        | NONE => let val a = values j f in vcache := Symtab.update (key, a) (!vcache); a end)
      end;

    (* cpre q {c} R with c free, and cpre q RA R with RA of value va *)
    fun opt_shift q v =
      if v = 0 then [0] else if q < 0 then [0, 1, 2, 3] else if q = ANY then [v]
      else if v = 3 andalso (q = EQ orelse q = GE) then [1] else [0, 1];
    fun opt_goto va q v =
      if v = 0 then [0] else if q < 0 then [0, 1, 2, 3] else if q = ANY then [v]
      else if q = EQ then
        (if v = 3 then [va] else if va = 3 then [v]
         else if v >= 2 andalso va >= 2 then [2] else [0, 1])
      else if va >= 2 then [v]
      else if q = GE andalso v = 3 then [1, 3]
      else distinct (op =) [0, 1, v];

    (* effects (LR_Vec eff) and the path effects of the left corners *)
    fun omin NONE b = b
      | omin a NONE = a
      | omin (SOME a) (SOME b) = SOME (Int.min (a, b));
    fun oadd (SOME a) (SOME b) = SOME (a + b)
      | oadd _ _ = NONE;
    fun ejoin ((i1, s1, c1): eff) ((i2, s2, c2): eff) = (i1 orelse i2, omin s1 s2, omin c1 c2);
    fun ecomp ((i1, s1, c1): eff) ((i2, s2, c2): eff) =
      let
        val a = omin (if i1 then SOME 0 else NONE) s1;
        val s = omin (if i2 then s1 else NONE) (oadd a s2);
        val c = omin (omin (if i2 then c1 else NONE) (oadd c1 s2)) c2;
      in (i1 andalso i2, s, c) end;
    fun of_rel q: eff =
      if q = EQ then (true, NONE, NONE) else if q = GT then (false, SOME 1, NONE)
      else if q = GE then (false, SOME 0, NONE) else (false, NONE, SOME 0);
    val pe = Vector.tabulate (nnts, fn B =>
      let
        val E = Unsynchronized.ref (Inttab.make [(B, (true, NONE, NONE): eff)]);
        fun loop () =
          let
            val changed = fold (fn (A, _) => fn ch =>
              fold (fn p => fn ch =>
                (case first_nt p of
                  SOME C =>
                    let
                      val e = ecomp (the (Inttab.lookup (!E) A)) (of_rel (rel p 0));
                      val old = Inttab.lookup (!E) C;
                      val e2 = (case old of SOME eC => ejoin eC e | NONE => e);
                    in
                      if old = SOME e2 then ch else (E := Inttab.update (C, e2) (!E); true)
                    end
                | NONE => ch)) (Array.sub (by_lhs, A)) ch) (Inttab.dest (!E)) false;
          in if changed then loop () else () end;
        val _ = loop ();
      in !E end);
    fun cls f k = Option.map #3 (find_first (fn (k', _, _) => k' = k) f);
    fun fval f k = (case find_first (fn (k', _, _) => k' = k) f of SOME (_, v, _) => v | NONE => 0);
    (* the set of a slot of A: the join of the effects from the kernel classes *)
    fun slot_sig j f A =
      let
        val sg = fold (fn (k, v, c) => fn sg =>
          let val (p, m) = item j k in
            (case Option.mapPartial nonterm (nxt (p, m)) of
              SOME B =>
                (case Inttab.lookup (Vector.sub (pe, B)) A of
                  SOME e0 =>
                    if v = 0 then sg
                    else
                      let val e = ecomp (of_rel (rel p m)) e0 in
                        Inttab.map_default (c, e) (fn e' => ejoin e' e) sg
                      end
                | NONE => sg)
            | NONE => sg)
          end) f Inttab.empty;
      in SSig (Inttab.dest sg) end;
    fun setid j ps f =
      let val it = item j ps in
        if is_slot it then slot_sig j f (lhs (#1 it))
        else SK (the_default ps (cls f ps))
      end;
    (* the kernel positions of the successor on X, each with its key and options *)
    fun succ j f X opt =
      let val vals = V j f in
        (case goto j X of
          NONE => NONE
        | SOME j2 =>
            SOME (j2, map_filter (fn k2 =>
              let val (p, m) = item j2 k2 in
                if m = 0 then NONE
                else
                  (case idx j (p, m - 1) of
                    NONE => NONE
                  | SOME ps =>
                      if Array.sub (vals, ps) = 0 then NONE
                      else if p < np andalso sym p (m - 1) <> X then NONE
                      else
                        let val q = if p < np then rel p (m - 1) else ~1 in
                          SOME (k2, Key (q, setid j ps f), opt q (Array.sub (vals, ps)))
                        end)
              end) (kpos j2)))
      end;
    fun sure ks = exists (fn (_, _, os) => not (member (op =) os 0)) ks;
    fun combos ks =
      let
        val groups = fold (fn (k, key, os) => fn gs =>
          (case AList.lookup (op =) gs key of
            SOME (os', l) => AList.update (op =) (key, (os', l @ [k])) gs
          | NONE => gs @ [(key, (os, [k]))])) ks [];
        fun prod [] = [[]]
          | prod ((_, (os, l)) :: gs) =
              let val rest = prod gs in
                maps (fn v => map (fn r => (v, l) :: r) rest) (sort_distinct int_ord os)
              end;
        fun frame asg =
          sort (int_ord o apply2 #1)
            (maps (fn (v, l) => if v = 0 then [] else
              let val c = fold Integer.min l (hd l) in map (fn k => (k, v, c)) l end) asg);
      in filter_out null (map frame (prod groups)) end;

    (* the states where the slot of a production started, by its end state; the items
       with a nonterminal after the dot *)
    fun follow j [] = SOME j
      | follow j (x :: xs) = (case goto j x of SOME j' => follow j' xs | NONE => NONE);
    fun pkey j p = j * (np + 1) + p;
    val (preds, with_A) =
      fold (fn j0 => fn (pr, wa) =>
        Vector.foldli (fn (k, it as (p, m), (pr, wa)) =>
          let
            val pr' =
              if is_slot it then
                (case follow j0 (Vector.foldr (op ::) [] (rhs p)) of
                  SOME j => Inttab.map_default (pkey j p, []) (insert (op =) j0) pr
                | NONE => pr)
              else pr;
            val wa' =
              (case Option.mapPartial nonterm (nxt (p, m)) of
                SOME A => Inttab.cons_list (j0 * nnts + A, k) wa
              | NONE => wa);
          in (pr', wa') end) (pr, wa) (items j0)) (0 upto nstates - 1) (Inttab.empty, Inttab.empty);
    fun preds_of j p = Inttab.lookup_list preds (pkey j p);
    fun with_A_of j0 A = rev (Inttab.lookup_list with_A (j0 * nnts + A));

    (* the configurations, by rounds: a reduction is rerun when the frames below grow *)
    fun ckey_of (j, f, z, know) =
      string_of_int j ^ "|" ^ fkey f ^ "|" ^
      (case z of NONE => "-" | SOME z => string_of_int z) ^ "|" ^
      space_implode ";" (map (fn (k, T) => string_of_int k ^ ":" ^ commas (map string_of_int T)) know);
    val conf = Unsynchronized.ref (Symtab.empty: (int * (int * int * int) list * int option *
      (int * int list) list) Symtab.table);
    val frames = Array.array (nstates, Symtab.empty: (int * int * int) list Symtab.table);
    fun process (j, f, z, _) add =
      let
        val vals = V j f;
        val _ = List.app (fn X =>
          if X < nt andalso (case z of NONE => true | SOME z => z = X) then
            (case succ j f X opt_shift of
              SOME (j2, ks) => List.app (fn f2 => add (j2, f2, NONE, [])) (combos ks)
            | NONE => ())
          else ()) (out_of j);
        val zs = (case z of SOME z => [z] | NONE => 0 upto nt);
      in
        zs |> List.app (fn zz => cells_of j zz |> List.app (fn (p, m, _) =>
          (case (if p < np then idx j (p, m) else NONE) of
            NONE => ()
          | SOME c =>
              if Array.sub (vals, c) = 0 then ()
              else
                let
                  val va = Array.sub (vals, c);
                  val A = lhs p;
                  val T = if zz < nt then SOME (tc j p zz) else NONE;
                in
                  preds_of j p |> List.app (fn j0 =>
                    let val sl = the (idx j0 (p, 0)) in
                      Symtab.fold (fn (_, f0) => fn () =>
                        let val v0 = V j0 f0 in
                          if Array.sub (v0, sl) = 0 then ()
                          else
                            let
                              val live = filter (fn x => Array.sub (v0, x) > 0) (with_A_of j0 A);
                              fun qx x =
                                let val (p', m') = item j0 x in if p' < np then rel p' m' else ~1 end;
                              val uniq =
                                (case live of
                                  [] => false
                                | x0 :: _ =>
                                    qx x0 = EQ andalso
                                    forall (fn x => qx x = qx x0 andalso
                                      setid j0 x f0 = setid j0 x0 f0) live);
                            in
                              (case succ j0 f0 (nt + 1 + A) (opt_goto va) of
                                NONE => ()
                              | SOME (j2, ks) =>
                                  let
                                    val ks' =
                                      if uniq then
                                        map (fn (k, Key (q, s), os) =>
                                              if q = EQ then (k, Uniq k, [va]) else (k, Key (q, s), os)
                                          | x => x) ks
                                      else ks;
                                    val kn = map_filter (fn (k, Uniq _, _) => SOME k | _ => NONE) ks';
                                  in
                                    combos ks' |> List.app (fn f2 =>
                                      let
                                        val kw =
                                          (case T of
                                            SOME t => map (rpair t) (filter (fn k => fval f2 k > 0) kn)
                                          | NONE => []);
                                      in add (j2, f2, SOME zz, sort (int_ord o apply2 #1) kw) end)
                                  end)
                            end
                        end) (Array.sub (frames, j0)) ()
                    end)
                end)))
      end;
    fun add_conf (cf as (j, f, _, _)) =
      (conf := Symtab.update (ckey_of cf, cf) (!conf);
       Array.update (frames, j, Symtab.update (fkey f, f) (Array.sub (frames, j))));
    val _ =
      List.app (fn j =>
        if member (op =) (Vector.foldr (op ::) [] (items j)) (np, 0) then
          add_conf (j, map (fn k => (k, 1, k)) (kpos j), NONE, [])
        else ()) (0 upto nstates - 1);
    fun rounds () =
      let
        val new = Unsynchronized.ref Symtab.empty;
        fun add cf =
          let val k = ckey_of cf in
            if Symtab.defined (!conf) k then () else new := Symtab.update (k, cf) (!new)
          end;
        val _ = Symtab.fold (fn (_, cf) => fn () => (tick (); process cf add)) (!conf) ();
      in
        if Symtab.is_empty (!new) then ()
        else (Symtab.fold (fn (_, cf) => fn () => add_conf cf) (!new) (); rounds ())
      end;

    (* whether a configuration may fail on z *)
    val (WEQ, WGE, WGT, WLE, WLT, WANY) = (0, 1, 2, 3, 4, 5);
    fun lic_sure t v =
      if t = WANY then v >= 1 else if t = WEQ orelse t = WGE then v = 3
      else if t = WLE orelse t = WLT then v >= 2 else false;
    fun impl t =
      if t = WEQ then [WEQ, WGE, WLE] else if t = WGT then [WGT, WGE]
      else if t = WLT then [WLT, WLE] else [t];
    fun shift_ok q = if q = EQ then [WEQ] else if q = GE then [WEQ, WGE, WGT] else [WGT];
    (* the set of item x contains the set of kernel position k *)
    fun sup j f x k =
      x = k orelse
      (if not (is_slot (item j x)) then
         (case (cls f x, cls f k) of (SOME a, SOME b) => a = b | _ => false)
       else
         (case (slot_sig j f (lhs (#1 (item j x))), cls f k) of
           (SSig sg, SOME ck) => exists (fn (c, (i, _, _)) => c = ck andalso i) sg
         | _ => false));
    fun may_fail (j, f, zz, know) z =
      if (case zz of SOME z' => z' <> z | NONE => false) then false
      else
        let
          val vals = V j f;
          val shifts =
            z < nt andalso
            (case succ j f z opt_shift of
              NONE => false
            | SOME (j2, ks) =>
                sure ks orelse
                exists (fn k2 =>
                  let val (p2, m2) = item j2 k2 in
                    m2 > 0 andalso p2 < np andalso
                    (case idx j (p2, m2 - 1) of
                      SOME ps =>
                        Array.sub (vals, ps) > 0 andalso sym p2 (m2 - 1) = z andalso
                        let val q = rel p2 (m2 - 1) in
                          q <> ANY andalso
                          exists (fn (k, T) => subset (op =) (T, shift_ok q) andalso sup j f ps k) know
                        end
                    | NONE => false)
                  end) (kpos j2));
          val reduces =
            exists (fn (p, m, t) =>
              (case idx j (p, m) of
                SOME c =>
                  let val v = Array.sub (vals, c) in
                    v > 0 andalso
                    (z = nt orelse lic_sure t v orelse
                     let val cs = tc j p z in
                       exists (fn (k, T) =>
                         forall (fn t2 => exists (member (op =) cs) (impl t2)) T andalso sup j f c k) know
                     end)
                  end
              | NONE => false)) (cells_of j z);
        in not shifts andalso not reduces end;
  in
    (rounds ();
     let
       val byj = Symtab.fold (fn (_, cf as (j, _, _, _)) => Inttab.cons_list (j, cf)) (!conf) Inttab.empty;
     in SOME (fn (s, z) => exists (fn cf => may_fail cf z) (Inttab.lookup_list byj s)) end)
    handle Out_Of_Time => NONE
  end;

end;
