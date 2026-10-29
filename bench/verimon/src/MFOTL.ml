(* The part of MonPoly's MFOTL (9bce98f^, 2020) the vendored parser uses: the
   formula type and free_vars, which the parser's aggregation check calls. *)

open Predicate

type tsdiff = float

type bound = OBnd of tsdiff | CBnd of tsdiff | Inf

type interval = bound * bound

type agg_op = Cnt | Min | Max | Sum | Avg | Med

type formula =
  | Equal of (term * term)
  | Less of (term * term)
  | LessEq of (term * term)
  | Pred of predicate
  | Let of (predicate * formula * formula)
  | Neg of formula
  | And of (formula * formula)
  | Or of (formula * formula)
  | Implies of (formula * formula)
  | Equiv of (formula * formula)
  | Exists of (var list * formula)
  | ForAll of (var list * formula)
  | Aggreg of (tsymb * var * agg_op * var * var list * formula)
  | Prev of (interval * formula)
  | Next of (interval * formula)
  | Eventually of (interval * formula)
  | Once of (interval * formula)
  | Always of (interval * formula)
  | PastAlways of (interval * formula)
  | Since of (interval * formula * formula)
  | Until of (interval * formula * formula)
  | Frex of (interval * regex)
  | Prex of (interval * regex)
and regex =
  | Wild
  | Test of formula
  | Concat of (regex * regex)
  | Plus of (regex * regex)
  | Star of regex

let rec free_vars = function
  | Equal (t1, t2) | Less (t1, t2) | LessEq (t1, t2) ->
      Misc.union (Predicate.tvars t1) (Predicate.tvars t2)
  | Pred p -> Predicate.pvars p
  | Let (_, _, f) | Neg f -> free_vars f
  | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
      Misc.union (free_vars f1) (free_vars f2)
  | Exists (vl, f) | ForAll (vl, f) ->
      List.filter (fun x -> not (List.mem x vl)) (free_vars f)
  | Aggreg (_, y, _, _, glist, _) -> y :: glist
  | Prev (_, f) | Next (_, f) | Eventually (_, f) | Once (_, f) | Always (_, f)
  | PastAlways (_, f) -> free_vars f
  | Since (_, f1, f2) | Until (_, f1, f2) -> Misc.union (free_vars f2) (free_vars f1)
  | Frex (_, r) | Prex (_, r) -> free_re_vars r
and free_re_vars = function
  | Wild -> []
  | Test f -> free_vars f
  | Concat (r1, r2) | Plus (r1, r2) -> Misc.union (free_re_vars r1) (free_re_vars r2)
  | Star r -> free_re_vars r
