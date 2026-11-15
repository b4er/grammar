(* Author: Basil Fürer *)

(* terminal providers: a name with a token type and the fixed spellings of its tokens,
   read by the clause tokens of NAME of the grammar command; registered from outside
   (a lexer, through the bridge theory of the session TIGER_Bridge) *)

signature TERMINAL_PROVIDER =
sig
  (* tokenT: a ground ('tok, 'ch, 'more) token_scheme; spellings: a spelling and its
     token value of type 'tok, the first of two equal spellings counts *)
  type provider = {tokenT: typ, spellings: (string * term) list}
  val register: binding -> provider -> local_theory -> local_theory
  val check: Proof.context -> xstring * Position.T -> string * provider
end;

structure Terminal_Provider: TERMINAL_PROVIDER =
struct

type provider = {tokenT: typ, spellings: (string * term) list};

structure Data = Generic_Data
(
  type T = provider Name_Space.table;
  val empty: T = Name_Space.empty_table "terminal provider";
  fun merge data: T = Name_Space.merge_tables data;
);

fun morph phi ({tokenT, spellings}: provider) : provider =
  {tokenT = Morphism.typ phi tokenT, spellings = map (apsnd (Morphism.term phi)) spellings};

fun register b p =
  Local_Theory.declaration
    {syntax = false, pervasive = false, pos = Binding.pos_of b}
    (fn phi => fn context =>
      Data.map (#2 o Name_Space.define context true (Morphism.binding phi b, morph phi p))
        context);

fun check ctxt = Name_Space.check (Context.Proof ctxt) (Data.get (Context.Proof ctxt));

end;
