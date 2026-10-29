(*
  Poly/ML runtime for purebench_gen.sml, the purebench CakeML program printed
  as Standard ML (purebenchPPScript.sml). The printed program carries the
  translated CakeML basis itself; this file supplies what CakeML's runtime
  provides underneath it:

  - CMLffi.call: the FFI of $(CAKEMLDIR)/basis/basis_ffi.c (2023), byte for
    byte: argument access, open_in/open_out/read/write/close, exit;
  - CMLprim: the byte-array copy primitives and word rotation.

  CakeML's int is unbounded, as is Poly/ML's default int.
*)

structure CMLprim = struct
  (* CopyStrAw8 [src; srcoff; len; dst; dstoff] *)
  fun copyStrAw8 (src, srcoff, len, dst, dstoff) =
    if srcoff < 0 orelse len < 0 orelse dstoff < 0
       orelse srcoff + len > String.size src
       orelse dstoff + len > Word8Array.length dst
    then raise Subscript
    else
      let fun go i =
            if i >= len then ()
            else (Word8Array.update (dst, dstoff + i,
                    Byte.charToByte (String.sub (src, srcoff + i)));
                  go (i + 1))
      in go 0 end

  (* CopyAw8Str [src; srcoff; len] *)
  fun copyAw8Str (src, srcoff, len) =
    if srcoff < 0 orelse len < 0 orelse srcoff + len > Word8Array.length src
    then raise Subscript
    else Byte.unpackString (Word8ArraySlice.slice (src, srcoff, SOME len))

  (* CopyAw8Aw8 [src; srcoff; len; dst; dstoff] *)
  fun copyAw8Aw8 (src, srcoff, len, dst, dstoff) =
    if srcoff < 0 orelse len < 0 orelse dstoff < 0
       orelse srcoff + len > Word8Array.length src
       orelse dstoff + len > Word8Array.length dst
    then raise Subscript
    else Word8ArraySlice.copy
           {src = Word8ArraySlice.slice (src, srcoff, SOME len),
            dst = dst, di = dstoff}

  fun rorWord8 (w, k) =
    let val k = Word.mod (k, 0w8)
    in Word8.orb (Word8.>> (w, k), Word8.<< (w, Word.- (0w8, k))) end
  fun rorWord64 (w, k) =
    let val k = Word.mod (k, 0w64)
    in Word64.orb (Word64.>> (w, k), Word64.<< (w, Word.- (0w64, k))) end
end;

structure CMLffi = struct
  (* functions, not values: polyc evaluates top-level values at compile time *)
  fun argv () = CommandLine.name () :: CommandLine.arguments ()

  fun get a i = Word8.toInt (Word8Array.sub (a, i))
  fun set a i n = Word8Array.update (a, i, Word8.fromInt n)

  fun byte2 a i = get a i * 256 + get a (i + 1)
  fun set_byte2 a i n = (set a i (n div 256 mod 256); set a (i + 1) (n mod 256))
  fun set_byte8 a i n =
    let fun go k = if k < 0 then ()
                   else (set a (i + k) (IntInf.toInt (IntInf.~>> (IntInf.fromInt n,
                                          Word.fromInt (8 * (7 - k))) mod 256)); go (k - 1))
    in go 7 end
  (* get_arg_count/get_arg_length write little-endian, unlike byte2 *)
  fun set_byte2' a n = (set a 0 (n mod 256); set a 1 (n div 256 mod 256))
  fun conf_int c =
    List.foldl (fn (ch, acc) => acc * 256 + Char.ord ch) 0 (String.explode c)

  (* the C side reads conf as a NUL-terminated string *)
  fun cstring c =
    case CharVector.findi (fn (_, ch) => ch = #"\000") c of
      SOME (i, _) => String.substring (c, 0, i)
    | NONE => c

  fun fd_of i = Posix.FileSys.wordToFD (SysWord.fromInt i)
  fun int_of fd = SysWord.toInt (Posix.FileSys.fdToWord fd)

  fun opened a (f : unit -> Posix.IO.file_desc) =
    (let val fd = f () in set a 0 0; set_byte8 a 1 (int_of fd) end)
    handle OS.SysErr _ => set a 0 1

  fun trace () = isSome (OS.Process.getEnv "PUREBENCH_TRACE")
  fun bytes a = String.concatWith ","
    (List.tabulate (Int.min (Word8Array.length a, 12),
                    fn i => Int.toString (get a i)))

  fun call name (c, a) =
    if not (trace ()) then call' name (c, a)
    else (TextIO.output (TextIO.stdErr,
            "ffi " ^ name ^ " conf=" ^ String.toString c ^ " in=[" ^ bytes a ^ "]");
          call' name (c, a);
          TextIO.output (TextIO.stdErr, " out=[" ^ bytes a ^ "]\n"))

  and call' name (c : string, a : Word8Array.array) : unit =
    case name of
      "get_arg_count" => set_byte2' a (length (argv ()))
    | "get_arg_length" =>
        set_byte2' a (String.size (List.nth (argv (), get a 0 + get a 1 * 256)))
    | "get_arg" =>
        let val s = List.nth (argv (), get a 0 + get a 1 * 256)
        in CharVector.appi (fn (k, ch) =>
             Word8Array.update (a, k, Byte.charToByte ch)) s end
    | "open_in" =>
        opened a (fn () => Posix.FileSys.openf
                             (cstring c, Posix.FileSys.O_RDONLY,
                              Posix.FileSys.O.flags []))
    | "open_out" =>
        opened a (fn () => Posix.FileSys.createf
                             (cstring c, Posix.FileSys.O_RDWR,
                              Posix.FileSys.O.trunc,
                              Posix.FileSys.S.flags
                                [Posix.FileSys.S.irusr, Posix.FileSys.S.iwusr,
                                 Posix.FileSys.S.irgrp, Posix.FileSys.S.iroth]))
    | "read" =>
        (let val n = byte2 a 0
             val got = Posix.IO.readArr
                         (fd_of (conf_int c), Word8ArraySlice.slice (a, 4, SOME n))
         in set a 0 0; set_byte2 a 1 got end
         handle OS.SysErr _ => set a 0 1)
    | "write" =>
        (let val n = byte2 a 0
             val off = byte2 a 2
             val put = Posix.IO.writeArr
                         (fd_of (conf_int c),
                          Word8ArraySlice.slice (a, 4 + off, SOME n))
         in set a 0 0; set_byte2 a 1 put end
         handle OS.SysErr _ => set a 0 1)
    | "close" =>
        ((Posix.IO.close (fd_of (conf_int c)); set a 0 0)
         handle OS.SysErr _ => set a 0 1)
    | "exit" => Posix.Process.exit (Word8.fromInt (get a 0))
    | _ => ()   (* "", poll_sigint, kernel_ffi: no-ops, as in basis_ffi.c *)
end;
(* generated by purebenchPPScript.sml *)

datatype ('a) option = SOME of 'a | NONE;

datatype ordering = Greater | Equal | Less;

datatype ('a, 'b) sum = Inr of 'b | Inl of 'a;

val fst = (fn v3 => (case v3 of
   (v2, v1) => v2));

val snd = (fn v3 => (case v3 of
   (v2, v1) => v1));

val cml_o = (fn v2 => (fn v3 => (fn v1 => (v2 (v3 v1)))));

val id = (fn v1 => v1);

val flip = (fn v3 => (fn v2 => (fn v1 => ((v3 v1) v2))));

val const = (fn v2 => (fn v1 => v2));

val update = (fn v3 => (fn v4 => (fn v2 => (fn v1 => (if (v3 = v1)
 then v4
 else (v2 v1))))));

val min = (fn v1 => (fn v2 => (if (v1 < v2)
 then v1
 else v2)));

val max = (fn v1 => (fn v2 => (if (v1 < v2)
 then v2
 else v1)));

fun owhile v1 = (fn v2 => (fn v3 => (if (v1 v3)
 then (((owhile v1) v2) (v2 v3))
 else (SOME v3))));

structure CML_Option = struct
type ('a) option = ('a) option;

val getOpt = (fn v3 => (fn v2 => (case v3 of
   (NONE) => v2
 | (SOME v1) => v1)));

val isSome = (fn v2 => (case v2 of
   (NONE) => (0 < 0)
 | (SOME v1) => (0 <= 0)));

val valOf = (fn v => (case v of
   (NONE) => (raise (Bind))
 | (SOME v1) => v1));

val join = (fn v2 => (case v2 of
   (NONE) => (NONE)
 | (SOME v1) => v1));

val map = (fn v2 => (fn v3 => (case v3 of
   (NONE) => (NONE)
 | (SOME v1) => (SOME (v2 v1)))));

val mapPartial = (fn v2 => (fn v3 => (case v3 of
   (NONE) => (NONE)
 | (SOME v1) => (v2 v1))));

val compose = (fn v3 => (fn v4 => (fn v2 => (case (v4 v2) of
   (NONE) => (NONE)
 | (SOME v1) => (SOME (v3 v1))))));

val composePartial = (fn v3 => (fn v4 => (fn v2 => (case (v4 v2) of
   (NONE) => (NONE)
 | (SOME v1) => (v3 v1)))));

val isNone = (fn v2 => (case v2 of
   (NONE) => (0 <= 0)
 | (SOME v1) => (0 < 0)));

val map2 = (fn v1 => (fn v2 => (fn v3 => (if ((isSome v2) andalso (isSome v3))
 then (SOME ((v1 (valOf v2)) (valOf v3)))
 else (NONE)))));

val compare = (fn v4 => (fn v5 => (fn v6 => (case v5 of
   (NONE) => (case v6 of
   (NONE) => (Equal)
 | (SOME v1) => (Less))
 | (SOME v3) => (case v6 of
   (NONE) => (Greater)
 | (SOME v2) => ((v4 v3) v2))))));

end;

structure CML_List = struct
type ('a) list = ('a) list;

val null = (fn v3 => (case v3 of
   [] => (0 <= 0)
 | (v2 :: v1) => (0 < 0)));

local
fun length_aux v3 = (fn v4 => (case v3 of
   [] => v4
 | (v2 :: v1) => ((length_aux v1) (v4 + 1))));

in
val length = (fn v1 => ((length_aux v1) 0));

local
fun rev v4 = (fn v3 => (case v4 of
   [] => v3
 | (v2 :: v1) => ((rev v1) (v2 :: v3))));

fun map_rev' v4 = (fn v5 => (fn v3 => (case v5 of
   [] => v3
 | (v2 :: v1) => (((map_rev' v4) v1) ((v4 v2) :: v3)))));

fun filter_rev' v3 = (fn v5 => (fn v4 => (case v5 of
   [] => v4
 | (v2 :: v1) => (if (v3 v2)
 then (((filter_rev' v3) v1) (v2 :: v4))
 else (((filter_rev' v3) v1) v4)))));

fun flat_rev' v4 = (fn v3 => (case v4 of
   [] => v3
 | (v2 :: v1) => ((flat_rev' v1) ((rev v2) v3))));

in
val rev = (fn v1 => ((rev v1) []));

val mapRev = (fn v1 => (fn v2 => (((map_rev' v1) v2) [])));

val filterRev = (fn v1 => (fn v2 => (((filter_rev' v1) v2) [])));

val flatRev = (fn v1 => ((flat_rev' v1) []));

val cml_x64 = (fn v1 => (fn v2 => (v1 @ v2)));

val hd = (fn v => (case v of
   [] => (raise (Bind))
 | (v2 :: v1) => v2));

val tl = (fn v3 => (case v3 of
   [] => []
 | (v2 :: v1) => v1));

fun last v = (case v of
   [] => (raise (Bind))
 | (v2 :: v1) => (if (v1 = [])
 then v2
 else (last v1)));

val getItem = (fn v3 => (case v3 of
   [] => (NONE)
 | (v2 :: v1) => (SOME (v2, v1))));

fun nth v1 = (fn v2 => (if (v2 = 0)
 then (hd v1)
 else ((nth (tl v1)) (let val k = (v2 - 1)
 in (if (k < 0)
 then 0
 else k) end))));

fun take v3 = (fn v4 => (case v3 of
   [] => []
 | (v2 :: v1) => (if (v4 = 0)
 then []
 else (v2 :: ((take v1) (let val k = (v4 - 1)
 in (if (k < 0)
 then 0
 else k) end))))));

fun drop v3 = (fn v4 => (case v3 of
   [] => []
 | (v2 :: v1) => (if (v4 = 0)
 then (v2 :: v1)
 else ((drop v1) (let val k = (v4 - 1)
 in (if (k < 0)
 then 0
 else k) end)))));

fun takeUntil v3 = (fn v4 => (case v4 of
   [] => []
 | (v2 :: v1) => (if (v3 v2)
 then []
 else (v2 :: ((takeUntil v3) v1)))));

fun dropUntil v3 = (fn v4 => (case v4 of
   [] => []
 | (v2 :: v1) => (if (v3 v2)
 then (v2 :: v1)
 else ((dropUntil v3) v1))));

fun cmp v7 = (fn v8 => (fn v9 => (case v8 of
   [] => (case v9 of
   [] => (Equal)
 | (v2 :: v1) => (Less))
 | (v6 :: v5) => (case v9 of
   [] => (Greater)
 | (v4 :: v3) => (case ((v7 v6) v4) of
   (Less) => (Less)
 | (Equal) => (((cmp v7) v5) v3)
 | (Greater) => (Greater))))));

fun concat v3 = (case v3 of
   [] => []
 | (v2 :: v1) => (v2 @ (concat v1)));

fun map v4 = (fn v5 => (case v5 of
   [] => []
 | (v3 :: v2) => (let val v1 = (v4 v3)
 in (v1 :: ((map v4) v2)) end)));

local
fun mapi v4 = (fn v5 => (fn v6 => (case v6 of
   [] => []
 | (v3 :: v2) => (let val v1 = ((v4 v5) v3)
 in (v1 :: (((mapi v4) (v5 + 1)) v2)) end))));

in
val mapi = (fn v1 => (fn v2 => (((mapi v1) 0) v2)));

fun mapPartial v4 = (fn v5 => (case v5 of
   [] => []
 | (v3 :: v2) => (case (v4 v3) of
   (NONE) => ((mapPartial v4) v2)
 | (SOME v1) => (v1 :: ((mapPartial v4) v2)))));

fun app f = (fn ls => (case ls of
   [] => ()
 | (x :: xs) => (let val _ = (f x)
 in ((app f) xs) end)));

fun find v3 = (fn v4 => (case v4 of
   [] => (NONE)
 | (v2 :: v1) => (if (v3 v2)
 then (SOME v2)
 else ((find v3) v1))));

fun filter v3 = (fn v4 => (case v4 of
   [] => []
 | (v2 :: v1) => (if (v3 v2)
 then (v2 :: ((filter v3) v1))
 else ((filter v3) v1))));

local
fun partition_aux v3 = (fn v5 => (fn v6 => (fn v4 => (case v5 of
   [] => ((rev v6), (rev v4))
 | (v2 :: v1) => (if (v3 v2)
 then ((((partition_aux v3) v1) (v2 :: v6)) v4)
 else ((((partition_aux v3) v1) v6) (v2 :: v4)))))));

in
val partition = (fn v1 => (fn v2 => ((((partition_aux v1) v2) []) [])));

fun foldl v4 = (fn v3 => (fn v5 => (case v5 of
   [] => v3
 | (v2 :: v1) => (((foldl v4) ((v4 v2) v3)) v1))));

local
fun foldli_aux v4 = (fn v3 => (fn v5 => (fn v6 => (case v6 of
   [] => v3
 | (v2 :: v1) => ((((foldli_aux v4) (((v4 v5) v2) v3)) (v5 + 1)) v1)))));

in
val foldli = (fn v2 => (fn v1 => (fn v3 => ((((foldli_aux v2) v1) 0) v3))));

fun foldr v4 = (fn v3 => (fn v5 => (case v5 of
   [] => v3
 | (v2 :: v1) => ((v4 v2) (((foldr v4) v3) v1)))));

fun foldri v5 = (fn v4 => (fn v6 => (case v6 of
   [] => v4
 | (v3 :: v2) => (((v5 0) v3) (((foldri (fn v1 => (v5 (v1 + 1)))) v4) v2)))));

fun exists v3 = (fn v4 => (case v4 of
   [] => (0 < 0)
 | (v2 :: v1) => ((v3 v2) orelse ((exists v3) v1))));

fun all v3 = (fn v4 => (case v4 of
   [] => (0 <= 0)
 | (v2 :: v1) => ((v3 v2) andalso ((all v3) v1))));

fun snoc v4 = (fn v3 => (case v3 of
   [] => (v4 :: [])
 | (v2 :: v1) => (v2 :: ((snoc v4) v1))));

local
fun genlist_aux v1 = (fn v3 => (fn v2 => (if (v3 = 0)
 then v2
 else (((genlist_aux v1) (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) ((v1 (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) :: v2)))));

in
val genlist = (fn v1 => (fn v2 => (((genlist_aux v1) v2) [])));

fun tabulate v8 = (fn v7 => (fn v6 => (fn v5 => (let val v4 = (v8 >= v7)
 in (if v4
 then (rev v5)
 else (let val v3 = (v6 v8)
 in (let val v2 = (v8 + 1)
 in (let val v1 = (v3 :: v5)
 in ((((tabulate v2) v7) v6) v1) end) end) end)) end))));

val tabulate = (fn v3 => (fn v2 => (let val v1 = []
 in ((((tabulate 0) v3) v2) v1) end)));

fun collate v7 = (fn v8 => (fn v9 => (case v8 of
   [] => (case v9 of
   [] => (Equal)
 | (v2 :: v1) => (Less))
 | (v6 :: v5) => (case v9 of
   [] => (Greater)
 | (v4 :: v3) => (if (((v7 v6) v4) = (Equal))
 then (((collate v7) v5) v3)
 else ((v7 v6) v4))))));

fun zip v7 = (case v7 of
   (v6, v5) => (case v6 of
   [] => []
 | (v4 :: v3) => (case v5 of
   [] => []
 | (v2 :: v1) => ((v4, v2) :: (zip (v3, v1))))));

fun member v4 = (fn v3 => (case v3 of
   [] => (0 < 0)
 | (v2 :: v1) => ((v4 = v2) orelse ((member v4) v1))));

fun sum v3 = (case v3 of
   [] => 0
 | (v2 :: v1) => (v2 + (sum v1)));

fun unzip v8 = (case v8 of
   [] => ([], [])
 | (v7 :: v6) => (case v7 of
   (v5, v4) => (let val v3 = (unzip v6)
 in (case v3 of
   (v2, v1) => ((v5 :: v2), (v4 :: v1))) end)));

val pad_right = (fn v1 => (fn v2 => (fn v3 => (v3 @ ((genlist (const v1)) (let val k = (v2 - (length v3))
 in (if (k < 0)
 then 0
 else k) end))))));

val pad_left = (fn v1 => (fn v2 => (fn v3 => (((genlist (const v1)) (let val k = (v2 - (length v3))
 in (if (k < 0)
 then 0
 else k) end)) @ v3))));

fun all_distinct v3 = (case v3 of
   [] => (0 <= 0)
 | (v2 :: v1) => ((((member v2) v1) = (0 < 0)) andalso (all_distinct v1)));

fun isPrefix v5 = (fn v6 => (case v5 of
   [] => (0 <= 0)
 | (v4 :: v3) => (case v6 of
   [] => (0 < 0)
 | (v2 :: v1) => ((v4 = v2) andalso ((isPrefix v3) v1)))));

fun front v = (case v of
   [] => (raise (Bind))
 | (v2 :: v1) => (if (v1 = [])
 then []
 else (v2 :: (front v1))));

fun splitAtPki v6 = (fn v7 => (fn v8 => (case v8 of
   [] => ((v7 []) [])
 | (v5 :: v4) => (if ((v6 0) v5)
 then ((v7 []) (v5 :: v4))
 else (((splitAtPki ((cml_o v6) (fn v1 => (v1 + 1)))) (fn v3 => (fn v2 => ((v7 (v5 :: v3)) v2)))) v4)))));

fun update v3 = (fn v4 => (fn v5 => (case v5 of
   [] => []
 | (v2 :: v1) => (if (v4 = 0)
 then (v3 :: v1)
 else (v2 :: (((update v3) (let val k = (v4 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v1))))));

fun compare v7 = (fn v8 => (fn v9 => (case v8 of
   [] => (case v9 of
   [] => (Equal)
 | (v2 :: v1) => (Less))
 | (v6 :: v5) => (case v9 of
   [] => (Greater)
 | (v4 :: v3) => (case ((v7 v6) v4) of
   (Less) => (Less)
 | (Equal) => (((compare v7) v5) v3)
 | (Greater) => (Greater))))));

local
fun qsort_part v3 = (fn v5 => (fn v4 => (fn v6 => (fn v7 => (case v4 of
   [] => (v6, v7)
 | (v2 :: v1) => (if ((v3 v2) v5)
 then (((((qsort_part v3) v5) v1) (v2 :: v6)) v7)
 else (((((qsort_part v3) v5) v1) v6) (v2 :: v7))))))));

fun qsort_acc v6 = (fn v7 => (fn v8 => (case v7 of
   [] => v8
 | (v5 :: v4) => (let val v3 = (((((qsort_part v6) v5) v4) []) [])
 in (case v3 of
   (v2, v1) => (((qsort_acc v6) v2) (v5 :: (((qsort_acc v6) v1) v8)))) end))));

in
val sort = (fn v1 => (fn v2 => (((qsort_acc v1) v2) [])));

end;

end;

end;

end;

end;

end;

end;

end;

structure CML_Alist = struct
fun lookup v5 = (fn v6 => (case v5 of
   [] => (NONE)
 | (v4 :: v3) => (case v4 of
   (v2, v1) => (if (v2 = v6)
 then (SOME v1)
 else ((lookup v3) v6)))));

val update = (fn v3 => (fn v4 => (case v4 of
   (v2, v1) => ((v2, v1) :: v3))));

fun every v5 = (fn v6 => (fn v7 => (case v7 of
   [] => (0 <= 0)
 | (v4 :: v3) => (case v4 of
   (v2, v1) => (if ((CML_List.member v2) v5)
 then (((every v5) v6) v3)
 else ((v6 (v2, v1)) andalso (((every (v2 :: v5)) v6) v3)))))));

val every = (fn v1 => ((every []) v1));

fun map v5 = (fn v6 => (case v6 of
   [] => []
 | (v4 :: v3) => (case v4 of
   (v2, v1) => ((v2, (v5 v1)) :: ((map v5) v3)))));

fun delete v5 = (fn v6 => (case v5 of
   [] => []
 | (v4 :: v3) => (case v4 of
   (v2, v1) => (if (v2 = v6)
 then ((delete v3) v6)
 else ((v2, v1) :: ((delete v3) v6))))));

end;

structure CML_String = struct
type string = string;

val sub = (fn v1 => (fn v2 => (String.sub (v1, v2))));

val implode = (fn v1 => (String.implode v1));

val explode = (fn v1 => (String.explode v1));

val size = (fn v1 => (String.size v1));

val concat = (fn v1 => (String.concat v1));

val substring = (fn v1 => (fn v2 => (fn v3 => (String.substring (v1, v2, v3)))));

val strcat = (fn v1 => (fn v2 => (String.concat (v1 :: (v2 :: [])))));

val cml_x94 = (fn v1 => (fn v2 => ((strcat v1) v2)));

val extract = (fn v4 => (fn v2 => (fn v3 => (if ((String.size v4) <= v2)
 then ""
 else (case v3 of
   (NONE) => (String.substring (v4, v2, (let val k = ((String.size v4) - v2)
 in (if (k < 0)
 then 0
 else k) end)))
 | (SOME v1) => (String.substring (v4, v2, ((min (let val k = ((String.size v4) - v2)
 in (if (k < 0)
 then 0
 else k) end)) v1))))))));

local
fun concatwith_aux v3 = (fn v4 => (fn v5 => (case v4 of
   [] => ""
 | (v2 :: v1) => (if v5
 then ((strcat v2) (((concatwith_aux v3) v1) (0 < 0)))
 else ((strcat v3) (((concatwith_aux v3) (v2 :: v1)) (0 <= 0)))))));

in
val concatWith = (fn v2 => (fn v1 => (((concatwith_aux v2) v1) (0 <= 0))));

val str = (fn v1 => (String.implode (v1 :: [])));

local
fun translate_aux v1 = (fn v4 => (fn v2 => (fn v3 => (if (v3 = 0)
 then []
 else ((v1 (String.sub (v4, v2))) :: ((((translate_aux v1) v4) (v2 + 1)) (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)))))));

in
val translate = (fn v1 => (fn v2 => (String.implode ((((translate_aux v1) v2) 0) (String.size v2)))));

local
fun splitl_aux v1 = (fn v3 => (fn v2 => (if ((v2 < (String.size v3)) andalso (v1 (String.sub (v3, v2))))
 then (((splitl_aux v1) v3) (v2 + 1))
 else ((((extract v3) 0) (SOME v2)), (((extract v3) v2) (NONE))))));

in
val split = (fn v1 => (fn v2 => (((splitl_aux v1) v2) 0)));

local
fun tokens_aux v3 = (fn v4 => (fn v5 => (fn v6 => (fn v7 => (case v5 of
   [] => (if (v7 = 0)
 then []
 else (if (v3 (String.sub (v4, v6)))
 then (((((tokens_aux v3) v4) []) (v6 + 1)) (let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end))
 else (((((tokens_aux v3) v4) ((String.sub (v4, v6)) :: [])) (v6 + 1)) (let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end))))
 | (v2 :: v1) => (if (v7 = 0)
 then ((String.implode (CML_List.rev (v2 :: v1))) :: [])
 else (if (v3 (String.sub (v4, v6)))
 then ((String.implode (CML_List.rev (v2 :: v1))) :: (((((tokens_aux v3) v4) []) (v6 + 1)) (let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end)))
 else (((((tokens_aux v3) v4) ((String.sub (v4, v6)) :: (v2 :: v1))) (v6 + 1)) (let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end)))))))));

in
val tokens = (fn v1 => (fn v2 => (((((tokens_aux v1) v2) []) 0) (String.size v2))));

local
fun fields_aux v1 = (fn v4 => (fn v5 => (fn v2 => (fn v3 => (if (v3 = 0)
 then ((String.implode (CML_List.rev v5)) :: [])
 else (if (v1 (String.sub (v4, v2)))
 then ((String.implode (CML_List.rev v5)) :: (((((fields_aux v1) v4) []) (v2 + 1)) (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)))
 else (((((fields_aux v1) v4) ((String.sub (v4, v2)) :: v5)) (v2 + 1)) (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end))))))));

in
val fields = (fn v1 => (fn v2 => (((((fields_aux v1) v2) []) 0) (String.size v2))));

fun findi v1 = (fn v2 => (fn v3 => (if (v2 < (String.size v3))
 then (if (v1 (String.sub (v3, v2)))
 then (SOME v2)
 else (((findi v1) (v2 + 1)) v3))
 else (NONE))));

local
fun isstringthere_aux v2 = (fn v4 => (fn v3 => (fn v5 => (fn v1 => (if (v1 = 0)
 then (0 <= 0)
 else (if ((String.sub (v2, v3)) = (String.sub (v4, v5)))
 then (((((isstringthere_aux v2) v4) (v3 + 1)) (v5 + 1)) (let val k = (v1 - 1)
 in (if (k < 0)
 then 0
 else k) end))
 else (0 < 0)))))));

in
fun isSubstring v4 = (fn v5 => (fn v1 => (fn v2 => (fn v3 => (if (v3 = 0)
 then (0 < 0)
 else (if (((((isstringthere_aux v4) v5) 0) v2) v1)
 then (0 <= 0)
 else (((((isSubstring v4) v5) v1) (v2 + 1)) (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end))))))));

val isSubstring = (fn v1 => (fn v2 => (if ((String.size v1) <= (String.size v2))
 then (((((isSubstring v1) v2) (String.size v1)) 0) ((let val k = ((String.size v2) - (String.size v1))
 in (if (k < 0)
 then 0
 else k) end) + 1))
 else (0 < 0))));

val isSuffix = (fn v1 => (fn v2 => (if ((String.size v1) <= (String.size v2))
 then (((((isstringthere_aux v1) v2) 0) (let val k = ((String.size v2) - (String.size v1))
 in (if (k < 0)
 then 0
 else k) end)) (String.size v1))
 else (0 < 0))));

val isPrefix = (fn v1 => (fn v2 => (if ((String.size v1) <= (String.size v2))
 then (((((isstringthere_aux v1) v2) 0) 0) (String.size v1))
 else (0 < 0))));

local
fun compare_aux v3 = (fn v4 => (fn v2 => (fn v5 => (fn v1 => (if (v1 = 0)
 then v2
 else (if ((String.sub (v4, v5)) < (String.sub (v3, v5)))
 then (Greater)
 else (if ((String.sub (v3, v5)) < (String.sub (v4, v5)))
 then (Less)
 else (((((compare_aux v3) v4) v2) (v5 + 1)) (let val k = (v1 - 1)
 in (if (k < 0)
 then 0
 else k) end)))))))));

in
val compare = (fn v1 => (fn v2 => (if ((String.size v1) < (String.size v2))
 then (((((compare_aux v1) v2) (Less)) 0) (String.size v1))
 else (if ((String.size v2) < (String.size v1))
 then (((((compare_aux v1) v2) (Greater)) 0) (String.size v2))
 else (((((compare_aux v1) v2) (Equal)) 0) (String.size v2))))));

val cml_x60 = (fn v1 => (fn v2 => (((compare v1) v2) = (Less))));

val cml_x60x61 = (fn v1 => (fn v2 => ((((compare v1) v2) = (Greater)) = (0 < 0))));

val cml_x62x61 = (fn v1 => (fn v2 => ((((compare v1) v2) = (Less)) = (0 < 0))));

val cml_x62 = (fn v1 => (fn v2 => (((compare v1) v2) = (Greater))));

local
fun collate_aux v1 = (fn v5 => (fn v6 => (fn v3 => (fn v2 => (fn v4 => (if (v4 = 0)
 then v3
 else (if (((v1 (String.sub (v5, v2))) (String.sub (v6, v2))) = (Equal))
 then ((((((collate_aux v1) v5) v6) v3) (v2 + 1)) (let val k = (v4 - 1)
 in (if (k < 0)
 then 0
 else k) end))
 else ((v1 (String.sub (v5, v2))) (String.sub (v6, v2))))))))));

in
val collate = (fn v1 => (fn v2 => (fn v3 => (if ((String.size v2) < (String.size v3))
 then ((((((collate_aux v1) v2) v3) (Less)) 0) (String.size v2))
 else (if ((String.size v3) < (String.size v2))
 then ((((((collate_aux v1) v2) v3) (Greater)) 0) (String.size v3))
 else ((((((collate_aux v1) v2) v3) (Equal)) 0) (String.size v3)))))));

val char_escape_seq = (fn v1 => (if (v1 = #"\t")
 then (SOME "\\t")
 else (if (v1 = #"\n")
 then (SOME "\\n")
 else (if (v1 = #"\\")
 then (SOME "\\\\")
 else (if (v1 = #"\"")
 then (SOME "\\\"")
 else (NONE))))));

local
val char_escaped = (fn v2 => (case (char_escape_seq v2) of
   (NONE) => (v2 :: [])
 | (SOME v1) => (String.explode v1)));

in
val escape_str = (fn v1 => (String.implode (((#"\"" :: []) @ (CML_List.concat ((CML_List.map char_escaped) (String.explode v1)))) @ (#"\"" :: []))));

val escape_char = (fn v1 => (String.implode (((#"#" :: (#"\"" :: [])) @ (char_escaped v1)) @ (#"\"" :: []))));

end;

end;

end;

end;

end;

end;

end;

end;

end;

end;

val cml_x43 = (fn v1 => (fn v2 => (v1 + v2)));

val cml_x45 = (fn v1 => (fn v2 => (v1 - v2)));

val cml_x42 = (fn v1 => (fn v2 => (v1 * v2)));

val cml_div = (fn v1 => (fn v2 => (v1 div v2)));

val cml_x60 = (fn v1 => (fn v2 => (v1 < v2)));

val cml_x62 = (fn v1 => (fn v2 => (v1 > v2)));

val cml_x60x61 = (fn v1 => (fn v2 => (v1 <= v2)));

val cml_x61 = (fn v1 => (fn v2 => (v1 = v2)));

val cml_x60x62 = (fn v1 => (fn v2 => ((v1 = v2) = (0 < 0))));

val cml_x94 = (fn v1 => (fn v2 => ((CML_String.strcat v1) v2)));

val cml_x58x61 = (fn x => (fn y => (x := y)));

val cml_x33 = (fn x => (! x));

structure CML_Pair = struct
val map = (fn v3 => (fn v4 => (fn v5 => (case v5 of
   (v2, v1) => ((v3 v2), (v4 v1))))));

val toString = (fn v3 => (fn v4 => (fn v5 => (case v5 of
   (v2, v1) => (String.concat ("(" :: ((v3 v2) :: (", " :: ((v4 v1) :: (")" :: []))))))))));

val compare = (fn v1 => (fn v2 => (fn v3 => (fn v4 => (case ((v1 (fst v3)) (fst v4)) of
   (Less) => (Less)
 | (Equal) => ((v2 (snd v3)) (snd v4))
 | (Greater) => (Greater))))));

end;

structure CML_Int = struct
type int = int;

val cml_x43 = (fn v1 => (fn v2 => (v1 + v2)));

val cml_x45 = (fn v1 => (fn v2 => (v1 - v2)));

val cml_x42 = (fn v1 => (fn v2 => (v1 * v2)));

val cml_div = (fn v1 => (fn v2 => (v1 div v2)));

val cml_mod = (fn v1 => (fn v2 => (v1 mod v2)));

val cml_x60 = (fn v1 => (fn v2 => (v1 < v2)));

val cml_x62 = (fn v1 => (fn v2 => (v1 > v2)));

val cml_x60x61 = (fn v1 => (fn v2 => (v1 <= v2)));

val cml_x62x61 = (fn v1 => (fn v2 => (v1 >= v2)));

val cml_x126 = (fn v1 => (0 - v1));

local
val exp_for_dec_enc = 8;

val tochar = (fn v1 => (if (v1 < 10)
 then (Char.chr ((Char.ord #"0") + v1))
 else (Char.chr (let val k = (((Char.ord #"A") + v1) - 10)
 in (if (k < 0)
 then 0
 else k) end))));

fun num_to_rev_chars v1 = (fn v2 => (fn v3 => (if (v2 = 0)
 then (((num_to_rev_chars (v1 div 100000000)) exp_for_dec_enc) ((v1 mod 100000000) + v3))
 else (if ((v3 < 10) andalso (v1 = 0))
 then ((tochar v3) :: [])
 else ((tochar (v3 mod 10)) :: (((num_to_rev_chars v1) (let val k = (v2 - 1)
 in (if (k < 0)
 then 0
 else k) end)) (v3 div 10)))))));

in
val int_to_string = (fn v2 => (fn v1 => (if (0 <= v1)
 then (String.implode (CML_List.rev (((num_to_rev_chars v1) 0) 0)))
 else (String.implode ((v2 :: []) @ (CML_List.rev (((num_to_rev_chars (let val k = v1
 in (if (k < 0)
 then (0 - k)
 else k) end)) 0) 0)))))));

val toString = (fn v1 => ((int_to_string #"~") v1));

end;

local
val fromchar_unsafe = (fn v1 => (let val k = ((Char.ord v1) - 48)
 in (if (k < 0)
 then 0
 else k) end));

fun fromchars_range_unsafe v1 = (fn v2 => (fn v3 => (if (v2 = 0)
 then 0
 else (((((fromchars_range_unsafe v1) (let val k = (v2 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v3) * 10) + (fromchar_unsafe (String.sub (v3, (v1 + (let val k = (v2 - 1)
 in (if (k < 0)
 then 0
 else k) end)))))))));

val padlen_dec = 8;

val maxsmall_dec = 100000000;

fun fromchars_unsafe v4 = (fn v5 => (if (v4 = 0)
 then 0
 else (if (((let val k = (v4 - 1)
 in (if (k < 0)
 then 0
 else k) end) + 1) <= 8)
 then (((fromchars_range_unsafe 0) ((let val k = (v4 - 1)
 in (if (k < 0)
 then 0
 else k) end) + 1)) v5)
 else (let val v3 = (let val k = (((let val k = (v4 - 1)
 in (if (k < 0)
 then 0
 else k) end) + 1) - 8)
 in (if (k < 0)
 then 0
 else k) end)
 in (let val v2 = (((fromchars_unsafe v3) v5) * 100000000)
 in (let val v1 = (((fromchars_range_unsafe v3) 8) v5)
 in (v2 + v1) end) end) end))));

val fromstring_unsafe = (fn v1 => (if ((String.size v1) = 0)
 then 0
 else (if ((String.sub (v1, 0)) = #"~")
 then (0 - ((fromchars_unsafe (let val k = ((String.size v1) - 1)
 in (if (k < 0)
 then 0
 else k) end)) (String.substring (v1, 1, (let val k = ((String.size v1) - 1)
 in (if (k < 0)
 then 0
 else k) end)))))
 else ((fromchars_unsafe (String.size v1)) v1))));

val fromchar = (fn v2 => (let val v1 = (Char.ord v2)
 in (if ((48 <= v1) andalso (v1 <= 57))
 then (SOME (let val k = (v1 - 48)
 in (if (k < 0)
 then 0
 else k) end))
 else (NONE)) end));

fun fromchars_range v6 = (fn v7 => (fn v8 => (if (v7 = 0)
 then (SOME 0)
 else (let val v4 = ((CML_Option.map (fn v5 => (10 * v5))) (((fromchars_range v6) (let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v8))
 in (let val v3 = (fromchar (String.sub (v8, (v6 + (let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end)))))
 in (((CML_Option.map2 (fn v2 => (fn v1 => (v2 + v1)))) v4) v3) end) end))));

fun fromchars v7 = (fn v8 => (if (v7 = 0)
 then (SOME 0)
 else (if (((let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end) + 1) <= 8)
 then (((fromchars_range 0) ((let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end) + 1)) v8)
 else (let val v6 = (let val k = (((let val k = (v7 - 1)
 in (if (k < 0)
 then 0
 else k) end) + 1) - 8)
 in (if (k < 0)
 then 0
 else k) end)
 in (let val v4 = ((CML_Option.map (fn v5 => (100000000 * v5))) ((fromchars v6) v8))
 in (let val v3 = (((fromchars_range v6) 8) v8)
 in (((CML_Option.map2 (fn v2 => (fn v1 => (v2 + v1)))) v4) v3) end) end) end))));

in
val fromString = (fn v5 => (if ((String.size v5) = 0)
 then (NONE)
 else (if (((String.sub (v5, 0)) = #"~") orelse ((String.sub (v5, 0)) = #"-"))
 then ((CML_Option.map ((cml_o (fn v1 => (0 - v1))) (fn v2 => v2))) ((fromchars (let val k = ((String.size v5) - 1)
 in (if (k < 0)
 then 0
 else k) end)) (String.substring (v5, 1, (let val k = ((String.size v5) - 1)
 in (if (k < 0)
 then 0
 else k) end)))))
 else (if ((String.sub (v5, 0)) = #"+")
 then ((CML_Option.map (fn v3 => v3)) ((fromchars (let val k = ((String.size v5) - 1)
 in (if (k < 0)
 then 0
 else k) end)) (String.substring (v5, 1, (let val k = ((String.size v5) - 1)
 in (if (k < 0)
 then 0
 else k) end)))))
 else ((CML_Option.map (fn v4 => v4)) ((fromchars (String.size v5)) v5))))));

val fromNatString = (fn v2 => (case (fromString v2) of
   (NONE) => (NONE)
 | (SOME v1) => (if (0 <= v1)
 then (SOME v1)
 else (NONE))));

local
fun num_gcd v1 = (fn v2 => (if (v1 = 0)
 then v2
 else ((num_gcd (v2 mod v1)) v1)));

in
val gcd = (fn v1 => (fn v2 => ((num_gcd (let val k = v1
 in (if (k < 0)
 then (0 - k)
 else k) end)) (let val k = v2
 in (if (k < 0)
 then (0 - k)
 else k) end))));

val compare = (fn v1 => (fn v2 => (if (v1 < v2)
 then (Less)
 else (if (v2 < v1)
 then (Greater)
 else (Equal)))));

end;

end;

end;

structure CML_Char = struct
type char = char;

val ord = (fn v1 => (Char.ord v1));

val chr = (fn v1 => (Char.chr v1));

val cml_x60 = (fn v1 => (fn v2 => (v1 < v2)));

val cml_x62 = (fn v1 => (fn v2 => (v1 > v2)));

val cml_x60x61 = (fn v1 => (fn v2 => (v1 <= v2)));

val cml_x62x61 = (fn v1 => (fn v2 => (v1 >= v2)));

val isSpace = (fn v1 => (((Char.ord v1) = 32) orelse ((9 <= (Char.ord v1)) andalso ((Char.ord v1) <= 13))));

val fromByte = (fn v1 => (Char.chr (Word8.toInt v1)));

local
val some_chars_vector = (Vector.fromList ((SOME #"\^@") :: ((SOME #"\^A") :: ((SOME #"\^B") :: ((SOME #"\^C") :: ((SOME #"\^D") :: ((SOME #"\^E") :: ((SOME #"\^F") :: ((SOME #"\a") :: ((SOME #"\b") :: ((SOME #"\t") :: ((SOME #"\n") :: ((SOME #"\v") :: ((SOME #"\f") :: ((SOME #"\r") :: ((SOME #"\^N") :: ((SOME #"\^O") :: ((SOME #"\^P") :: ((SOME #"\^Q") :: ((SOME #"\^R") :: ((SOME #"\^S") :: ((SOME #"\^T") :: ((SOME #"\^U") :: ((SOME #"\^V") :: ((SOME #"\^W") :: ((SOME #"\^X") :: ((SOME #"\^Y") :: ((SOME #"\^Z") :: ((SOME #"\^[") :: ((SOME #"\^\") :: ((SOME #"\^]") :: ((SOME #"\^^") :: ((SOME #"\^_") :: ((SOME #" ") :: ((SOME #"!") :: ((SOME #"\"") :: ((SOME #"#") :: ((SOME #"$") :: ((SOME #"%") :: ((SOME #"&") :: ((SOME #"'") :: ((SOME #"(") :: ((SOME #")") :: ((SOME #"*") :: ((SOME #"+") :: ((SOME #",") :: ((SOME #"-") :: ((SOME #".") :: ((SOME #"/") :: ((SOME #"0") :: ((SOME #"1") :: ((SOME #"2") :: ((SOME #"3") :: ((SOME #"4") :: ((SOME #"5") :: ((SOME #"6") :: ((SOME #"7") :: ((SOME #"8") :: ((SOME #"9") :: ((SOME #":") :: ((SOME #";") :: ((SOME #"<") :: ((SOME #"=") :: ((SOME #">") :: ((SOME #"?") :: ((SOME #"@") :: ((SOME #"A") :: ((SOME #"B") :: ((SOME #"C") :: ((SOME #"D") :: ((SOME #"E") :: ((SOME #"F") :: ((SOME #"G") :: ((SOME #"H") :: ((SOME #"I") :: ((SOME #"J") :: ((SOME #"K") :: ((SOME #"L") :: ((SOME #"M") :: ((SOME #"N") :: ((SOME #"O") :: ((SOME #"P") :: ((SOME #"Q") :: ((SOME #"R") :: ((SOME #"S") :: ((SOME #"T") :: ((SOME #"U") :: ((SOME #"V") :: ((SOME #"W") :: ((SOME #"X") :: ((SOME #"Y") :: ((SOME #"Z") :: ((SOME #"[") :: ((SOME #"\\") :: ((SOME #"]") :: ((SOME #"^") :: ((SOME #"_") :: ((SOME #"`") :: ((SOME #"a") :: ((SOME #"b") :: ((SOME #"c") :: ((SOME #"d") :: ((SOME #"e") :: ((SOME #"f") :: ((SOME #"g") :: ((SOME #"h") :: ((SOME #"i") :: ((SOME #"j") :: ((SOME #"k") :: ((SOME #"l") :: ((SOME #"m") :: ((SOME #"n") :: ((SOME #"o") :: ((SOME #"p") :: ((SOME #"q") :: ((SOME #"r") :: ((SOME #"s") :: ((SOME #"t") :: ((SOME #"u") :: ((SOME #"v") :: ((SOME #"w") :: ((SOME #"x") :: ((SOME #"y") :: ((SOME #"z") :: ((SOME #"{") :: ((SOME #"|") :: ((SOME #"}") :: ((SOME #"~") :: ((SOME #"\127") :: ((SOME #"\128") :: ((SOME #"\129") :: ((SOME #"\130") :: ((SOME #"\131") :: ((SOME #"\132") :: ((SOME #"\133") :: ((SOME #"\134") :: ((SOME #"\135") :: ((SOME #"\136") :: ((SOME #"\137") :: ((SOME #"\138") :: ((SOME #"\139") :: ((SOME #"\140") :: ((SOME #"\141") :: ((SOME #"\142") :: ((SOME #"\143") :: ((SOME #"\144") :: ((SOME #"\145") :: ((SOME #"\146") :: ((SOME #"\147") :: ((SOME #"\148") :: ((SOME #"\149") :: ((SOME #"\150") :: ((SOME #"\151") :: ((SOME #"\152") :: ((SOME #"\153") :: ((SOME #"\154") :: ((SOME #"\155") :: ((SOME #"\156") :: ((SOME #"\157") :: ((SOME #"\158") :: ((SOME #"\159") :: ((SOME #"\160") :: ((SOME #"\161") :: ((SOME #"\162") :: ((SOME #"\163") :: ((SOME #"\164") :: ((SOME #"\165") :: ((SOME #"\166") :: ((SOME #"\167") :: ((SOME #"\168") :: ((SOME #"\169") :: ((SOME #"\170") :: ((SOME #"\171") :: ((SOME #"\172") :: ((SOME #"\173") :: ((SOME #"\174") :: ((SOME #"\175") :: ((SOME #"\176") :: ((SOME #"\177") :: ((SOME #"\178") :: ((SOME #"\179") :: ((SOME #"\180") :: ((SOME #"\181") :: ((SOME #"\182") :: ((SOME #"\183") :: ((SOME #"\184") :: ((SOME #"\185") :: ((SOME #"\186") :: ((SOME #"\187") :: ((SOME #"\188") :: ((SOME #"\189") :: ((SOME #"\190") :: ((SOME #"\191") :: ((SOME #"\192") :: ((SOME #"\193") :: ((SOME #"\194") :: ((SOME #"\195") :: ((SOME #"\196") :: ((SOME #"\197") :: ((SOME #"\198") :: ((SOME #"\199") :: ((SOME #"\200") :: ((SOME #"\201") :: ((SOME #"\202") :: ((SOME #"\203") :: ((SOME #"\204") :: ((SOME #"\205") :: ((SOME #"\206") :: ((SOME #"\207") :: ((SOME #"\208") :: ((SOME #"\209") :: ((SOME #"\210") :: ((SOME #"\211") :: ((SOME #"\212") :: ((SOME #"\213") :: ((SOME #"\214") :: ((SOME #"\215") :: ((SOME #"\216") :: ((SOME #"\217") :: ((SOME #"\218") :: ((SOME #"\219") :: ((SOME #"\220") :: ((SOME #"\221") :: ((SOME #"\222") :: ((SOME #"\223") :: ((SOME #"\224") :: ((SOME #"\225") :: ((SOME #"\226") :: ((SOME #"\227") :: ((SOME #"\228") :: ((SOME #"\229") :: ((SOME #"\230") :: ((SOME #"\231") :: ((SOME #"\232") :: ((SOME #"\233") :: ((SOME #"\234") :: ((SOME #"\235") :: ((SOME #"\236") :: ((SOME #"\237") :: ((SOME #"\238") :: ((SOME #"\239") :: ((SOME #"\240") :: ((SOME #"\241") :: ((SOME #"\242") :: ((SOME #"\243") :: ((SOME #"\244") :: ((SOME #"\245") :: ((SOME #"\246") :: ((SOME #"\247") :: ((SOME #"\248") :: ((SOME #"\249") :: ((SOME #"\250") :: ((SOME #"\251") :: ((SOME #"\252") :: ((SOME #"\253") :: ((SOME #"\254") :: ((SOME #"\255") :: [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));

in
val some = (fn v1 => (Vector.sub (some_chars_vector, (Char.ord v1))));

end;

end;

structure CML_Word8 = struct
type word = Word8.word;

val fromInt = (fn v1 => (Word8.fromInt v1));

val toInt = (fn v1 => (Word8.toInt v1));

val toIntSigned = (fn v1 => (let val x = (Word8.toInt v1)
 in (if (x < 128)
 then x
 else (x - 256)) end));

val andb = (fn v1 => (fn v2 => (Word8.andb (v1, v2))));

val orb = (fn v1 => (fn v2 => (Word8.orb (v1, v2))));

val xorb = (fn v1 => (fn v2 => (Word8.xorb (v1, v2))));

val notb = (fn v1 => (Word8.xorb (v1, (0wxFF : Word8.word))));

val cml_x43 = (fn v1 => (fn v2 => (Word8.+ (v1, v2))));

val cml_x45 = (fn v1 => (fn v2 => (Word8.- (v1, v2))));

val cml_x60x60 = (fn v2 => (fn v1 => (if (v1 < 8)
 then (if (v1 < 4)
 then (if (v1 < 2)
 then (if (v1 < 1)
 then v2
 else (Word8.<< (v2, (Word.fromInt 1))))
 else (if (v1 < 3)
 then (Word8.<< (v2, (Word.fromInt 2)))
 else (Word8.<< (v2, (Word.fromInt 3)))))
 else (if (v1 < 6)
 then (if (v1 < 5)
 then (Word8.<< (v2, (Word.fromInt 4)))
 else (Word8.<< (v2, (Word.fromInt 5))))
 else (if (v1 < 7)
 then (Word8.<< (v2, (Word.fromInt 6)))
 else (Word8.<< (v2, (Word.fromInt 7))))))
 else (0wx0 : Word8.word))));

val cml_x62x62 = (fn v2 => (fn v1 => (if (v1 < 8)
 then (if (v1 < 4)
 then (if (v1 < 2)
 then (if (v1 < 1)
 then v2
 else (Word8.>> (v2, (Word.fromInt 1))))
 else (if (v1 < 3)
 then (Word8.>> (v2, (Word.fromInt 2)))
 else (Word8.>> (v2, (Word.fromInt 3)))))
 else (if (v1 < 6)
 then (if (v1 < 5)
 then (Word8.>> (v2, (Word.fromInt 4)))
 else (Word8.>> (v2, (Word.fromInt 5))))
 else (if (v1 < 7)
 then (Word8.>> (v2, (Word.fromInt 6)))
 else (Word8.>> (v2, (Word.fromInt 7))))))
 else (0wx0 : Word8.word))));

val cml_x126x62x62 = (fn v2 => (fn v1 => (if (v1 < 8)
 then (if (v1 < 4)
 then (if (v1 < 2)
 then (if (v1 < 1)
 then v2
 else (Word8.~>> (v2, (Word.fromInt 1))))
 else (if (v1 < 3)
 then (Word8.~>> (v2, (Word.fromInt 2)))
 else (Word8.~>> (v2, (Word.fromInt 3)))))
 else (if (v1 < 6)
 then (if (v1 < 5)
 then (Word8.~>> (v2, (Word.fromInt 4)))
 else (Word8.~>> (v2, (Word.fromInt 5))))
 else (if (v1 < 7)
 then (Word8.~>> (v2, (Word.fromInt 6)))
 else (Word8.~>> (v2, (Word.fromInt 7))))))
 else (Word8.~>> (v2, (Word.fromInt 8))))));

end;

type byte_array = Word8Array.array;

structure CML_Word8Array = struct
val array = (fn x => (fn y => (Word8Array.array (x, y))));

val sub = (fn x => (fn y => (Word8Array.sub (x, y))));

val length = (fn x => (Word8Array.length x));

val update = (fn x => (fn y => (fn z => (Word8Array.update (x, y, z)))));

val copy = (fn src => (fn srcoff => (fn len => (fn dst => (fn dstoff => (CMLprim.copyAw8Aw8 (src, srcoff, len, dst, dstoff)))))));

val copyVec = (fn src => (fn srcoff => (fn len => (fn dst => (fn dstoff => (CMLprim.copyStrAw8 (src, srcoff, len, dst, dstoff)))))));

val substring = (fn src => (fn srcoff => (fn len => (CMLprim.copyAw8Str (src, srcoff, len)))));

local
fun findi_aux f = (fn arr => (fn max => (fn n => (let val cml_x32v0 = ((cml_x61 n) max)
 in (if cml_x32v0
 then (NONE)
 else (let val cml_x32v1 = ((sub arr) n)
 in (let val cml_x32v2 = (f cml_x32v1)
 in (if cml_x32v2
 then (let val cml_x32v3 = ((sub arr) n)
 in (let val cml_x32v4 = (n, cml_x32v3)
 in (SOME cml_x32v4) end) end)
 else (let val cml_x32v5 = ((cml_x43 n) 1)
 in ((((findi_aux f) arr) max) cml_x32v5) end)) end) end)) end))));

in
fun findi f = (fn arr => (let val cml_x32v0 = (length arr)
 in ((((findi_aux f) arr) cml_x32v0) 0) end));

end;

end;

datatype ('k, 'w) balanced_map = Bin of int * 'k * 'w * ('k, 'w) balanced_map * ('k, 'w) balanced_map | Tip;

local
datatype ('a, 'b) map = Map of ('a -> ('a -> ordering)) * ('a, 'b) balanced_map;

val size = (fn v6 => (case v6 of
   (Tip) => 0
 | (Bin (v5, v4, v3, v2, v1)) => v5));

val singleton = (fn v1 => (fn v2 => (Bin (1, v1, v2, (Tip), (Tip)))));

val ratio = 2;

val delta = 3;

val balancel = (fn v41 => (fn v42 => (fn v43 => (fn v44 => (case v43 of
   (Tip) => (case v44 of
   (Tip) => (Bin (1, v41, v42, (Tip), (Tip)))
 | (Bin (v5, v4, v3, v2, v1)) => (Bin ((1 + v5), v41, v42, (Tip), (Bin (v5, v4, v3, v2, v1)))))
 | (Bin (v40, v39, v38, v37, v36)) => (case v44 of
   (Tip) => (case v37 of
   (Tip) => (case v36 of
   (Tip) => (Bin (2, v41, v42, (Bin (v40, v39, v38, (Tip), (Tip))), (Tip)))
 | (Bin (v10, v9, v8, v7, v6)) => (Bin (3, v9, v8, (Bin (1, v39, v38, (Tip), (Tip))), (Bin (1, v41, v42, (Tip), (Tip))))))
 | (Bin (v20, v19, v18, v17, v16)) => (case v36 of
   (Tip) => (Bin (3, v39, v38, (Bin (v20, v19, v18, v17, v16)), (Bin (1, v41, v42, (Tip), (Tip)))))
 | (Bin (v15, v14, v13, v12, v11)) => (if (v15 < (ratio * v20))
 then (Bin ((1 + v40), v39, v38, (Bin (v20, v19, v18, v17, v16)), (Bin ((1 + v15), v41, v42, (Bin (v15, v14, v13, v12, v11)), (Tip)))))
 else (Bin ((1 + v40), v14, v13, (Bin (((1 + v20) + (size v12)), v39, v38, (Bin (v20, v19, v18, v17, v16)), v12)), (Bin ((1 + (size v11)), v41, v42, v11, (Tip))))))))
 | (Bin (v35, v34, v33, v32, v31)) => (if (v40 > (delta * v35))
 then (case v37 of
   (Tip) => (Tip)
 | (Bin (v30, v29, v28, v27, v26)) => (case v36 of
   (Tip) => (Tip)
 | (Bin (v25, v24, v23, v22, v21)) => (if (v25 < (ratio * v30))
 then (Bin (((1 + v40) + v35), v39, v38, v37, (Bin (((1 + v35) + v25), v41, v42, v36, (Bin (v35, v34, v33, v32, v31))))))
 else (Bin (((1 + v40) + v35), v24, v23, (Bin (((1 + v30) + (size v22)), v39, v38, v37, v22)), (Bin (((1 + v35) + (size v21)), v41, v42, v21, (Bin (v35, v34, v33, v32, v31)))))))))
 else (Bin (((1 + v40) + v35), v41, v42, (Bin (v40, v39, v38, v37, v36)), (Bin (v35, v34, v33, v32, v31)))))))))));

val balancer = (fn v41 => (fn v42 => (fn v43 => (fn v44 => (case v43 of
   (Tip) => (case v44 of
   (Tip) => (Bin (1, v41, v42, (Tip), (Tip)))
 | (Bin (v20, v19, v18, v17, v16)) => (case v17 of
   (Tip) => (case v16 of
   (Tip) => (Bin (2, v41, v42, (Tip), (Bin (v20, v19, v18, (Tip), (Tip)))))
 | (Bin (v5, v4, v3, v2, v1)) => (Bin (3, v19, v18, (Bin (1, v41, v42, (Tip), (Tip))), (Bin (v5, v4, v3, v2, v1)))))
 | (Bin (v15, v14, v13, v12, v11)) => (case v16 of
   (Tip) => (Bin (3, v14, v13, (Bin (1, v41, v42, (Tip), (Tip))), (Bin (1, v19, v18, (Tip), (Tip)))))
 | (Bin (v10, v9, v8, v7, v6)) => (if (v15 < (ratio * v10))
 then (Bin ((1 + v20), v19, v18, (Bin ((1 + v15), v41, v42, (Tip), (Bin (v15, v14, v13, v12, v11)))), (Bin (v10, v9, v8, v7, v6))))
 else (Bin ((1 + v20), v14, v13, (Bin ((1 + (size v12)), v41, v42, (Tip), v12)), (Bin (((1 + v10) + (size v11)), v19, v18, v11, (Bin (v10, v9, v8, v7, v6))))))))))
 | (Bin (v40, v39, v38, v37, v36)) => (case v44 of
   (Tip) => (Bin ((1 + v40), v41, v42, (Bin (v40, v39, v38, v37, v36)), (Tip)))
 | (Bin (v35, v34, v33, v32, v31)) => (if (v35 > (delta * v40))
 then (case v32 of
   (Tip) => (Tip)
 | (Bin (v30, v29, v28, v27, v26)) => (case v31 of
   (Tip) => (Tip)
 | (Bin (v25, v24, v23, v22, v21)) => (if (v30 < (ratio * v25))
 then (Bin (((1 + v40) + v35), v34, v33, (Bin (((1 + v40) + v30), v41, v42, (Bin (v40, v39, v38, v37, v36)), v32)), v31))
 else (Bin (((1 + v40) + v35), v29, v28, (Bin (((1 + v40) + (size v27)), v41, v42, (Bin (v40, v39, v38, v37, v36)), v27)), (Bin (((1 + v25) + (size v26)), v34, v33, v26, v31)))))))
 else (Bin (((1 + v40) + v35), v41, v42, (Bin (v40, v39, v38, v37, v36)), (Bin (v35, v34, v33, v32, v31)))))))))));

fun deletefindmax v14 = (case v14 of
   (Tip) => ((raise (Bind)), (Tip))
 | (Bin (v13, v12, v11, v10, v9)) => (case v9 of
   (Tip) => ((v12, v11), v10)
 | (Bin (v8, v7, v6, v5, v4)) => (let val v3 = (deletefindmax (Bin (v8, v7, v6, v5, v4)))
 in (case v3 of
   (v2, v1) => (v2, ((((balancel v12) v11) v10) v1))) end)));

fun deletefindmin v14 = (case v14 of
   (Tip) => ((raise (Bind)), (Tip))
 | (Bin (v13, v12, v11, v10, v9)) => (case v10 of
   (Tip) => ((v12, v11), v9)
 | (Bin (v8, v7, v6, v5, v4)) => (let val v3 = (deletefindmin (Bin (v8, v7, v6, v5, v4)))
 in (case v3 of
   (v2, v1) => (v2, ((((balancer v12) v11) v1) v9))) end)));

val glue = (fn v23 => (fn v24 => (case v23 of
   (Tip) => v24
 | (Bin (v22, v21, v20, v19, v18)) => (case v24 of
   (Tip) => (Bin (v22, v21, v20, v19, v18))
 | (Bin (v17, v16, v15, v14, v13)) => (if ((size (Bin (v22, v21, v20, v19, v18))) > (size (Bin (v17, v16, v15, v14, v13))))
 then (let val v6 = (deletefindmax (Bin (v22, v21, v20, v19, v18)))
 in (case v6 of
   (v5, v4) => ((case v5 of
   (v3, v2) => (fn v1 => ((((balancer v3) v2) v1) (Bin (v17, v16, v15, v14, v13))))) v4)) end)
 else (let val v12 = (deletefindmin (Bin (v17, v16, v15, v14, v13)))
 in (case v12 of
   (v11, v10) => ((case v11 of
   (v9, v8) => (fn v7 => ((((balancel v9) v8) (Bin (v22, v21, v20, v19, v18))) v7))) v10)) end))))));

fun trim_help_greater v6 = (fn v7 => (fn v8 => (case v8 of
   (Tip) => (Tip)
 | (Bin (v5, v4, v3, v2, v1)) => (if ((((v6 v4) v7) = (Less)) orelse (((v6 v4) v7) = (Equal)))
 then (((trim_help_greater v6) v7) v1)
 else (Bin (v5, v4, v3, v2, v1))))));

fun trim_help_lesser v6 = (fn v7 => (fn v8 => (case v8 of
   (Tip) => (Tip)
 | (Bin (v5, v4, v3, v2, v1)) => (if ((((v6 v4) v7) = (Greater)) orelse (((v6 v4) v7) = (Equal)))
 then (((trim_help_lesser v6) v7) v2)
 else (Bin (v5, v4, v3, v2, v1))))));

fun trim_help_middle v10 = (fn v8 => (fn v11 => (fn v9 => (case (v8, v9) of
   (v7, v6) => (case v6 of
   (Tip) => (Tip)
 | (Bin (v5, v4, v3, v2, v1)) => (if ((((v10 v4) v7) = (Less)) orelse (((v10 v4) v7) = (Equal)))
 then ((((trim_help_middle v10) v7) v11) v1)
 else (if ((((v10 v4) v11) = (Greater)) orelse (((v10 v4) v11) = (Equal)))
 then ((((trim_help_middle v10) v7) v11) v2)
 else (Bin (v5, v4, v3, v2, v1)))))))));

val trim = (fn v4 => (fn v5 => (fn v6 => (fn v7 => (case v5 of
   (NONE) => (case v6 of
   (NONE) => v7
 | (SOME v1) => (((trim_help_lesser v4) v1) v7))
 | (SOME v3) => (case v6 of
   (NONE) => (((trim_help_greater v4) v3) v7)
 | (SOME v2) => ((((trim_help_middle v4) v3) v2) v7)))))));

fun insertmin v6 = (fn v8 => (fn v7 => (case v7 of
   (Tip) => ((singleton v6) v8)
 | (Bin (v5, v4, v3, v2, v1)) => ((((balancel v4) v3) (((insertmin v6) v8) v2)) v1))));

fun insertmax v6 = (fn v8 => (fn v7 => (case v7 of
   (Tip) => ((singleton v6) v8)
 | (Bin (v5, v4, v3, v2, v1)) => ((((balancer v4) v3) v2) (((insertmax v6) v8) v1)))));

val bin = (fn v1 => (fn v4 => (fn v2 => (fn v3 => (Bin ((((size v2) + (size v3)) + 1), v1, v4, v2, v3))))));

fun link v11 = (fn v12 => (fn v13 => (fn v14 => (case v13 of
   (Tip) => (((insertmin v11) v12) v14)
 | (Bin (v10, v9, v8, v7, v6)) => (case v14 of
   (Tip) => (((insertmax v11) v12) (Bin (v10, v9, v8, v7, v6)))
 | (Bin (v5, v4, v3, v2, v1)) => (if ((delta * v10) < v5)
 then ((((balancel v4) v3) ((((link v11) v12) (Bin (v10, v9, v8, v7, v6))) v2)) v1)
 else (if ((delta * v5) < v10)
 then ((((balancer v9) v8) v7) ((((link v11) v12) v6) (Bin (v5, v4, v3, v2, v1))))
 else ((((bin v11) v12) (Bin (v10, v9, v8, v7, v6))) (Bin (v5, v4, v3, v2, v1))))))))));

fun link2 v11 = (fn v12 => (case v12 of
   (Tip) => v11
 | (Bin (v10, v9, v8, v7, v6)) => (case v11 of
   (Tip) => (Bin (v10, v9, v8, v7, v6))
 | (Bin (v5, v4, v3, v2, v1)) => (if ((delta * v5) < v10)
 then ((((balancel v9) v8) ((link2 (Bin (v5, v4, v3, v2, v1))) v7)) v6)
 else (if ((delta * v10) < v5)
 then ((((balancer v4) v3) v2) ((link2 v1) (Bin (v10, v9, v8, v7, v6))))
 else ((glue (Bin (v5, v4, v3, v2, v1))) (Bin (v10, v9, v8, v7, v6))))))));

fun filterlt_help v7 = (fn v6 => (fn v8 => (case v8 of
   (Tip) => (Tip)
 | (Bin (v5, v4, v3, v2, v1)) => (case ((v7 v4) v6) of
   (Less) => ((((link v4) v3) v2) (((filterlt_help v7) v6) v1))
 | (Equal) => v2
 | (Greater) => (((filterlt_help v7) v6) v2)))));

val filterlt = (fn v2 => (fn v3 => (fn v4 => (case v3 of
   (NONE) => v4
 | (SOME v1) => (((filterlt_help v2) v1) v4)))));

fun filtergt_help v7 = (fn v6 => (fn v8 => (case v8 of
   (Tip) => (Tip)
 | (Bin (v5, v4, v3, v2, v1)) => (case ((v7 v6) v4) of
   (Less) => ((((link v4) v3) (((filtergt_help v7) v6) v2)) v1)
 | (Equal) => v1
 | (Greater) => (((filtergt_help v7) v6) v1)))));

val filtergt = (fn v2 => (fn v3 => (fn v4 => (case v3 of
   (NONE) => v4
 | (SOME v1) => (((filtergt_help v2) v1) v4)))));

fun insertr v6 = (fn v7 => (fn v9 => (fn v8 => (case v8 of
   (Tip) => ((singleton v7) v9)
 | (Bin (v5, v4, v3, v2, v1)) => (case ((v6 v7) v4) of
   (Less) => ((((balancel v4) v3) ((((insertr v6) v7) v9) v2)) v1)
 | (Equal) => (Bin (v5, v4, v3, v2, v1))
 | (Greater) => ((((balancer v4) v3) v2) ((((insertr v6) v7) v9) v1)))))));

fun hedgeunion v21 = (fn v22 => (fn v23 => (fn v24 => (fn v25 => (case v25 of
   (Tip) => v24
 | (Bin (v20, v19, v18, v17, v16)) => (case v24 of
   (Tip) => ((((link v19) v18) (((filtergt v21) v22) v17)) (((filterlt v21) v23) v16))
 | (Bin (v15, v14, v13, v12, v11)) => (case v17 of
   (Tip) => (case v16 of
   (Tip) => ((((insertr v21) v19) v18) (Bin (v15, v14, v13, v12, v11)))
 | (Bin (v5, v4, v3, v2, v1)) => ((((link v14) v13) (((((hedgeunion v21) v22) (SOME v14)) v12) ((((trim v21) v22) (SOME v14)) (Bin (v20, v19, v18, (Tip), (Bin (v5, v4, v3, v2, v1))))))) (((((hedgeunion v21) (SOME v14)) v23) v11) ((((trim v21) (SOME v14)) v23) (Bin (v20, v19, v18, (Tip), (Bin (v5, v4, v3, v2, v1))))))))
 | (Bin (v10, v9, v8, v7, v6)) => ((((link v14) v13) (((((hedgeunion v21) v22) (SOME v14)) v12) ((((trim v21) v22) (SOME v14)) (Bin (v20, v19, v18, (Bin (v10, v9, v8, v7, v6)), v16))))) (((((hedgeunion v21) (SOME v14)) v23) v11) ((((trim v21) (SOME v14)) v23) (Bin (v20, v19, v18, (Bin (v10, v9, v8, v7, v6)), v16))))))))))));

fun lookup v6 = (fn v7 => (fn v8 => (case v8 of
   (Tip) => (NONE)
 | (Bin (v5, v4, v3, v2, v1)) => (case ((v6 v7) v4) of
   (Less) => (((lookup v6) v7) v2)
 | (Equal) => (SOME v3)
 | (Greater) => (((lookup v6) v7) v1)))));

fun hedgeunionwithkey v21 = (fn v22 => (fn v23 => (fn v24 => (fn v25 => (fn v26 => (case (v22, (v23, (v24, (v25, v26)))) of
   (v20, v19) => (case v19 of
   (v18, v17) => (case v17 of
   (v16, v15) => (case v15 of
   (v14, v13) => (case v13 of
   (Tip) => v14
 | (Bin (v12, v11, v10, v9, v8)) => (case v14 of
   (Tip) => ((((link v11) v10) (((filtergt v21) v18) v9)) (((filterlt v21) v16) v8))
 | (Bin (v7, v6, v5, v4, v3)) => (let val v1 = (case (((lookup v21) v6) (Bin (v12, v11, v10, v9, v8))) of
   (NONE) => v5
 | (SOME v2) => (((v20 v6) v5) v2))
 in ((((link v6) v1) ((((((hedgeunionwithkey v21) v20) v18) (SOME v6)) v4) ((((trim v21) v18) (SOME v6)) (Bin (v12, v11, v10, v9, v8))))) ((((((hedgeunionwithkey v21) v20) (SOME v6)) v16) v3) ((((trim v21) (SOME v6)) v16) (Bin (v12, v11, v10, v9, v8))))) end))))))))))));

fun splitlookup v18 = (fn v19 => (fn v20 => (case v20 of
   (Tip) => ((Tip), ((NONE), (Tip)))
 | (Bin (v17, v16, v15, v14, v13)) => (case ((v18 v19) v16) of
   (Less) => (let val v6 = (((splitlookup v18) v19) v14)
 in (case v6 of
   (v5, v4) => (case v4 of
   (v3, v2) => (let val v1 = ((((link v16) v15) v2) v13)
 in (v5, (v3, v1)) end))) end)
 | (Equal) => (v14, ((SOME v15), v13))
 | (Greater) => (let val v12 = (((splitlookup v18) v19) v13)
 in (case v12 of
   (v11, v10) => (case v10 of
   (v9, v8) => (let val v7 = ((((link v16) v15) v14) v11)
 in (v7, (v9, v8)) end))) end)))));

fun submap' v18 = (fn v19 => (fn v20 => (fn v21 => (case (v20, v21) of
   (v17, v16) => (case v17 of
   (Tip) => (0 <= 0)
 | (Bin (v15, v14, v13, v12, v11)) => (case v16 of
   (Tip) => (0 < 0)
 | (Bin (v10, v9, v8, v7, v6)) => (case (((splitlookup v18) v14) (Bin (v10, v9, v8, v7, v6))) of
   (v5, v4) => (case v4 of
   (v3, v2) => (case v3 of
   (NONE) => (0 < 0)
 | (SOME v1) => ((((v19 v13) v1) andalso ((((submap' v18) v19) v12) v5)) andalso ((((submap' v18) v19) v11) v2)))))))))));

val null = (fn v6 => (case v6 of
   (Tip) => (0 <= 0)
 | (Bin (v5, v4, v3, v2, v1)) => (0 < 0)));

fun member v6 = (fn v7 => (fn v8 => (case v8 of
   (Tip) => (0 < 0)
 | (Bin (v5, v4, v3, v2, v1)) => (case ((v6 v7) v4) of
   (Less) => (((member v6) v7) v2)
 | (Equal) => (0 <= 0)
 | (Greater) => (((member v6) v7) v1)))));

val empty = (Tip);

fun insert v6 = (fn v7 => (fn v9 => (fn v8 => (case v8 of
   (Tip) => ((singleton v7) v9)
 | (Bin (v5, v4, v3, v2, v1)) => (case ((v6 v7) v4) of
   (Less) => ((((balancel v4) v3) ((((insert v6) v7) v9) v2)) v1)
 | (Equal) => (Bin (v5, v7, v9, v2, v1))
 | (Greater) => ((((balancer v4) v3) v2) ((((insert v6) v7) v9) v1)))))));

fun delete v6 = (fn v7 => (fn v8 => (case v8 of
   (Tip) => (Tip)
 | (Bin (v5, v4, v3, v2, v1)) => (case ((v6 v7) v4) of
   (Less) => ((((balancer v4) v3) (((delete v6) v7) v2)) v1)
 | (Equal) => ((glue v2) v1)
 | (Greater) => ((((balancel v4) v3) v2) (((delete v6) v7) v1))))));

val union = (fn v11 => (fn v12 => (fn v13 => (case v12 of
   (Tip) => v13
 | (Bin (v10, v9, v8, v7, v6)) => (case v13 of
   (Tip) => (Bin (v10, v9, v8, v7, v6))
 | (Bin (v5, v4, v3, v2, v1)) => (((((hedgeunion v11) (NONE)) (NONE)) (Bin (v10, v9, v8, v7, v6))) (Bin (v5, v4, v3, v2, v1))))))));

val unionWithKey = (fn v15 => (fn v16 => (fn v17 => (fn v18 => (case (v16, (v17, v18)) of
   (v14, v13) => (case v13 of
   (v12, v11) => (case v12 of
   (Tip) => v11
 | (Bin (v10, v9, v8, v7, v6)) => (case v11 of
   (Tip) => (Bin (v10, v9, v8, v7, v6))
 | (Bin (v5, v4, v3, v2, v1)) => ((((((hedgeunionwithkey v15) v14) (NONE)) (NONE)) (Bin (v10, v9, v8, v7, v6))) (Bin (v5, v4, v3, v2, v1)))))))))));

val unionWith = (fn v4 => (fn v5 => (fn v6 => (fn v7 => ((((unionWithKey v4) (fn v3 => (fn v2 => (fn v1 => ((v5 v2) v1))))) v6) v7)))));

fun foldrWithKey v6 = (fn v8 => (fn v7 => (case v7 of
   (Tip) => v8
 | (Bin (v5, v4, v3, v2, v1)) => (((foldrWithKey v6) (((v6 v4) v3) (((foldrWithKey v6) v8) v1))) v2))));

val toAscList = (fn v4 => (((foldrWithKey (fn v3 => (fn v2 => (fn v1 => ((v3, v2) :: v1))))) []) v4));

val compare = (fn v1 => (fn v2 => (fn v3 => (fn v4 => (((CML_List.compare ((CML_Pair.compare v1) v2)) (toAscList v3)) (toAscList v4))))));

fun mapWithKey v6 = (fn v7 => (case v7 of
   (Tip) => (Tip)
 | (Bin (v5, v4, v3, v2, v1)) => (Bin (v5, v4, ((v6 v4) v3), ((mapWithKey v6) v2), ((mapWithKey v6) v1)))));

val map = (fn v3 => (fn v4 => ((mapWithKey (fn v2 => (fn v1 => (v3 v1)))) v4)));

val isSubmapOfBy = (fn v1 => (fn v2 => (fn v3 => (fn v4 => (((size v3) <= (size v4)) andalso ((((submap' v1) v2) v3) v4))))));

val isSubmapOf = (fn v3 => (fn v4 => (fn v5 => ((((isSubmapOfBy v3) (fn v2 => (fn v1 => (v2 = v1)))) v4) v5))));

val fromList = (fn v5 => (fn v6 => (((CML_List.foldr (fn v4 => (case v4 of
   (v3, v2) => (fn v1 => ((((insert v5) v3) v2) v1))))) empty) v6)));

fun filterWithKey v8 = (fn v9 => (case v9 of
   (Tip) => (Tip)
 | (Bin (v7, v6, v5, v4, v3)) => (let val v2 = ((filterWithKey v8) v4)
 in (let val v1 = ((filterWithKey v8) v3)
 in (if ((v8 v6) v5)
 then ((((link v6) v5) v2) v1)
 else ((link2 v2) v1)) end) end)));

val filter = (fn v3 => (fn v4 => ((filterWithKey (fn v2 => (fn v1 => (v3 v1)))) v4)));

fun all v6 = (fn v7 => (case v7 of
   (Tip) => (0 <= 0)
 | (Bin (v5, v4, v3, v2, v1)) => (if ((v6 v4) v3)
 then (if ((all v6) v2)
 then (if ((all v6) v1)
 then (0 <= 0)
 else (0 < 0))
 else (0 < 0))
 else (0 < 0))));

fun exists v6 = (fn v7 => (case v7 of
   (Tip) => (0 < 0)
 | (Bin (v5, v4, v3, v2, v1)) => (if ((v6 v4) v3)
 then (0 <= 0)
 else (if ((exists v6) v2)
 then (0 <= 0)
 else (if ((exists v6) v1)
 then (0 <= 0)
 else (0 < 0))))));

in
structure CML_Map = struct
type ('a, 'b) map = ('a, 'b) map;

val lookup = (fn v4 => (fn v3 => (case v4 of
   (Map (v2, v1)) => (((lookup v2) v3) v1))));

val insert = (fn v5 => (fn v3 => (fn v4 => (case v5 of
   (Map (v2, v1)) => (Map (v2, ((((insert v2) v3) v4) v1)))))));

val delete = (fn v4 => (fn v3 => (case v4 of
   (Map (v2, v1)) => (Map (v2, (((delete v2) v3) v1))))));

val null = (fn v3 => (case v3 of
   (Map (v2, v1)) => (null v1)));

val size = (fn v3 => (case v3 of
   (Map (v2, v1)) => (size v1)));

val empty = (fn v1 => (Map (v1, empty)));

val union = (fn v6 => (fn v5 => (case v6 of
   (Map (v4, v3)) => (case v5 of
   (Map (v2, v1)) => (Map (v4, (((union v4) v3) v1)))))));

val unionWith = (fn v5 => (fn v7 => (fn v6 => (case v7 of
   (Map (v4, v3)) => (case v6 of
   (Map (v2, v1)) => (Map (v4, ((((unionWith v4) v5) v3) v1))))))));

val unionWithKey = (fn v5 => (fn v7 => (fn v6 => (case v7 of
   (Map (v4, v3)) => (case v6 of
   (Map (v2, v1)) => (Map (v4, ((((unionWithKey v4) v5) v3) v1))))))));

val foldrWithKey = (fn v3 => (fn v5 => (fn v4 => (case v4 of
   (Map (v2, v1)) => (((foldrWithKey v3) v5) v1)))));

val map = (fn v3 => (fn v4 => (case v4 of
   (Map (v2, v1)) => (Map (v2, ((map v3) v1))))));

val mapWithKey = (fn v3 => (fn v4 => (case v4 of
   (Map (v2, v1)) => (Map (v2, ((mapWithKey v3) v1))))));

val toAscList = (fn v3 => (case v3 of
   (Map (v2, v1)) => (toAscList v1)));

val fromList = (fn v1 => (fn v2 => (Map (v1, ((fromList v1) v2)))));

val isSubmapBy = (fn v5 => (fn v7 => (fn v6 => (case v7 of
   (Map (v4, v3)) => (case v6 of
   (Map (v2, v1)) => ((((isSubmapOfBy v4) v5) v3) v1))))));

val isSubmap = (fn v3 => (fn v4 => (((isSubmapBy (fn v2 => (fn v1 => (v2 = v1)))) v3) v4)));

val all = (fn v3 => (fn v4 => (case v4 of
   (Map (v2, v1)) => ((all v3) v1))));

val exists = (fn v3 => (fn v4 => (case v4 of
   (Map (v2, v1)) => ((exists v3) v1))));

val filterWithKey = (fn v3 => (fn v4 => (case v4 of
   (Map (v2, v1)) => (Map (v2, ((filterWithKey v3) v1))))));

val filter = (fn v3 => (fn v4 => (case v4 of
   (Map (v2, v1)) => (Map (v2, ((filter v3) v1))))));

end;

type ('a, 'b) map = ('a, 'b) map;

end;

structure CML_CommandLine = struct
local
fun read16bit a = (let val w0 = ((CML_Word8Array.sub a) 0)
 in (let val w1 = ((CML_Word8Array.sub a) 1)
 in (let val cml_x32v1 = (CML_Word8.toInt w1)
 in (let val cml_x32v2 = ((cml_x42 cml_x32v1) 256)
 in (let val cml_x32v0 = (CML_Word8.toInt w0)
 in ((cml_x43 cml_x32v0) cml_x32v2) end) end) end) end) end);

fun write16bit a = (fn i => (let val cml_x32v0 = (CML_Word8.fromInt i)
 in (let val _ = (((CML_Word8Array.update a) 0) cml_x32v0)
 in (let val cml_x32v1 = ((cml_div i) 256)
 in (let val cml_x32v2 = (CML_Word8.fromInt cml_x32v1)
 in (((CML_Word8Array.update a) 1) cml_x32v2) end) end) end) end));

fun cloop a = (fn n => (fn acc => (let val cml_x32v0 = ((cml_x61 n) 0)
 in (if cml_x32v0
 then acc
 else (let val n = ((cml_x45 n) 1)
 in (let val u = ((write16bit a) n)
 in (let val u = (CMLffi.call "get_arg_length" ("", a))
 in (let val l = (read16bit a)
 in (let val cml_x32v2 = (CML_Word8.fromInt 0)
 in (let val cml_x32v1 = ((max 2) l)
 in (let val tmp = ((CML_Word8Array.array cml_x32v1) cml_x32v2)
 in (let val u = ((write16bit tmp) n)
 in (let val u = (CMLffi.call "get_arg" ("", tmp))
 in (let val arg = (((CML_Word8Array.substring tmp) 0) l)
 in (let val cml_x32v3 = (arg :: acc)
 in (((cloop a) n) cml_x32v3) end) end) end) end) end) end) end) end) end) end) end)) end)));

in
fun cline u = (case u of
   () => (let val cml_x32v0 = (CML_Word8.fromInt 0)
 in (let val a = ((CML_Word8Array.array 2) cml_x32v0)
 in (let val u = (CMLffi.call "get_arg_count" ("", a))
 in (let val n = (read16bit a)
 in (let val cml_x32v1 = []
 in (((cloop a) n) cml_x32v1) end) end) end) end) end));

fun name u = (let val cml_x32v0 = (cline u)
 in (CML_List.hd cml_x32v0) end);

fun arguments u = (let val cml_x32v0 = (cline u)
 in (CML_List.tl cml_x32v0) end);

end;

end;

structure CML_Marshalling = struct
fun n2w2 n = (fn bytes => (fn off => (let val cml_x32v0 = ((cml_div n) 256)
 in (let val cml_x32v1 = (CML_Word8.fromInt cml_x32v0)
 in (let val a = (((CML_Word8Array.update bytes) off) cml_x32v1)
 in (let val cml_x32v3 = (CML_Word8.fromInt n)
 in (let val cml_x32v2 = ((cml_x43 off) 1)
 in (let val a = (((CML_Word8Array.update bytes) cml_x32v2) cml_x32v3)
 in () end) end) end) end) end) end)));

fun w22n bytes = (fn off => (let val b1 = ((CML_Word8Array.sub bytes) off)
 in (let val cml_x32v0 = ((cml_x43 off) 1)
 in (let val b0 = ((CML_Word8Array.sub bytes) cml_x32v0)
 in (let val cml_x32v3 = (CML_Word8.toInt b0)
 in (let val cml_x32v1 = (CML_Word8.toInt b1)
 in (let val cml_x32v2 = ((cml_x42 cml_x32v1) 256)
 in ((cml_x43 cml_x32v2) cml_x32v3) end) end) end) end) end) end));

end;

structure CML_TextIO = struct
local
datatype instream = Instream of string;

datatype outstream = Outstream of string;

datatype instreambuffered = InstreamBuffered of instream * (int) ref * (int) ref * byte_array;

val get_out = (fn v2 => (case v2 of
   (Outstream v1) => v1));

val get_in = (fn v2 => (case v2 of
   (Instream v1) => v1));

in
type instream = instream;

type outstream = outstream;

type b_instream = instreambuffered;

exception BadFileName;

exception InvalidFD;

exception EndOfFile;

exception IllegalArgument;

local
val iobuff = (Word8Array.array (2052, (0wx0 : Word8.word)));

in
val stdIn = (Instream "\^@\^@\^@\^@\^@\^@\^@\^@");

val stdOut = (Outstream "\^@\^@\^@\^@\^@\^@\^@\^A");

val stdErr = (Outstream "\^@\^@\^@\^@\^@\^@\^@\^B");

local
fun writei fd = (fn n => (fn i => (let val a = (((CML_Marshalling.n2w2 n) iobuff) 0)
 in (let val a = (((CML_Marshalling.n2w2 i) iobuff) 2)
 in (let val a = (CMLffi.call "write" (fd, iobuff))
 in (let val cml_x32v1 = (CML_Word8.fromInt 1)
 in (let val cml_x32v0 = ((CML_Word8Array.sub iobuff) 0)
 in (let val cml_x32v2 = ((cml_x61 cml_x32v0) cml_x32v1)
 in (if cml_x32v2
 then (let val cml_x32v3 = (InvalidFD)
 in (raise cml_x32v3) end)
 else (let val nw = ((CML_Marshalling.w22n iobuff) 1)
 in (let val cml_x32v4 = ((cml_x61 nw) 0)
 in (if cml_x32v4
 then (((writei fd) n) i)
 else nw) end) end)) end) end) end) end) end) end)));

fun write fd = (fn n => (fn i => (let val cml_x32v0 = ((cml_x61 n) 0)
 in (if cml_x32v0
 then ()
 else (let val nw = (((writei fd) n) i)
 in (let val cml_x32v1 = ((cml_x60 nw) n)
 in (if cml_x32v1
 then (let val cml_x32v3 = ((cml_x43 i) nw)
 in (let val cml_x32v2 = ((cml_x45 n) nw)
 in (((write fd) cml_x32v2) cml_x32v3) end) end)
 else ()) end) end)) end)));

in
fun output1 fd = (fn c => (let val cml_x32v0 = (CML_Char.ord c)
 in (let val cml_x32v1 = (CML_Word8.fromInt cml_x32v0)
 in (let val _ = (((CML_Word8Array.update iobuff) 4) cml_x32v1)
 in (let val cml_x32v2 = (get_out fd)
 in (let val _ = (((write cml_x32v2) 1) 0)
 in () end) end) end) end) end));

fun output fd = (fn s => (let val cml_x32v0 = ((cml_x61 s) "")
 in (if cml_x32v0
 then ()
 else (let val z = (CML_String.size s)
 in (let val cml_x32v1 = ((cml_x60x61 z) 2048)
 in (let val n = (if cml_x32v1
 then z
 else 2048)
 in (let val fl = (((((CML_Word8Array.copyVec s) 0) n) iobuff) 4)
 in (let val cml_x32v2 = (get_out fd)
 in (let val a = (((write cml_x32v2) n) 0)
 in (let val cml_x32v3 = ((cml_x45 z) n)
 in (let val cml_x32v4 = (((CML_String.substring s) n) cml_x32v3)
 in ((output fd) cml_x32v4) end) end) end) end) end) end) end) end)) end));

fun cml_print s = ((output stdOut) s);

fun print_err s = ((output stdErr) s);

fun print_list ls = (case ls of
   [] => ()
 | (x :: xs) => (let val _ = (cml_print x)
 in (print_list xs) end));

fun openIn fname = (let val cml_x32v0 = (CML_Word8.fromInt 0)
 in (let val b = ((CML_Word8Array.array 9) cml_x32v0)
 in (let val cml_x32v1 = (CML_Char.chr 0)
 in (let val cml_x32v2 = (CML_String.str cml_x32v1)
 in (let val cml_x32v3 = ((cml_x94 fname) cml_x32v2)
 in (let val a = (CMLffi.call "open_in" (cml_x32v3, b))
 in (let val cml_x32v5 = (CML_Word8.fromInt 0)
 in (let val cml_x32v4 = ((CML_Word8Array.sub b) 0)
 in (let val cml_x32v6 = ((cml_x61 cml_x32v4) cml_x32v5)
 in (if cml_x32v6
 then (let val cml_x32v7 = (((CML_Word8Array.substring b) 1) 8)
 in (Instream cml_x32v7) end)
 else (let val cml_x32v8 = (BadFileName)
 in (raise cml_x32v8) end)) end) end) end) end) end) end) end) end) end);

fun openOut fname = (let val cml_x32v0 = (CML_Word8.fromInt 0)
 in (let val b = ((CML_Word8Array.array 9) cml_x32v0)
 in (let val cml_x32v1 = (CML_Char.chr 0)
 in (let val cml_x32v2 = (CML_String.str cml_x32v1)
 in (let val cml_x32v3 = ((cml_x94 fname) cml_x32v2)
 in (let val a = (CMLffi.call "open_out" (cml_x32v3, b))
 in (let val cml_x32v5 = (CML_Word8.fromInt 0)
 in (let val cml_x32v4 = ((CML_Word8Array.sub b) 0)
 in (let val cml_x32v6 = ((cml_x61 cml_x32v4) cml_x32v5)
 in (if cml_x32v6
 then (let val cml_x32v7 = (((CML_Word8Array.substring b) 1) 8)
 in (Outstream cml_x32v7) end)
 else (let val cml_x32v8 = (BadFileName)
 in (raise cml_x32v8) end)) end) end) end) end) end) end) end) end) end);

fun closeOut fd = (let val cml_x32v0 = (get_out fd)
 in (let val a = (CMLffi.call "close" (cml_x32v0, iobuff))
 in (let val cml_x32v2 = (CML_Word8.fromInt 0)
 in (let val cml_x32v1 = ((CML_Word8Array.sub iobuff) 0)
 in (let val cml_x32v3 = ((cml_x61 cml_x32v1) cml_x32v2)
 in (if cml_x32v3
 then ()
 else (let val cml_x32v4 = (InvalidFD)
 in (raise cml_x32v4) end)) end) end) end) end) end);

fun closeIn fd = (let val cml_x32v0 = (get_in fd)
 in (let val a = (CMLffi.call "close" (cml_x32v0, iobuff))
 in (let val cml_x32v2 = (CML_Word8.fromInt 0)
 in (let val cml_x32v1 = ((CML_Word8Array.sub iobuff) 0)
 in (let val cml_x32v3 = ((cml_x61 cml_x32v1) cml_x32v2)
 in (if cml_x32v3
 then ()
 else (let val cml_x32v4 = (InvalidFD)
 in (raise cml_x32v4) end)) end) end) end) end) end);

local
fun read fd = (fn n => (let val a = (((CML_Marshalling.n2w2 n) iobuff) 0)
 in (let val _ = (CMLffi.call "read" (fd, iobuff))
 in (let val cml_x32v0 = ((CML_Word8Array.sub iobuff) 0)
 in (let val cml_x32v1 = (CML_Word8.toInt cml_x32v0)
 in (let val cml_x32v2 = ((cml_x60x62 cml_x32v1) 1)
 in (if cml_x32v2
 then ((CML_Marshalling.w22n iobuff) 1)
 else (let val cml_x32v3 = (InvalidFD)
 in (raise cml_x32v3) end)) end) end) end) end) end));

fun read_byte fd = (let val cml_x32v0 = ((read fd) 1)
 in (let val cml_x32v1 = ((cml_x61 cml_x32v0) 0)
 in (if cml_x32v1
 then (let val cml_x32v2 = (EndOfFile)
 in (raise cml_x32v2) end)
 else ((CML_Word8Array.sub iobuff) 4)) end) end);

fun input fd = (fn buff => (fn off => (fn len => (let fun input0 off = (fn len => (fn count => (let val cml_x32v1 = ((min len) 2048)
 in (let val cml_x32v0 = (get_in fd)
 in (let val nread = ((read cml_x32v0) cml_x32v1)
 in (let val cml_x32v2 = ((cml_x61 nread) 0)
 in (if cml_x32v2
 then count
 else (let val _ = (((((CML_Word8Array.copy iobuff) 4) nread) buff) off)
 in (let val cml_x32v5 = ((cml_x43 count) nread)
 in (let val cml_x32v4 = ((cml_x45 len) nread)
 in (let val cml_x32v3 = ((cml_x43 off) nread)
 in (((input0 cml_x32v3) cml_x32v4) cml_x32v5) end) end) end) end)) end) end) end) end)))
 in (((input0 off) len) 0) end))));

in
fun input1 fd = ((let val cml_x32v0 = (get_in fd)
 in (let val cml_x32v1 = (read_byte cml_x32v0)
 in (let val cml_x32v2 = (CML_Char.fromByte cml_x32v1)
 in (CML_Char.some cml_x32v2) end) end) end)
 handle (EndOfFile) => (NONE));

local
fun extend_array arr = (let val len = (CML_Word8Array.length arr)
 in (let val cml_x32v1 = (CML_Word8.fromInt 0)
 in (let val cml_x32v0 = ((cml_x42 2) len)
 in (let val arr' = ((CML_Word8Array.array cml_x32v0) cml_x32v1)
 in (let val _ = (((((CML_Word8Array.copy arr) 0) len) arr') 0)
 in arr' end) end) end) end) end);

in
fun inputLine fd = (let val cml_x32v0 = (CML_Char.ord #"\n")
 in (let val nl = (CML_Word8.fromInt cml_x32v0)
 in (let fun inputLine_aux arr = (fn i => (let val cml_x32v1 = (CML_Word8Array.length arr)
 in (let val cml_x32v2 = ((cml_x60 i) cml_x32v1)
 in (if cml_x32v2
 then ((let val cml_x32v3 = (get_in fd)
 in (let val c = (read_byte cml_x32v3)
 in (let val u = (((CML_Word8Array.update arr) i) c)
 in (let val cml_x32v4 = ((cml_x61 c) nl)
 in (if cml_x32v4
 then (let val cml_x32v5 = ((cml_x43 i) 1)
 in (let val cml_x32v6 = (((CML_Word8Array.substring arr) 0) cml_x32v5)
 in (SOME cml_x32v6) end) end)
 else (let val cml_x32v7 = ((cml_x43 i) 1)
 in ((inputLine_aux arr) cml_x32v7) end)) end) end) end) end)
 handle (EndOfFile) => (let val cml_x32v8 = ((cml_x61 i) 0)
 in (if cml_x32v8
 then (NONE)
 else (let val _ = (((CML_Word8Array.update arr) i) nl)
 in (let val cml_x32v9 = ((cml_x43 i) 1)
 in (let val cml_x32v10 = (((CML_Word8Array.substring arr) 0) cml_x32v9)
 in (SOME cml_x32v10) end) end) end)) end))
 else (let val cml_x32v11 = (extend_array arr)
 in ((inputLine_aux cml_x32v11) i) end)) end) end))
 in (let val cml_x32v12 = (CML_Word8.fromInt 0)
 in (let val cml_x32v13 = ((CML_Word8Array.array 127) cml_x32v12)
 in ((inputLine_aux cml_x32v13) 0) end) end) end) end) end);

fun inputLines fd = (let val cml_x32v0 = (inputLine fd)
 in (case cml_x32v0 of
   (NONE) => []
 | (SOME l) => (let val cml_x32v1 = (inputLines fd)
 in (l :: cml_x32v1) end)) end);

fun inputLinesFrom fname = ((let val fd = (openIn fname)
 in (let val lines = (inputLines fd)
 in (let val _ = (closeIn fd)
 in (SOME lines) end) end) end)
 handle (BadFileName) => (NONE));

fun inputAll fd = (let fun inputAll_aux arr = (fn i => (let val len = (CML_Word8Array.length arr)
 in (let val cml_x32v0 = ((cml_x60 i) len)
 in (if cml_x32v0
 then (let val cml_x32v1 = ((cml_x45 len) i)
 in (let val n = ((((input fd) arr) i) cml_x32v1)
 in (let val cml_x32v2 = ((cml_x61 n) 0)
 in (if cml_x32v2
 then (((CML_Word8Array.substring arr) 0) i)
 else (let val cml_x32v3 = ((cml_x43 i) n)
 in ((inputAll_aux arr) cml_x32v3) end)) end) end) end)
 else (let val cml_x32v4 = (extend_array arr)
 in ((inputAll_aux cml_x32v4) i) end)) end) end))
 in (let val cml_x32v5 = (CML_Word8.fromInt 0)
 in (let val cml_x32v6 = ((CML_Word8Array.array 127) cml_x32v5)
 in ((inputAll_aux cml_x32v6) 0) end) end) end);

fun copy inp = (fn out => (let val cml_x32v0 = (get_in inp)
 in (let val nr = ((read cml_x32v0) 2048)
 in (let val cml_x32v1 = ((cml_x61 nr) 0)
 in (if cml_x32v1
 then ()
 else (let val cml_x32v2 = (get_out out)
 in (let val _ = (((write cml_x32v2) nr) 0)
 in ((copy inp) out) end) end)) end) end) end));

fun b_openStdInSetBufferSize bsize = (let val cml_x32v5 = (CML_Word8.fromInt 48)
 in (let val cml_x32v2 = ((cml_x43 bsize) 4)
 in (let val cml_x32v3 = ((max cml_x32v2) 1028)
 in (let val cml_x32v4 = ((min 65535) cml_x32v3)
 in (let val cml_x32v6 = ((CML_Word8Array.array cml_x32v4) cml_x32v5)
 in (let val cml_x32v1 = (ref 4)
 in (let val cml_x32v0 = (ref 4)
 in (InstreamBuffered (stdIn, cml_x32v0, cml_x32v1, cml_x32v6)) end) end) end) end) end) end) end);

fun b_openStdIn cml_ = (case cml_ of
   () => (b_openStdInSetBufferSize 4096));

fun b_openInSetBufferSize fname = (fn bsize => (let val is = (openIn fname)
 in (let val cml_x32v5 = (CML_Word8.fromInt 48)
 in (let val cml_x32v2 = ((cml_x43 bsize) 4)
 in (let val cml_x32v3 = ((max cml_x32v2) 1028)
 in (let val cml_x32v4 = ((min 65535) cml_x32v3)
 in (let val cml_x32v6 = ((CML_Word8Array.array cml_x32v4) cml_x32v5)
 in (let val cml_x32v1 = (ref 4)
 in (let val cml_x32v0 = (ref 4)
 in (InstreamBuffered (is, cml_x32v0, cml_x32v1, cml_x32v6)) end) end) end) end) end) end) end) end));

fun b_openIn fname = ((b_openInSetBufferSize fname) 4096);

fun b_closeIn is = (case is of
   (InstreamBuffered (fd, rref, wref, surplus)) => (closeIn fd));

local
fun b_input_aux is = (fn buff => (fn off => (fn len => (case is of
   (InstreamBuffered (fd, rref, wref, surplus)) => (let val readat = (cml_x33 rref)
 in (let val _ = (((((CML_Word8Array.copy surplus) readat) len) buff) off)
 in (let val cml_x32v0 = ((cml_x43 readat) len)
 in (let val _ = ((cml_x58x61 rref) cml_x32v0)
 in len end) end) end) end)))));

in
fun b_input is = (fn buff => (fn off => (fn len => (case is of
   (InstreamBuffered (fd, rref, wref, surplus)) => (let val cml_x32v1 = (cml_x33 rref)
 in (let val cml_x32v0 = (cml_x33 wref)
 in (let val nBuffered = ((cml_x45 cml_x32v0) cml_x32v1)
 in (let val cml_x32v3 = ((cml_x43 len) off)
 in (let val cml_x32v2 = (CML_Word8Array.length buff)
 in (let val cml_x32v4 = ((cml_x60 cml_x32v2) cml_x32v3)
 in (if cml_x32v4
 then (let val cml_x32v5 = (IllegalArgument)
 in (raise cml_x32v5) end)
 else (let val cml_x32v6 = (CML_Word8Array.length surplus)
 in (let val cml_x32v7 = ((cml_x45 cml_x32v6) 4)
 in (let val cml_x32v8 = ((cml_x60 cml_x32v7) len)
 in (if cml_x32v8
 then (let val _ = ((((b_input_aux is) buff) off) nBuffered)
 in (let val cml_x32v10 = ((cml_x45 len) nBuffered)
 in (let val cml_x32v9 = ((cml_x43 off) nBuffered)
 in (let val cml_x32v11 = ((((input fd) buff) cml_x32v9) cml_x32v10)
 in ((cml_x43 cml_x32v11) nBuffered) end) end) end) end)
 else (let val cml_x32v12 = ((cml_x62 len) nBuffered)
 in (if cml_x32v12
 then (let val _ = ((((b_input_aux is) buff) off) nBuffered)
 in (let val cml_x32v13 = (CML_Word8Array.length surplus)
 in (let val cml_x32v14 = ((cml_x45 cml_x32v13) 4)
 in (let val cml_x32v15 = ((((input fd) surplus) 4) cml_x32v14)
 in (let val cml_x32v16 = ((cml_x43 4) cml_x32v15)
 in (let val _ = ((cml_x58x61 wref) cml_x32v16)
 in (let val _ = ((cml_x58x61 rref) 4)
 in (let val cml_x32v20 = ((cml_x45 len) nBuffered)
 in (let val cml_x32v18 = (cml_x33 wref)
 in (let val cml_x32v19 = ((cml_x45 cml_x32v18) 4)
 in (let val cml_x32v21 = ((min cml_x32v19) cml_x32v20)
 in (let val cml_x32v17 = ((cml_x43 off) nBuffered)
 in (let val cml_x32v22 = ((((b_input_aux is) buff) cml_x32v17) cml_x32v21)
 in ((cml_x43 cml_x32v22) nBuffered) end) end) end) end) end) end) end) end) end) end) end) end) end)
 else ((((b_input_aux is) buff) off) len)) end)) end) end) end)) end) end) end) end) end) end)))));

local
fun read_into fd = (fn buff => (fn n => (let val a = (((CML_Marshalling.n2w2 n) buff) 0)
 in (let val _ = (CMLffi.call "read" (fd, buff))
 in (let val cml_x32v0 = ((CML_Word8Array.sub buff) 0)
 in (let val cml_x32v1 = (CML_Word8.toInt cml_x32v0)
 in (let val cml_x32v2 = ((cml_x60x62 cml_x32v1) 1)
 in (if cml_x32v2
 then ((CML_Marshalling.w22n buff) 1)
 else (let val cml_x32v3 = (InvalidFD)
 in (raise cml_x32v3) end)) end) end) end) end) end)));

in
local
fun b_refillBuffer_with_read is = (case is of
   (InstreamBuffered (fd, rref, wref, surplus)) => (let val cml_x32v1 = (CML_Word8Array.length surplus)
 in (let val cml_x32v2 = ((cml_x45 cml_x32v1) 4)
 in (let val cml_x32v0 = (get_in fd)
 in (let val cml_x32v3 = (((read_into cml_x32v0) surplus) cml_x32v2)
 in (let val cml_x32v4 = ((cml_x43 4) cml_x32v3)
 in (let val _ = ((cml_x58x61 wref) cml_x32v4)
 in (let val _ = ((cml_x58x61 rref) 4)
 in (let val cml_x32v5 = (cml_x33 wref)
 in ((cml_x45 cml_x32v5) 4) end) end) end) end) end) end) end) end));

fun b_input1_aux is = (case is of
   (InstreamBuffered (fd, rref, wref, surplus)) => (let val readat = (cml_x33 rref)
 in (let val cml_x32v0 = (cml_x33 wref)
 in (let val cml_x32v1 = ((cml_x61 cml_x32v0) readat)
 in (if cml_x32v1
 then (NONE)
 else (let val cml_x32v2 = ((cml_x43 readat) 1)
 in (let val _ = ((cml_x58x61 rref) cml_x32v2)
 in (let val cml_x32v3 = ((CML_Word8Array.sub surplus) readat)
 in (let val cml_x32v4 = (CML_Char.fromByte cml_x32v3)
 in (CML_Char.some cml_x32v4) end) end) end) end)) end) end) end));

in
fun b_input1 is = (case is of
   (InstreamBuffered (fd, rref, wref, surplus)) => (let val cml_x32v1 = (cml_x33 rref)
 in (let val cml_x32v0 = (cml_x33 wref)
 in (let val cml_x32v2 = ((cml_x61 cml_x32v0) cml_x32v1)
 in (if cml_x32v2
 then (let val _ = (b_refillBuffer_with_read is)
 in (b_input1_aux is) end)
 else (b_input1_aux is)) end) end) end));

local
fun b_inputUntil_aux is = (fn cml_ => (case cml_ of
   chr => (let val cml_x32v0 = (b_input1 is)
 in (case cml_x32v0 of
   (SOME c) => (let val cml_x32v1 = ((cml_x60x62 c) chr)
 in (if cml_x32v1
 then (let val cml_x32v2 = ((b_inputUntil_aux is) chr)
 in (c :: cml_x32v2) end)
 else (let val cml_x32v3 = []
 in (c :: cml_x32v3) end)) end)
 | (NONE) => []) end)));

val compress = (fn v1 => (String.implode (CML_List.rev v1)));

fun b_inputLine_aux is = (fn k => (fn chrs => (fn strs => (let val cml_x32v0 = (b_input1 is)
 in (case cml_x32v0 of
   (NONE) => (let val cml_x32v1 = (CML_List.null chrs)
 in (let val cml_x32v3 = (cml_x32v1 andalso (CML_List.null strs))
 in (if cml_x32v3
 then (NONE)
 else (let val cml_x32v4 = (#"\n" :: chrs)
 in (let val cml_x32v5 = (compress cml_x32v4)
 in (let val cml_x32v6 = (cml_x32v5 :: strs)
 in (let val cml_x32v7 = (CML_List.rev cml_x32v6)
 in (let val cml_x32v8 = (CML_String.concat cml_x32v7)
 in (SOME cml_x32v8) end) end) end) end) end)) end) end)
 | (SOME c) => (let val cml_x32v9 = ((cml_x61 c) #"\n")
 in (if cml_x32v9
 then (let val cml_x32v10 = (c :: chrs)
 in (let val cml_x32v11 = (compress cml_x32v10)
 in (let val cml_x32v12 = (cml_x32v11 :: strs)
 in (let val cml_x32v13 = (CML_List.rev cml_x32v12)
 in (let val cml_x32v14 = (CML_String.concat cml_x32v13)
 in (SOME cml_x32v14) end) end) end) end) end)
 else (let val cml_x32v15 = ((cml_x61 k) 0)
 in (if cml_x32v15
 then (let val cml_x32v17 = (c :: chrs)
 in (let val cml_x32v18 = (compress cml_x32v17)
 in (let val cml_x32v19 = (cml_x32v18 :: strs)
 in (let val cml_x32v16 = []
 in ((((b_inputLine_aux is) 500) cml_x32v16) cml_x32v19) end) end) end) end)
 else (let val cml_x32v21 = (c :: chrs)
 in (let val cml_x32v20 = ((cml_x45 k) 1)
 in ((((b_inputLine_aux is) cml_x32v20) cml_x32v21) strs) end) end)) end)) end)) end))));

val some_compress = (fn v3 => (fn v4 => (fn v2 => (fn v1 => (if v4
 then (NONE)
 else (SOME (CML_List.rev (if (CML_List.null v2)
 then v1
 else ((v3 (compress v2)) :: v1)))))))));

fun b_inputLineTokens_aux is = (fn f => (fn g => (fn is_emp => (fn chrs => (fn acc => (let val cml_x32v0 = (b_input1 is)
 in (case cml_x32v0 of
   (NONE) => ((((some_compress g) is_emp) chrs) acc)
 | (SOME c) => (let val cml_x32v1 = ((cml_x61 c) #"\n")
 in (if cml_x32v1
 then (let val cml_x32v2 = (false)
 in ((((some_compress g) cml_x32v2) chrs) acc) end)
 else (let val cml_x32v3 = (f c)
 in (if cml_x32v3
 then (let val cml_x32v4 = (CML_List.null chrs)
 in (if cml_x32v4
 then (let val cml_x32v6 = []
 in (let val cml_x32v5 = (false)
 in ((((((b_inputLineTokens_aux is) f) g) cml_x32v5) cml_x32v6) acc) end) end)
 else (let val cml_x32v9 = (compress chrs)
 in (let val cml_x32v10 = (g cml_x32v9)
 in (let val cml_x32v11 = (cml_x32v10 :: acc)
 in (let val cml_x32v8 = []
 in (let val cml_x32v7 = (false)
 in ((((((b_inputLineTokens_aux is) f) g) cml_x32v7) cml_x32v8) cml_x32v11) end) end) end) end) end)) end)
 else (let val cml_x32v13 = (c :: chrs)
 in (let val cml_x32v12 = (false)
 in ((((((b_inputLineTokens_aux is) f) g) cml_x32v12) cml_x32v13) acc) end) end)) end)) end)) end))))));

in
fun b_inputUntil is = (fn chr => (let val cml_x32v0 = ((b_inputUntil_aux is) chr)
 in (CML_String.implode cml_x32v0) end));

fun b_inputLine is = (let val cml_x32v1 = []
 in (let val cml_x32v0 = []
 in ((((b_inputLine_aux is) 500) cml_x32v0) cml_x32v1) end) end);

fun b_inputLineTokens is = (fn f => (fn g => (let val cml_x32v2 = []
 in (let val cml_x32v1 = []
 in (let val cml_x32v0 = (true)
 in ((((((b_inputLineTokens_aux is) f) g) cml_x32v0) cml_x32v1) cml_x32v2) end) end) end)));

local
fun b_inputLines_aux is = (fn acc => (let val cml_x32v0 = (b_inputLine is)
 in (case cml_x32v0 of
   (NONE) => (CML_List.rev acc)
 | (SOME l) => (let val cml_x32v1 = (l :: acc)
 in ((b_inputLines_aux is) cml_x32v1) end)) end));

fun b_inputAllTokens_aux is = (fn f => (fn g => (fn acc => (let val cml_x32v0 = (((b_inputLineTokens is) f) g)
 in (case cml_x32v0 of
   (NONE) => (CML_List.rev acc)
 | (SOME l) => (let val cml_x32v1 = (l :: acc)
 in ((((b_inputAllTokens_aux is) f) g) cml_x32v1) end)) end))));

fun b_consume_rest is = (let val cml_x32v0 = (b_input1 is)
 in (case cml_x32v0 of
   (NONE) => ()
 | (SOME c) => (b_consume_rest is)) end);

fun b_open_option stdin_or_fname = (case stdin_or_fname of
   (NONE) => (let val cml_x32v0 = ()
 in (let val is = (b_openStdIn cml_x32v0)
 in (let val cml_x32v1 = (fn cml_ => (case cml_ of
   () => (b_consume_rest is)))
 in (let val cml_x32v2 = (is, cml_x32v1)
 in (SOME cml_x32v2) end) end) end) end)
 | (SOME fname) => ((let val is = (b_openIn fname)
 in (let val cml_x32v3 = (fn cml_ => (case cml_ of
   () => (b_closeIn is)))
 in (let val cml_x32v4 = (is, cml_x32v3)
 in (SOME cml_x32v4) end) end) end)
 handle (BadFileName) => (NONE)));

fun fold_chars_loop f = (fn is => (fn y => (let val cml_x32v0 = (b_input1 is)
 in (case cml_x32v0 of
   (NONE) => y
 | (SOME c) => (let val cml_x32v1 = ((f c) y)
 in (((fold_chars_loop f) is) cml_x32v1) end)) end)));

fun fold_lines_loop f = (fn is => (fn y => (let val cml_x32v0 = (b_inputLine is)
 in (case cml_x32v0 of
   (NONE) => y
 | (SOME c) => (let val cml_x32v1 = ((f c) y)
 in (((fold_lines_loop f) is) cml_x32v1) end)) end)));

fun fold_tokens_loop g = (fn h => (fn f => (fn is => (fn y => (let val cml_x32v0 = (((b_inputLineTokens is) g) h)
 in (case cml_x32v0 of
   (NONE) => y
 | (SOME c) => (let val cml_x32v1 = ((f c) y)
 in (((((fold_tokens_loop g) h) f) is) cml_x32v1) end)) end)))));

in
fun b_inputLines is = (let val cml_x32v0 = []
 in ((b_inputLines_aux is) cml_x32v0) end);

fun b_inputLinesFrom fname = ((let val is = (b_openIn fname)
 in (let val lines = (b_inputLines is)
 in (let val _ = (b_closeIn is)
 in (SOME lines) end) end) end)
 handle (BadFileName) => (NONE));

fun b_inputLinesStdIn cml_ = (case cml_ of
   () => (let val cml_x32v0 = ()
 in (let val is = (b_openStdIn cml_x32v0)
 in (b_inputLines is) end) end));

fun b_inputAllTokens is = (fn f => (fn g => (let val cml_x32v0 = []
 in ((((b_inputAllTokens_aux is) f) g) cml_x32v0) end)));

fun b_inputAllTokensFrom fname = (fn f => (fn g => ((let val is = (b_openIn fname)
 in (let val lines = (((b_inputAllTokens is) f) g)
 in (let val _ = (b_closeIn is)
 in (SOME lines) end) end) end)
 handle (BadFileName) => (NONE))));

fun b_inputAllTokensStdIn f = (fn g => (let val cml_x32v0 = ()
 in (let val is = (b_openStdIn cml_x32v0)
 in (let val lines = (((b_inputAllTokens is) f) g)
 in (SOME lines) end) end) end));

fun foldChars f = (fn x => (fn stdin_or_fname => (let val cml_x32v0 = (b_open_option stdin_or_fname)
 in (case cml_x32v0 of
   (NONE) => (NONE)
 | (SOME (is, close)) => ((let val res = (((fold_chars_loop f) is) x)
 in (let val cml_x32v1 = ()
 in (let val _ = (close cml_x32v1)
 in (SOME res) end) end) end)
 handle e => (let val cml_x32v2 = ()
 in (let val _ = (close cml_x32v2)
 in (raise e) end) end))) end)));

fun foldLines f = (fn x => (fn stdin_or_fname => (let val cml_x32v0 = (b_open_option stdin_or_fname)
 in (case cml_x32v0 of
   (NONE) => (NONE)
 | (SOME (is, close)) => ((let val res = (((fold_lines_loop f) is) x)
 in (let val cml_x32v1 = ()
 in (let val _ = (close cml_x32v1)
 in (SOME res) end) end) end)
 handle e => (let val cml_x32v2 = ()
 in (let val _ = (close cml_x32v2)
 in (raise e) end) end))) end)));

fun foldTokens g = (fn h => (fn f => (fn x => (fn stdin_or_fname => (let val cml_x32v0 = (b_open_option stdin_or_fname)
 in (case cml_x32v0 of
   (NONE) => (NONE)
 | (SOME (is, close)) => ((let val res = (((((fold_tokens_loop g) h) f) is) x)
 in (let val cml_x32v1 = ()
 in (let val _ = (close cml_x32v1)
 in (SOME res) end) end) end)
 handle e => (let val cml_x32v2 = ()
 in (let val _ = (close cml_x32v2)
 in (raise e) end) end))) end)))));

end;

end;

end;

end;

end;

end;

end;

end;

end;

end;

end;

val cml_print = CML_TextIO.cml_print;

datatype source_values_v = Num of int | Pair of source_values_v * source_values_v;

fun list v3 = (case v3 of
   [] => (Num 0)
 | (v2 :: v1) => (Pair (v2, (list v1))));

datatype pure_config_lit = Msg of (char) list * (char) list | Loc of int | Str_1 of (char) list | Int of int;

datatype pure_config_atom_op = Message of (char) list | Strgeq | Strgt | Strleq | Strlt | Streq | Substring | Implode | Concat | Elem | Len | Geq | Gt | Leq | Lt | Eq | Mod | Div_1 | Mul | Sub | Add | Lit of pure_config_lit;

fun flat v3 = (case v3 of
   [] => []
 | (v2 :: v1) => (v2 @ (flat v1)));

fun foldl_1 v4 = (fn v3 => (fn v5 => (case v5 of
   [] => v3
 | (v2 :: v1) => (((foldl_1 v4) ((v4 v3) v2)) v1))));

fun foldr_1 v4 = (fn v3 => (fn v5 => (case v5 of
   [] => v3
 | (v2 :: v1) => ((v4 v2) (((foldr_1 v4) v3) v1)))));

datatype state_cexp_csop = Ffi of string | Unsafeupdate | Update_2 | Unsafesub | Sub_1 | Length_2 | Ref | Alloc_2 | Atomop_3 of pure_config_atom_op | Cons_3 of string | Appop;

datatype state_cexp_cexp = Handleapp of state_cexp_cexp * state_cexp_cexp | Handle_2 of state_cexp_cexp * string * state_cexp_cexp | Raise_2 of state_cexp_cexp | Case_3 of string * ((string * ((string) list * state_cexp_cexp))) list * ((((string * int)) list * state_cexp_cexp)) option | If_1 of state_cexp_cexp * state_cexp_cexp * state_cexp_cexp | Let_3 of (string) option * state_cexp_cexp * state_cexp_cexp | Letrec_3 of ((string * (string * state_cexp_cexp))) list * state_cexp_cexp | Lam_3 of (string) option * state_cexp_cexp | App_3 of state_cexp_csop * (state_cexp_cexp) list | Var_3 of string;

val bool = (fn v1 => (if v1
 then (App_3 ((Cons_3 "True"), []))
 else (App_3 ((Cons_3 "False"), []))));

datatype location_locn = Posn of int * int | Eofpt | Unknownpt;

datatype location_locs = Locs of location_locn * location_locn;

val unknown_loc = (Locs ((Unknownpt), (Unknownpt)));

fun oel v3 = (fn v4 => (case v4 of
   [] => (NONE)
 | (v2 :: v1) => (if (v3 = 0)
 then (SOME v2)
 else ((oel (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v1))));

fun l2n v3 = (fn v4 => (case v4 of
   [] => 0
 | (v2 :: v1) => ((v2 mod v3) + (v3 * ((l2n v3) v1)))));

val s2n = (fn v1 => (fn v2 => (fn v3 => ((l2n v1) ((CML_List.map v2) (CML_List.rev v3))))));

val ishexdigit = (fn v1 => (((48 <= (Char.ord v1)) andalso ((Char.ord v1) <= 57)) orelse (((97 <= (Char.ord v1)) andalso ((Char.ord v1) <= 102)) orelse ((65 <= (Char.ord v1)) andalso ((Char.ord v1) <= 70)))));

val unhex = (fn v => (if (v = #"0")
 then 0
 else (if (v = #"1")
 then 1
 else (if (v = #"2")
 then 2
 else (if (v = #"3")
 then 3
 else (if (v = #"4")
 then 4
 else (if (v = #"5")
 then 5
 else (if (v = #"6")
 then 6
 else (if (v = #"7")
 then 7
 else (if (v = #"8")
 then 8
 else (if (v = #"9")
 then 9
 else (if (v = #"a")
 then 10
 else (if (v = #"b")
 then 11
 else (if (v = #"c")
 then 12
 else (if (v = #"d")
 then 13
 else (if (v = #"e")
 then 14
 else (if (v = #"f")
 then 15
 else (if (v = #"A")
 then 10
 else (if (v = #"B")
 then 11
 else (if (v = #"C")
 then 12
 else (if (v = #"D")
 then 13
 else (if (v = #"E")
 then 14
 else (if (v = #"F")
 then 15
 else (raise (Bind)))))))))))))))))))))))));

val unhex_alt = (fn v1 => (if (ishexdigit v1)
 then (unhex v1)
 else 0));

val num_from_dec_string_alt = (fn v1 => (((s2n 10) unhex_alt) v1));

val num_from_hex_string_alt = (fn v1 => (((s2n 16) unhex_alt) v1));

datatype pure_lexer_impl_symbol = Errors | Others of (char) list | Ffis of (char) list | Longs of (char) list | Words of int | Numbers of int | Chars of char | Strings of (char) list;

val next_line = (fn v3 => (case v3 of
   (Unknownpt) => (Unknownpt)
 | (Eofpt) => (Eofpt)
 | (Posn (v2, v1)) => (Posn ((v2 + 1), 1))));

val next_loc = (fn v3 => (fn v4 => (case v4 of
   (Unknownpt) => (Unknownpt)
 | (Eofpt) => (Eofpt)
 | (Posn (v2, v1)) => (Posn (v2, (v1 + v3))))));

fun read_string v5 = (fn v4 => (fn v3 => (if (v5 = [])
 then ((Errors), (v3, []))
 else (if ((CML_List.hd v5) = #"\"")
 then ((Strings v4), (v3, (CML_List.tl v5)))
 else (if ((CML_List.hd v5) = #"\n")
 then ((Errors), ((next_line v3), (CML_List.tl v5)))
 else (if (((CML_List.hd v5) = #"\\") = (0 < 0))
 then (((read_string (CML_List.tl v5)) (v4 @ ((CML_List.hd v5) :: []))) ((next_loc 1) v3))
 else (case (CML_List.tl v5) of
   [] => ((Errors), (v3, (CML_List.tl v5)))
 | (v2 :: v1) => (if (v2 = #"\\")
 then (((read_string v1) (v4 @ (#"\\" :: []))) ((next_loc 2) v3))
 else (if (v2 = #"\"")
 then (((read_string v1) (v4 @ (#"\"" :: []))) ((next_loc 2) v3))
 else (if (v2 = #"n")
 then (((read_string v1) (v4 @ (#"\n" :: []))) ((next_loc 2) v3))
 else (if (v2 = #"t")
 then (((read_string v1) (v4 @ (#"\t" :: []))) ((next_loc 2) v3))
 else ((Errors), (v3, (CML_List.tl v5))))))))))))));

fun el v2 = (fn v1 => (if (v2 = 0)
 then (CML_List.hd v1)
 else ((el (let val k = (v2 - 1)
 in (if (k < 0)
 then 0
 else k) end)) (CML_List.tl v1))));

val isdigit = (fn v1 => ((48 <= (Char.ord v1)) andalso ((Char.ord v1) <= 57)));

fun implode_1 v3 = (case v3 of
   [] => []
 | (v2 :: v1) => (v2 :: (implode_1 v1)));

fun read_while v3 = (fn v4 => (fn v5 => (case v4 of
   [] => ((implode_1 (CML_List.rev v5)), [])
 | (v2 :: v1) => (if (v3 v2)
 then (((read_while v3) v1) (v2 :: v5))
 else ((implode_1 (CML_List.rev v5)), (v2 :: v1))))));

val islower = (fn v1 => ((97 <= (Char.ord v1)) andalso ((Char.ord v1) <= 122)));

val isupper = (fn v1 => ((65 <= (Char.ord v1)) andalso ((Char.ord v1) <= 90)));

val isalpha = (fn v1 => ((islower v1) orelse (isupper v1)));

val isalphanum = (fn v1 => ((isalpha v1) orelse (isdigit v1)));

val isalphanumprime = (fn v1 => ((isalphanum v1) orelse ((v1 = #"'") orelse (v1 = #"_"))));

val mkchars = (fn v8 => (case v8 of
   (Strings v1) => (if ((CML_List.length v1) = 1)
 then (Chars (CML_List.hd v1))
 else (Errors))
 | (Chars v2) => (Errors)
 | (Numbers v3) => (Errors)
 | (Words v4) => (Errors)
 | (Longs v5) => (Errors)
 | (Ffis v6) => (Errors)
 | (Others v7) => (Errors)
 | (Errors) => (Errors)));

fun read_fficall v4 = (fn v3 => (fn v5 => (case v4 of
   [] => ((Errors), (v5, []))
 | (v2 :: v1) => (if (v2 = #")")
 then ((Ffis (CML_List.rev v3)), (((next_loc 2) v5), v1))
 else (if (v2 = #"\n")
 then ((Errors), (v5, v1))
 else (if (CML_Char.isSpace v2)
 then (((read_fficall v1) v3) ((next_loc 1) v5))
 else (((read_fficall v1) (v2 :: v3)) ((next_loc 1) v5))))))));

fun skip_nested_comment v5 = (fn v6 => (fn v7 => (case v5 of
   [] => (NONE)
 | (v4 :: v3) => (case v3 of
   [] => (NONE)
 | (v2 :: v1) => (if ((v4 :: (v2 :: [])) = (#"{" :: (#"-" :: [])))
 then (((skip_nested_comment v1) (v6 + 1)) ((next_loc 2) v7))
 else (if ((v4 :: (v2 :: [])) = (#"-" :: (#"}" :: [])))
 then (if (v6 = 0)
 then (SOME (v1, ((next_loc 2) v7)))
 else (((skip_nested_comment v1) (let val k = (v6 - 1)
 in (if (k < 0)
 then 0
 else k) end)) ((next_loc 2) v7)))
 else (if ((Char.ord v4) = 10)
 then (((skip_nested_comment (v2 :: v1)) v6) (next_line v7))
 else (((skip_nested_comment (v2 :: v1)) v6) ((next_loc 1) v7)))))))));

val isprint = (fn v1 => ((32 <= (Char.ord v1)) andalso ((Char.ord v1) < 127)));

val isgraph = (fn v1 => ((isprint v1) andalso ((CML_Char.isSpace v1) = (0 < 0))));

val ispunct = (fn v1 => ((isgraph v1) andalso ((isalphanum v1) = (0 < 0))));

fun skip_eol_comment v3 = (fn v4 => (case v3 of
   [] => (SOME ([], v4))
 | (v2 :: v1) => (if (v2 = #"\n")
 then (SOME (v1, (next_line v4)))
 else ((skip_eol_comment v1) ((next_loc 1) v4)))));

val is_single_char_symbol = (fn v1 => ((CML_List.member v1) (#"(" :: (#")" :: (#"[" :: (#"]" :: (#"{" :: (#"}" :: (#"," :: (#";" :: []))))))))));

val issymbol = (fn v1 => ((CML_List.member v1) (#"`" :: (#"!" :: (#"%" :: (#"&" :: (#"$" :: (#"#" :: (#"+" :: (#"-" :: (#"/" :: (#":" :: (#"<" :: (#"=" :: (#">" :: (#"?" :: (#"@" :: (#"\\" :: (#"~" :: (#"^" :: (#"|" :: (#"*" :: []))))))))))))))))))))));

fun next_sym_alt v58 = (fn v59 => (case v58 of
   [] => (NONE)
 | (v57 :: v56) => (if (v57 = #"\n")
 then ((next_sym_alt v56) (next_line v59))
 else (if (CML_Char.isSpace v57)
 then ((next_sym_alt v56) ((next_loc 1) v59))
 else (if (isdigit v57)
 then (if (if (v56 = [])
 then (0 < 0)
 else ((v57 = #"0") andalso ((CML_List.hd v56) = #"w")))
 then (if ((CML_List.tl v56) = [])
 then (SOME ((Errors), ((Locs (v59, v59)), [])))
 else (if (isdigit (CML_List.hd (CML_List.tl v56)))
 then (let val v3 = (((read_while isdigit) (CML_List.tl v56)) [])
 in (case v3 of
   (v2, v1) => (SOME ((Words (num_from_dec_string_alt v2)), ((Locs (v59, ((next_loc ((CML_List.length v2) + 1)) v59))), v1)))) end)
 else (if ((CML_List.hd (CML_List.tl v56)) = #"x")
 then (let val v6 = (((read_while ishexdigit) (CML_List.tl (CML_List.tl v56))) [])
 in (case v6 of
   (v5, v4) => (SOME ((Words (num_from_hex_string_alt v5)), ((Locs (v59, ((next_loc ((CML_List.length v5) + 2)) v59))), v4)))) end)
 else (SOME ((Errors), ((Locs (v59, v59)), (CML_List.tl v56)))))))
 else (if (if (v56 = [])
 then (0 < 0)
 else ((v57 = #"0") andalso ((CML_List.hd v56) = #"x")))
 then (let val v9 = (((read_while ishexdigit) (CML_List.tl v56)) [])
 in (case v9 of
   (v8, v7) => (SOME ((Numbers (num_from_hex_string_alt v8)), ((Locs (v59, ((next_loc (CML_List.length v8)) v59))), v7)))) end)
 else (let val v12 = (((read_while isdigit) v56) [])
 in (case v12 of
   (v11, v10) => (SOME ((Numbers (num_from_dec_string_alt (v57 :: v11))), ((Locs (v59, ((next_loc (CML_List.length v11)) v59))), v10)))) end)))
 else (if ((v57 = #"~") andalso (if (v56 = [])
 then (0 < 0)
 else (isdigit (CML_List.hd v56))))
 then (let val v15 = (((read_while isdigit) v56) [])
 in (case v15 of
   (v14, v13) => (SOME ((Numbers (0 - (num_from_dec_string_alt v14))), ((Locs (v59, ((next_loc (CML_List.length v14)) v59))), v13)))) end)
 else (if (v57 = #"'")
 then (let val v18 = (((read_while isalphanumprime) v56) (v57 :: []))
 in (case v18 of
   (v17, v16) => (SOME ((Others v17), ((Locs (v59, ((next_loc (let val k = ((CML_List.length v17) - 1)
 in (if (k < 0)
 then 0
 else k) end)) v59))), v16)))) end)
 else (if (v57 = #"\"")
 then (let val v23 = (((read_string v56) []) ((next_loc 1) v59))
 in (case v23 of
   (v22, v21) => (case v21 of
   (v20, v19) => (SOME (v22, ((Locs (v59, v20)), v19))))) end)
 else (if (v57 = #"`")
 then (SOME ((Others (#"`" :: [])), ((Locs (v59, v59)), v56)))
 else (if ((CML_List.isPrefix (#"#" :: (#"\"" :: []))) (v57 :: v56))
 then (let val v28 = (((read_string (CML_List.tl v56)) []) ((next_loc 2) v59))
 in (case v28 of
   (v27, v26) => (case v26 of
   (v25, v24) => (SOME ((mkchars v27), ((Locs (v59, v25)), v24))))) end)
 else (if ((CML_List.isPrefix (#"#" :: (#"(" :: []))) (v57 :: v56))
 then (let val v33 = (((read_fficall (CML_List.tl v56)) []) ((next_loc 2) v59))
 in (case v33 of
   (v32, v31) => (case v31 of
   (v30, v29) => (SOME (v32, ((Locs (v59, v30)), v29))))) end)
 else (if ((CML_List.isPrefix (#"{" :: (#"-" :: []))) (v57 :: v56))
 then (case (((skip_nested_comment (CML_List.tl v56)) 0) ((next_loc 2) v59)) of
   (NONE) => (SOME ((Errors), ((Locs (v59, ((next_loc 2) v59))), [])))
 | (SOME v36) => (case v36 of
   (v35, v34) => ((next_sym_alt v35) v34)))
 else (if (((CML_List.isPrefix (#"-" :: (#"-" :: []))) (v57 :: v56)) andalso (if (2 <= (CML_List.length v56))
 then ((ispunct ((el 1) v56)) = (0 < 0))
 else (0 <= 0)))
 then (case ((skip_eol_comment (CML_List.tl v56)) ((next_loc 2) v59)) of
   (NONE) => (SOME ((Errors), ((Locs (v59, ((next_loc 2) v59))), [])))
 | (SOME v39) => (case v39 of
   (v38, v37) => ((next_sym_alt v38) v37)))
 else (if (is_single_char_symbol v57)
 then (SOME ((Others (v57 :: [])), ((Locs (v59, v59)), v56)))
 else (if (issymbol v57)
 then (let val v42 = (((read_while issymbol) v56) (v57 :: []))
 in (case v42 of
   (v41, v40) => (SOME ((Others v41), ((Locs (v59, ((next_loc (let val k = ((CML_List.length v41) - 1)
 in (if (k < 0)
 then 0
 else k) end)) v59))), v40)))) end)
 else (if (isalpha v57)
 then (let val v55 = (((read_while isalphanumprime) v56) (v57 :: []))
 in (case v55 of
   (v54, v53) => (case v53 of
   [] => (SOME ((Others v54), ((Locs (v59, ((next_loc (let val k = ((CML_List.length v54) - 1)
 in (if (k < 0)
 then 0
 else k) end)) v59))), v53)))
 | (v52 :: v51) => (if (v52 = #".")
 then (case v51 of
   [] => (SOME ((Errors), ((Locs (v59, ((next_loc (CML_List.length v54)) v59))), [])))
 | (v50 :: v49) => (if (isalpha v50)
 then (let val v45 = (((read_while isalphanumprime) v49) (v50 :: []))
 in (case v45 of
   (v44, v43) => (SOME ((Longs ((v54 @ (#"." :: [])) @ v44)), ((Locs (v59, ((next_loc ((CML_List.length v54) + (CML_List.length v44))) v59))), v43)))) end)
 else (if (issymbol v50)
 then (let val v48 = (((read_while issymbol) v49) (v50 :: []))
 in (case v48 of
   (v47, v46) => (SOME ((Longs ((v54 @ (#"." :: [])) @ v47)), ((Locs (v59, ((next_loc ((CML_List.length v54) + (CML_List.length v47))) v59))), v46)))) end)
 else (SOME ((Errors), ((Locs (v59, ((next_loc (CML_List.length v54)) v59))), v49))))))
 else (SOME ((Others v54), ((Locs (v59, ((next_loc (let val k = ((CML_List.length v54) - 1)
 in (if (k < 0)
 then 0
 else k) end)) v59))), v53)))))) end)
 else (if (v57 = #"_")
 then (SOME ((Others (#"_" :: [])), ((Locs (v59, v59)), v56)))
 else (SOME ((Errors), ((Locs (v59, v59)), v56))))))))))))))))))));

datatype tokens_token = Replidt of (char) list | Ffit of (char) list | Longidt of (char) list * (char) list | Symbolt of (char) list | Alphat of (char) list | Tyvart of (char) list | Chart of char | Stringt of (char) list | Realt of (char) list | Wordt of int | Hexintt of (char) list | Intt of int | Withtypet | Witht | Whilet | Wheret | Valt | Typet | Thent | Structuret | Structt | Signaturet | Sigt | Sharingt | Rect | Raiset | Orelset | Opent | Opt_1 | Oft | Localt | Lett | Includet | Int_1 | Ift | Handlet | Funt | Fnt | Exceptiont | Eqtypet | Endt | Elset | Datatypet | Caset | Ast | Andalsot | Andt | Rbracet | Bart | Lbracet | Underbart | Rbrackt | Lbrackt | Darrowt | Equalst | Semicolont | Sealt | Colont | Dotst | Arrowt | Commat | Start | Rpart | Lpart | Hasht | Lexerrort | Newlinet | Whitespacet of int;

fun splitp v3 = (fn v4 => (case v4 of
   [] => ([], [])
 | (v2 :: v1) => (if (v3 v2)
 then ([], (v2 :: v1))
 else ((v2 :: (fst ((splitp v3) v1))), (snd ((splitp v3) v1))))));

val processident = (fn v3 => (case v3 of
   [] => (Lexerrort)
 | (v2 :: v1) => (if (isalpha v2)
 then (Alphat (v2 :: v1))
 else (Symbolt (v2 :: v1)))));

val get_token = (fn v1 => (if (v1 = (#"(" :: []))
 then (Lpart)
 else (if (v1 = (#")" :: []))
 then (Rpart)
 else (if (v1 = (#"," :: []))
 then (Commat)
 else (if (v1 = (#";" :: []))
 then (Semicolont)
 else (if (v1 = (#"=" :: []))
 then (Equalst)
 else (if (v1 = (#"[" :: []))
 then (Lbrackt)
 else (if (v1 = (#"]" :: []))
 then (Rbrackt)
 else (if (v1 = (#"{" :: []))
 then (Lbracet)
 else (if (v1 = (#"}" :: []))
 then (Rbracet)
 else (if (v1 = (#"|" :: []))
 then (Bart)
 else (if (v1 = (#"_" :: []))
 then (Underbart)
 else (if (v1 = (#"c" :: (#"a" :: (#"s" :: (#"e" :: [])))))
 then (Caset)
 else (if (v1 = (#"e" :: (#"l" :: (#"s" :: (#"e" :: [])))))
 then (Elset)
 else (if (v1 = (#"e" :: (#"x" :: (#"c" :: (#"e" :: (#"p" :: (#"t" :: (#"i" :: (#"o" :: (#"n" :: []))))))))))
 then (Exceptiont)
 else (if (v1 = (#"i" :: (#"f" :: [])))
 then (Ift)
 else (if (v1 = (#"i" :: (#"n" :: [])))
 then (Int_1)
 else (if (v1 = (#"i" :: (#"n" :: (#"c" :: (#"l" :: (#"u" :: (#"d" :: (#"e" :: []))))))))
 then (Includet)
 else (if (v1 = (#"l" :: (#"e" :: (#"t" :: []))))
 then (Lett)
 else (if (v1 = (#"o" :: (#"f" :: [])))
 then (Oft)
 else (if (v1 = (#"t" :: (#"h" :: (#"e" :: (#"n" :: [])))))
 then (Thent)
 else (if (v1 = (#"t" :: (#"y" :: (#"p" :: (#"e" :: [])))))
 then (Typet)
 else (if (v1 = (#"w" :: (#"h" :: (#"e" :: (#"r" :: (#"e" :: []))))))
 then (Wheret)
 else (processident v1))))))))))))))))))))))));

val token_of_sym = (fn v14 => (case v14 of
   (Strings v1) => (Stringt v1)
 | (Chars v2) => (Chart v2)
 | (Numbers v3) => (Intt v3)
 | (Words v4) => (Wordt v4)
 | (Longs v11) => (let val v9 = ((splitp (fn v10 => (v10 = #"."))) v11)
 in (case v9 of
   (v8, v7) => (Longidt (v8, (case v7 of
   [] => []
 | (v6 :: v5) => v5)))) end)
 | (Ffis v12) => (Ffit v12)
 | (Others v13) => (get_token v13)
 | (Errors) => (Lexerrort)));

val next_token = (fn v6 => (fn v7 => (case ((next_sym_alt v6) v7) of
   (NONE) => (NONE)
 | (SOME v5) => (case v5 of
   (v4, v3) => (case v3 of
   (v2, v1) => (SOME ((token_of_sym v4), (v2, v1))))))));

fun lexer_fun_aux v8 = (fn v9 => (case ((next_token v8) v9) of
   (NONE) => []
 | (SOME v7) => (case v7 of
   (v6, v5) => (case v5 of
   (v4, v3) => (case v4 of
   (Locs (v2, v1)) => ((v6, (Locs (v2, v1))) :: ((lexer_fun_aux v3) ((next_loc 1) v1))))))));

val lexer_fun = (fn v1 => ((lexer_fun_aux v1) (Posn (1, 1))));

datatype pureAST_litAST = Litstring of (char) list | Litint of int;

datatype pureAST_patAST = Patuscore | Patlit of pureAST_litAST | Pattup of (pureAST_patAST) list | Patapp of (char) list * (pureAST_patAST) list | Patvar of (char) list;

datatype pureAST_tyAST = Tytup of (pureAST_tyAST) list | Tyvar of (char) list | Tyop of (char) list * (pureAST_tyAST) list;

datatype pureAST_expAST = Expcase of pureAST_expAST * ((pureAST_patAST * pureAST_expAST)) list | Expdo of (pureAST_expdostmtAST) list * pureAST_expAST | Explet of (pureAST_expdecAST) list * pureAST_expAST | Explit of pureAST_litAST | Expif of pureAST_expAST * pureAST_expAST * pureAST_expAST | Expabs of pureAST_patAST * pureAST_expAST | Expapp of pureAST_expAST * pureAST_expAST | Exptup of (pureAST_expAST) list | Expop of pure_config_atom_op * (pureAST_expAST) list | Expcon of (char) list * (pureAST_expAST) list | Expvar of (char) list
and pureAST_expdecAST = Expdecfunbind of (char) list * (pureAST_patAST) list * pureAST_expAST | Expdecpatbind of pureAST_patAST * pureAST_expAST | Expdectysig of (char) list * pureAST_tyAST
and pureAST_expdostmtAST = Expdostmtlet of (pureAST_expdecAST) list | Expdostmtbind of pureAST_patAST * pureAST_expAST | Expdostmtexp of pureAST_expAST;

fun list_rel v7 = (fn v9 => (fn v8 => (case v9 of
   [] => (case v8 of
   [] => (0 <= 0)
 | (v2 :: v1) => (0 < 0))
 | (v6 :: v5) => (case v8 of
   [] => (0 < 0)
 | (v4 :: v3) => (((v7 v6) v4) andalso (((list_rel v7) v5) v3))))));

datatype ('a, 'b) grammar_symbol = Nt of ('b, int) sum | Tok of 'a;

datatype ('a, 'b, 'locs) grammar_parsetree = Nd of (('b, int) sum * 'locs) * (('a, 'b, 'locs) grammar_parsetree) list | Lf of (('a, 'b) grammar_symbol * 'locs);

datatype pureNT_ppegnt = Ndoblocklayout | Ndostmtseqeq | Ndostmtseq | Npatalts | Npatalt | Ndostmteq | Nblocklayout | Ndoblock | Ndostmt | Nvalbinding | Nfreeeqbind | Neqbind | Neqbindseq' | Neqbindseq | Nop | Nlit | Naexpeq | Naexp | Nfexp2 | Nfexpeq | Nfexp | Niexpeq | Niexp | Nlsafeexpeq | Nlsafeexp | Nexpeq | Nexp | Nfunrhs | Napat | Npat | Ntyapp | Ntycondecl | Nty | Ntybase | Ndecl | Ndecls;

val mktoklf = (fn v1 => ((Lf ((Tok (fst v1)), (snd v1))) :: []));

datatype ispeg_locrel = Lrok | Lrgt | Lrge | Lreq;

datatype ('a, 'b, 'c, 'e) ispeg_ispegsym = Error of 'e | Not of ('a, 'b, 'c, 'e) ispeg_ispegsym * 'c | Rpt of ('a, 'b, 'c, 'e) ispeg_ispegsym * (('c) list -> 'c) | Choice of ('a, 'b, 'c, 'e) ispeg_ispegsym * ('a, 'b, 'c, 'e) ispeg_ispegsym * (('c, 'c) sum -> 'c) | Seq_1 of ('a, 'b, 'c, 'e) ispeg_ispegsym * ('a, 'b, 'c, 'e) ispeg_ispegsym * ('c -> ('c -> 'c)) | Nt_1 of ('b, int) sum * ('c -> 'c) * ispeg_locrel | Tok_1 of ('a -> bool) * (('a * location_locs) -> 'c) * ispeg_locrel | Any of (('a * location_locs) -> 'c) | Empty of 'c;

datatype ('a, 'b, 'c, 'e) ispeg_ispeg = Recordtypeispeg of ('a, 'b, 'c, 'e) ispeg_ispegsym * 'e * 'e * 'e * 'e * 'e * ((('b, int) sum * ('a, 'b, 'c, 'e) ispeg_ispegsym)) list;

val recordtypeispegseldefanyeof = (fn v8 => (case v8 of
   (Recordtypeispeg (v7, v6, v5, v4, v3, v2, v1)) => v6));

val recordtypeispegseldeftokfalse = (fn v8 => (case v8 of
   (Recordtypeispeg (v7, v6, v5, v4, v3, v2, v1)) => v5));

val recordtypeispegseldeftokeof = (fn v8 => (case v8 of
   (Recordtypeispeg (v7, v6, v5, v4, v3, v2, v1)) => v4));

val recordtypeispegseldefnotfail = (fn v8 => (case v8 of
   (Recordtypeispeg (v7, v6, v5, v4, v3, v2, v1)) => v3));

val recordtypeispegseldefifail = (fn v8 => (case v8 of
   (Recordtypeispeg (v7, v6, v5, v4, v3, v2, v1)) => v2));

val recordtypeispegseldefrules = (fn v8 => (case v8 of
   (Recordtypeispeg (v7, v6, v5, v4, v3, v2, v1)) => v1));

val nt = (fn v3 => (fn v2 => (fn v1 => (Nt_1 ((Inl v3), v2, v1)))));

val fupdate_list = (fn v1 => ((foldl_1 CML_Alist.update) v1));

val pegf = (fn v4 => (fn v3 => (Seq_1 (v4, (Empty []), (fn v2 => (fn v1 => (v3 v2)))))));

val merge_locs = (fn v6 => (fn v5 => (case v6 of
   (Locs (v4, v3)) => (case v5 of
   (Locs (v2, v1)) => (Locs (v4, v1))))));

fun merge_list_locs v7 = (case v7 of
   [] => unknown_loc
 | (v6 :: v5) => (case v5 of
   [] => v6
 | (v4 :: v3) => (case v3 of
   [] => ((merge_locs v6) v4)
 | (v2 :: v1) => (merge_list_locs (v6 :: (v2 :: v1))))));

val ptree_loc = (fn v8 => (case v8 of
   (Lf v3) => (case v3 of
   (v2, v1) => v1)
 | (Nd (v7, v6)) => (case v7 of
   (v5, v4) => v4)));

val ptree_list_loc = (fn v1 => (merge_list_locs ((CML_List.map ptree_loc) v1)));

val mknt = (fn v1 => (fn v2 => ((Nd (((Inl v1), (ptree_list_loc v2)), v2)) :: [])));

val sumid = (fn v3 => (case v3 of
   (Inl v1) => v1
 | (Inr v2) => v2));

fun choicel v3 = (case v3 of
   [] => (Not ((Empty []), []))
 | (v2 :: v1) => (Choice (v2, (choicel v1), sumid)));

fun append_1 v3 = (fn v4 => (case v3 of
   [] => v4
 | (v2 :: v1) => (v2 :: ((append_1 v1) v4))));

val seql = (fn v4 => (fn v3 => ((pegf (((foldr_1 (fn v2 => (fn v1 => (Seq_1 (v2, v1, append_1))))) (Empty [])) v4)) v3)));

val option_bind = (fn v3 => (fn v2 => (case v3 of
   (NONE) => (NONE)
 | (SOME v1) => (v2 v1))));

val destalphat = (fn v15 => (case v15 of
   (Whitespacet v1) => (NONE)
 | (Newlinet) => (NONE)
 | (Lexerrort) => (NONE)
 | (Hasht) => (NONE)
 | (Lpart) => (NONE)
 | (Rpart) => (NONE)
 | (Start) => (NONE)
 | (Commat) => (NONE)
 | (Arrowt) => (NONE)
 | (Dotst) => (NONE)
 | (Colont) => (NONE)
 | (Sealt) => (NONE)
 | (Semicolont) => (NONE)
 | (Equalst) => (NONE)
 | (Darrowt) => (NONE)
 | (Lbrackt) => (NONE)
 | (Rbrackt) => (NONE)
 | (Underbart) => (NONE)
 | (Lbracet) => (NONE)
 | (Bart) => (NONE)
 | (Rbracet) => (NONE)
 | (Andt) => (NONE)
 | (Andalsot) => (NONE)
 | (Ast) => (NONE)
 | (Caset) => (NONE)
 | (Datatypet) => (NONE)
 | (Elset) => (NONE)
 | (Endt) => (NONE)
 | (Eqtypet) => (NONE)
 | (Exceptiont) => (NONE)
 | (Fnt) => (NONE)
 | (Funt) => (NONE)
 | (Handlet) => (NONE)
 | (Ift) => (NONE)
 | (Int_1) => (NONE)
 | (Includet) => (NONE)
 | (Lett) => (NONE)
 | (Localt) => (NONE)
 | (Oft) => (NONE)
 | (Opt_1) => (NONE)
 | (Opent) => (NONE)
 | (Orelset) => (NONE)
 | (Raiset) => (NONE)
 | (Rect) => (NONE)
 | (Sharingt) => (NONE)
 | (Sigt) => (NONE)
 | (Signaturet) => (NONE)
 | (Structt) => (NONE)
 | (Structuret) => (NONE)
 | (Thent) => (NONE)
 | (Typet) => (NONE)
 | (Valt) => (NONE)
 | (Wheret) => (NONE)
 | (Whilet) => (NONE)
 | (Witht) => (NONE)
 | (Withtypet) => (NONE)
 | (Intt v2) => (NONE)
 | (Hexintt v3) => (NONE)
 | (Wordt v4) => (NONE)
 | (Realt v5) => (NONE)
 | (Stringt v6) => (NONE)
 | (Chart v7) => (NONE)
 | (Tyvart v8) => (NONE)
 | (Alphat v9) => (SOME v9)
 | (Symbolt v10) => (NONE)
 | (Longidt (v12, v11)) => (NONE)
 | (Ffit v13) => (NONE)
 | (Replidt v14) => (NONE)));

val option_guard = (fn v1 => (if v1
 then (SOME ())
 else (NONE)));

val option_ignore_bind = (fn v1 => (fn v2 => ((option_bind v1) (const v2))));

val keywords = ((#"d" :: (#"a" :: (#"t" :: (#"a" :: [])))) :: ((#"w" :: (#"h" :: (#"e" :: (#"r" :: (#"e" :: []))))) :: ((#"l" :: (#"e" :: (#"t" :: []))) :: ((#"i" :: (#"n" :: [])) :: ((#"i" :: (#"f" :: [])) :: ((#"t" :: (#"h" :: (#"e" :: (#"n" :: [])))) :: ((#"e" :: (#"l" :: (#"s" :: (#"e" :: [])))) :: ((#"d" :: (#"o" :: [])) :: []))))))));

val ohd = (fn v3 => (case v3 of
   [] => (NONE)
 | (v2 :: v1) => (SOME v2)));

val lcname = (fn v2 => (((option_ignore_bind (option_guard (((CML_List.member v2) keywords) = (0 < 0)))) ((option_bind (ohd v2)) (fn v1 => (option_guard (islower v1))))) = (SOME ())));

val lcname_tok = (fn v2 => (((option_bind (destalphat v2)) (fn v1 => (option_guard (lcname v1)))) = (SOME ())));

val capname = (fn v2 => (((option_bind (ohd v2)) (fn v1 => (option_guard (isupper v1)))) = (SOME ())));

val capname_tok = (fn v2 => (((option_bind (destalphat v2)) (fn v1 => (option_guard (capname v1)))) = (SOME ())));

val sepby1 = (fn v1 => (fn v2 => ((seql (v1 :: ((Rpt (((seql (v2 :: (v1 :: []))) id), flat)) :: []))) id)));

val sepby = (fn v1 => (fn v2 => (choicel (((sepby1 v1) v2) :: ((Empty []) :: [])))));

val rpt1 = (fn v1 => ((seql (v1 :: ((Rpt (v1, flat)) :: []))) id));

val destsymbolt = (fn v15 => (case v15 of
   (Whitespacet v1) => (NONE)
 | (Newlinet) => (NONE)
 | (Lexerrort) => (NONE)
 | (Hasht) => (NONE)
 | (Lpart) => (NONE)
 | (Rpart) => (NONE)
 | (Start) => (NONE)
 | (Commat) => (NONE)
 | (Arrowt) => (NONE)
 | (Dotst) => (NONE)
 | (Colont) => (NONE)
 | (Sealt) => (NONE)
 | (Semicolont) => (NONE)
 | (Equalst) => (NONE)
 | (Darrowt) => (NONE)
 | (Lbrackt) => (NONE)
 | (Rbrackt) => (NONE)
 | (Underbart) => (NONE)
 | (Lbracet) => (NONE)
 | (Bart) => (NONE)
 | (Rbracet) => (NONE)
 | (Andt) => (NONE)
 | (Andalsot) => (NONE)
 | (Ast) => (NONE)
 | (Caset) => (NONE)
 | (Datatypet) => (NONE)
 | (Elset) => (NONE)
 | (Endt) => (NONE)
 | (Eqtypet) => (NONE)
 | (Exceptiont) => (NONE)
 | (Fnt) => (NONE)
 | (Funt) => (NONE)
 | (Handlet) => (NONE)
 | (Ift) => (NONE)
 | (Int_1) => (NONE)
 | (Includet) => (NONE)
 | (Lett) => (NONE)
 | (Localt) => (NONE)
 | (Oft) => (NONE)
 | (Opt_1) => (NONE)
 | (Opent) => (NONE)
 | (Orelset) => (NONE)
 | (Raiset) => (NONE)
 | (Rect) => (NONE)
 | (Sharingt) => (NONE)
 | (Sigt) => (NONE)
 | (Signaturet) => (NONE)
 | (Structt) => (NONE)
 | (Structuret) => (NONE)
 | (Thent) => (NONE)
 | (Typet) => (NONE)
 | (Valt) => (NONE)
 | (Wheret) => (NONE)
 | (Whilet) => (NONE)
 | (Witht) => (NONE)
 | (Withtypet) => (NONE)
 | (Intt v2) => (NONE)
 | (Hexintt v3) => (NONE)
 | (Wordt v4) => (NONE)
 | (Realt v5) => (NONE)
 | (Stringt v6) => (NONE)
 | (Chart v7) => (NONE)
 | (Tyvart v8) => (NONE)
 | (Alphat v9) => (NONE)
 | (Symbolt v10) => (SOME v10)
 | (Longidt (v12, v11)) => (NONE)
 | (Ffit v13) => (NONE)
 | (Replidt v14) => (NONE)));

val issymbolopt = (fn v2 => (((option_bind (destsymbolt v2)) (fn v1 => (option_guard (((v1 = (#"<" :: (#"-" :: []))) = (0 < 0)) andalso (((v1 = (#":" :: (#":" :: []))) = (0 < 0)) andalso (((v1 = (#"-" :: (#">" :: []))) = (0 < 0)) andalso ((v1 = (#"`" :: [])) = (0 < 0)))))))) = (SOME ())));

val isalphat = (fn v15 => (case v15 of
   (Whitespacet v1) => (0 < 0)
 | (Newlinet) => (0 < 0)
 | (Lexerrort) => (0 < 0)
 | (Hasht) => (0 < 0)
 | (Lpart) => (0 < 0)
 | (Rpart) => (0 < 0)
 | (Start) => (0 < 0)
 | (Commat) => (0 < 0)
 | (Arrowt) => (0 < 0)
 | (Dotst) => (0 < 0)
 | (Colont) => (0 < 0)
 | (Sealt) => (0 < 0)
 | (Semicolont) => (0 < 0)
 | (Equalst) => (0 < 0)
 | (Darrowt) => (0 < 0)
 | (Lbrackt) => (0 < 0)
 | (Rbrackt) => (0 < 0)
 | (Underbart) => (0 < 0)
 | (Lbracet) => (0 < 0)
 | (Bart) => (0 < 0)
 | (Rbracet) => (0 < 0)
 | (Andt) => (0 < 0)
 | (Andalsot) => (0 < 0)
 | (Ast) => (0 < 0)
 | (Caset) => (0 < 0)
 | (Datatypet) => (0 < 0)
 | (Elset) => (0 < 0)
 | (Endt) => (0 < 0)
 | (Eqtypet) => (0 < 0)
 | (Exceptiont) => (0 < 0)
 | (Fnt) => (0 < 0)
 | (Funt) => (0 < 0)
 | (Handlet) => (0 < 0)
 | (Ift) => (0 < 0)
 | (Int_1) => (0 < 0)
 | (Includet) => (0 < 0)
 | (Lett) => (0 < 0)
 | (Localt) => (0 < 0)
 | (Oft) => (0 < 0)
 | (Opt_1) => (0 < 0)
 | (Opent) => (0 < 0)
 | (Orelset) => (0 < 0)
 | (Raiset) => (0 < 0)
 | (Rect) => (0 < 0)
 | (Sharingt) => (0 < 0)
 | (Sigt) => (0 < 0)
 | (Signaturet) => (0 < 0)
 | (Structt) => (0 < 0)
 | (Structuret) => (0 < 0)
 | (Thent) => (0 < 0)
 | (Typet) => (0 < 0)
 | (Valt) => (0 < 0)
 | (Wheret) => (0 < 0)
 | (Whilet) => (0 < 0)
 | (Witht) => (0 < 0)
 | (Withtypet) => (0 < 0)
 | (Intt v2) => (0 < 0)
 | (Hexintt v3) => (0 < 0)
 | (Wordt v4) => (0 < 0)
 | (Realt v5) => (0 < 0)
 | (Stringt v6) => (0 < 0)
 | (Chart v7) => (0 < 0)
 | (Tyvart v8) => (0 < 0)
 | (Alphat v9) => (0 <= 0)
 | (Symbolt v10) => (0 < 0)
 | (Longidt (v12, v11)) => (0 < 0)
 | (Ffit v13) => (0 < 0)
 | (Replidt v14) => (0 < 0)));

fun drop_1 v3 = (fn v4 => (case v4 of
   [] => []
 | (v2 :: v1) => (if (v3 = 0)
 then (v2 :: v1)
 else ((drop_1 (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v1))));

fun odds v5 = (case v5 of
   [] => []
 | (v4 :: v3) => (case v3 of
   [] => (v4 :: [])
 | (v2 :: v1) => (v4 :: (odds v1))));

val destffit = (fn v15 => (case v15 of
   (Whitespacet v1) => (NONE)
 | (Newlinet) => (NONE)
 | (Lexerrort) => (NONE)
 | (Hasht) => (NONE)
 | (Lpart) => (NONE)
 | (Rpart) => (NONE)
 | (Start) => (NONE)
 | (Commat) => (NONE)
 | (Arrowt) => (NONE)
 | (Dotst) => (NONE)
 | (Colont) => (NONE)
 | (Sealt) => (NONE)
 | (Semicolont) => (NONE)
 | (Equalst) => (NONE)
 | (Darrowt) => (NONE)
 | (Lbrackt) => (NONE)
 | (Rbrackt) => (NONE)
 | (Underbart) => (NONE)
 | (Lbracet) => (NONE)
 | (Bart) => (NONE)
 | (Rbracet) => (NONE)
 | (Andt) => (NONE)
 | (Andalsot) => (NONE)
 | (Ast) => (NONE)
 | (Caset) => (NONE)
 | (Datatypet) => (NONE)
 | (Elset) => (NONE)
 | (Endt) => (NONE)
 | (Eqtypet) => (NONE)
 | (Exceptiont) => (NONE)
 | (Fnt) => (NONE)
 | (Funt) => (NONE)
 | (Handlet) => (NONE)
 | (Ift) => (NONE)
 | (Int_1) => (NONE)
 | (Includet) => (NONE)
 | (Lett) => (NONE)
 | (Localt) => (NONE)
 | (Oft) => (NONE)
 | (Opt_1) => (NONE)
 | (Opent) => (NONE)
 | (Orelset) => (NONE)
 | (Raiset) => (NONE)
 | (Rect) => (NONE)
 | (Sharingt) => (NONE)
 | (Sigt) => (NONE)
 | (Signaturet) => (NONE)
 | (Structt) => (NONE)
 | (Structuret) => (NONE)
 | (Thent) => (NONE)
 | (Typet) => (NONE)
 | (Valt) => (NONE)
 | (Wheret) => (NONE)
 | (Whilet) => (NONE)
 | (Witht) => (NONE)
 | (Withtypet) => (NONE)
 | (Intt v2) => (NONE)
 | (Hexintt v3) => (NONE)
 | (Wordt v4) => (NONE)
 | (Realt v5) => (NONE)
 | (Stringt v6) => (NONE)
 | (Chart v7) => (NONE)
 | (Tyvart v8) => (NONE)
 | (Alphat v9) => (NONE)
 | (Symbolt v10) => (NONE)
 | (Longidt (v12, v11)) => (NONE)
 | (Ffit v13) => (SOME v13)
 | (Replidt v14) => (NONE)));

val isint = (fn v15 => (case v15 of
   (Whitespacet v1) => (0 < 0)
 | (Newlinet) => (0 < 0)
 | (Lexerrort) => (0 < 0)
 | (Hasht) => (0 < 0)
 | (Lpart) => (0 < 0)
 | (Rpart) => (0 < 0)
 | (Start) => (0 < 0)
 | (Commat) => (0 < 0)
 | (Arrowt) => (0 < 0)
 | (Dotst) => (0 < 0)
 | (Colont) => (0 < 0)
 | (Sealt) => (0 < 0)
 | (Semicolont) => (0 < 0)
 | (Equalst) => (0 < 0)
 | (Darrowt) => (0 < 0)
 | (Lbrackt) => (0 < 0)
 | (Rbrackt) => (0 < 0)
 | (Underbart) => (0 < 0)
 | (Lbracet) => (0 < 0)
 | (Bart) => (0 < 0)
 | (Rbracet) => (0 < 0)
 | (Andt) => (0 < 0)
 | (Andalsot) => (0 < 0)
 | (Ast) => (0 < 0)
 | (Caset) => (0 < 0)
 | (Datatypet) => (0 < 0)
 | (Elset) => (0 < 0)
 | (Endt) => (0 < 0)
 | (Eqtypet) => (0 < 0)
 | (Exceptiont) => (0 < 0)
 | (Fnt) => (0 < 0)
 | (Funt) => (0 < 0)
 | (Handlet) => (0 < 0)
 | (Ift) => (0 < 0)
 | (Int_1) => (0 < 0)
 | (Includet) => (0 < 0)
 | (Lett) => (0 < 0)
 | (Localt) => (0 < 0)
 | (Oft) => (0 < 0)
 | (Opt_1) => (0 < 0)
 | (Opent) => (0 < 0)
 | (Orelset) => (0 < 0)
 | (Raiset) => (0 < 0)
 | (Rect) => (0 < 0)
 | (Sharingt) => (0 < 0)
 | (Sigt) => (0 < 0)
 | (Signaturet) => (0 < 0)
 | (Structt) => (0 < 0)
 | (Structuret) => (0 < 0)
 | (Thent) => (0 < 0)
 | (Typet) => (0 < 0)
 | (Valt) => (0 < 0)
 | (Wheret) => (0 < 0)
 | (Whilet) => (0 < 0)
 | (Witht) => (0 < 0)
 | (Withtypet) => (0 < 0)
 | (Intt v2) => (0 <= 0)
 | (Hexintt v3) => (0 < 0)
 | (Wordt v4) => (0 < 0)
 | (Realt v5) => (0 < 0)
 | (Stringt v6) => (0 < 0)
 | (Chart v7) => (0 < 0)
 | (Tyvart v8) => (0 < 0)
 | (Alphat v9) => (0 < 0)
 | (Symbolt v10) => (0 < 0)
 | (Longidt (v12, v11)) => (0 < 0)
 | (Ffit v13) => (0 < 0)
 | (Replidt v14) => (0 < 0)));

val isstring = (fn v15 => (case v15 of
   (Whitespacet v1) => (0 < 0)
 | (Newlinet) => (0 < 0)
 | (Lexerrort) => (0 < 0)
 | (Hasht) => (0 < 0)
 | (Lpart) => (0 < 0)
 | (Rpart) => (0 < 0)
 | (Start) => (0 < 0)
 | (Commat) => (0 < 0)
 | (Arrowt) => (0 < 0)
 | (Dotst) => (0 < 0)
 | (Colont) => (0 < 0)
 | (Sealt) => (0 < 0)
 | (Semicolont) => (0 < 0)
 | (Equalst) => (0 < 0)
 | (Darrowt) => (0 < 0)
 | (Lbrackt) => (0 < 0)
 | (Rbrackt) => (0 < 0)
 | (Underbart) => (0 < 0)
 | (Lbracet) => (0 < 0)
 | (Bart) => (0 < 0)
 | (Rbracet) => (0 < 0)
 | (Andt) => (0 < 0)
 | (Andalsot) => (0 < 0)
 | (Ast) => (0 < 0)
 | (Caset) => (0 < 0)
 | (Datatypet) => (0 < 0)
 | (Elset) => (0 < 0)
 | (Endt) => (0 < 0)
 | (Eqtypet) => (0 < 0)
 | (Exceptiont) => (0 < 0)
 | (Fnt) => (0 < 0)
 | (Funt) => (0 < 0)
 | (Handlet) => (0 < 0)
 | (Ift) => (0 < 0)
 | (Int_1) => (0 < 0)
 | (Includet) => (0 < 0)
 | (Lett) => (0 < 0)
 | (Localt) => (0 < 0)
 | (Oft) => (0 < 0)
 | (Opt_1) => (0 < 0)
 | (Opent) => (0 < 0)
 | (Orelset) => (0 < 0)
 | (Raiset) => (0 < 0)
 | (Rect) => (0 < 0)
 | (Sharingt) => (0 < 0)
 | (Sigt) => (0 < 0)
 | (Signaturet) => (0 < 0)
 | (Structt) => (0 < 0)
 | (Structuret) => (0 < 0)
 | (Thent) => (0 < 0)
 | (Typet) => (0 < 0)
 | (Valt) => (0 < 0)
 | (Wheret) => (0 < 0)
 | (Whilet) => (0 < 0)
 | (Witht) => (0 < 0)
 | (Withtypet) => (0 < 0)
 | (Intt v2) => (0 < 0)
 | (Hexintt v3) => (0 < 0)
 | (Wordt v4) => (0 < 0)
 | (Realt v5) => (0 < 0)
 | (Stringt v6) => (0 <= 0)
 | (Chart v7) => (0 < 0)
 | (Tyvart v8) => (0 < 0)
 | (Alphat v9) => (0 < 0)
 | (Symbolt v10) => (0 < 0)
 | (Longidt (v12, v11)) => (0 < 0)
 | (Ffit v13) => (0 < 0)
 | (Replidt v14) => (0 < 0)));

val purepeg = (Recordtypeispeg ((((nt (Ndecls)) id) (Lrok)), (#"D" :: (#"i" :: (#"d" :: (#"n" :: (#"'" :: (#"t" :: (#" " :: (#"e" :: (#"x" :: (#"p" :: (#"e" :: (#"c" :: (#"t" :: (#" " :: (#"a" :: (#"n" :: (#" " :: (#"E" :: (#"O" :: (#"F" :: [])))))))))))))))))))), (#"F" :: (#"a" :: (#"i" :: (#"l" :: (#"e" :: (#"d" :: (#" " :: (#"t" :: (#"o" :: (#" " :: (#"s" :: (#"e" :: (#"e" :: (#" " :: (#"e" :: (#"x" :: (#"p" :: (#"e" :: (#"c" :: (#"t" :: (#"e" :: (#"d" :: (#" " :: (#"t" :: (#"o" :: (#"k" :: (#"e" :: (#"n" :: [])))))))))))))))))))))))))))), (#"F" :: (#"a" :: (#"i" :: (#"l" :: (#"e" :: (#"d" :: (#" " :: (#"t" :: (#"o" :: (#" " :: (#"s" :: (#"e" :: (#"e" :: (#" " :: (#"e" :: (#"x" :: (#"p" :: (#"e" :: (#"c" :: (#"t" :: (#"e" :: (#"d" :: (#" " :: (#"t" :: (#"o" :: (#"k" :: (#"e" :: (#"n" :: (#";" :: (#" " :: (#"s" :: (#"a" :: (#"w" :: (#" " :: (#"E" :: (#"O" :: (#"F" :: (#" " :: (#"i" :: (#"n" :: (#"s" :: (#"t" :: (#"e" :: (#"a" :: (#"d" :: []))))))))))))))))))))))))))))))))))))))))))))), (#"N" :: (#"o" :: (#"t" :: (#" " :: (#"c" :: (#"o" :: (#"m" :: (#"b" :: (#"i" :: (#"n" :: (#"a" :: (#"t" :: (#"o" :: (#"r" :: (#" " :: (#"f" :: (#"a" :: (#"i" :: (#"l" :: (#"e" :: (#"d" :: []))))))))))))))))))))), (#"I" :: (#"n" :: (#"d" :: (#"e" :: (#"n" :: (#"t" :: (#"a" :: (#"t" :: (#"i" :: (#"o" :: (#"n" :: (#" " :: (#"f" :: (#"a" :: (#"i" :: (#"l" :: (#"u" :: (#"r" :: (#"e" :: []))))))))))))))))))), ((fupdate_list []) (((Inl (Ndecls)), ((pegf (Rpt ((((nt (Ndecl)) id) (Lreq)), flat))) (mknt (Ndecls)))) :: (((Inl (Ndecl)), (choicel (((seql ((Tok_1 (lcname_tok, mktoklf, (Lreq))) :: ((Tok_1 ((fn v1 => ((Symbolt (#":" :: (#":" :: []))) = v1)), mktoklf, (Lrgt))) :: ((((nt (Nty)) id) (Lrgt)) :: [])))) (mknt (Ndecl))) :: (((seql ((Tok_1 ((fn v2 => ((Alphat (#"d" :: (#"a" :: (#"t" :: (#"a" :: []))))) = v2)), mktoklf, (Lreq))) :: ((Tok_1 (capname_tok, mktoklf, (Lrgt))) :: ((Rpt ((Tok_1 (lcname_tok, mktoklf, (Lrgt))), flat)) :: ((Tok_1 ((fn v3 => ((Equalst) = v3)), mktoklf, (Lrgt))) :: (((sepby1 (((nt (Ntycondecl)) id) (Lrgt))) (Tok_1 ((fn v4 => ((Bart) = v4)), mktoklf, (Lrgt)))) :: [])))))) (mknt (Ndecl))) :: (((pegf (((nt (Nvalbinding)) id) (Lreq))) (mknt (Ndecl))) :: []))))) :: (((Inl (Nvalbinding)), ((seql ((((nt (Nexpeq)) id) (Lreq)) :: ((Tok_1 ((fn v5 => ((Equalst) = v5)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: [])))) (mknt (Nvalbinding)))) :: (((Inl (Ntycondecl)), ((seql ((Tok_1 (capname_tok, mktoklf, (Lrge))) :: ((Rpt ((((nt (Ntybase)) id) (Lrge)), flat)) :: []))) (mknt (Ntycondecl)))) :: (((Inl (Ntybase)), (choicel (((pegf (Tok_1 (capname_tok, mktoklf, (Lrge)))) (mknt (Ntybase))) :: (((pegf (Tok_1 (lcname_tok, mktoklf, (Lrge)))) (mknt (Ntybase))) :: (((seql ((Tok_1 ((fn v6 => ((Lpart) = v6)), mktoklf, (Lrge))) :: (((sepby (((nt (Nty)) id) (Lrge))) (Tok_1 ((fn v7 => ((Commat) = v7)), mktoklf, (Lrge)))) :: ((Tok_1 ((fn v8 => ((Rpart) = v8)), mktoklf, (Lrge))) :: [])))) (mknt (Ntybase))) :: (((seql ((Tok_1 ((fn v9 => ((Lbrackt) = v9)), mktoklf, (Lrge))) :: ((((nt (Nty)) id) (Lrge)) :: ((Tok_1 ((fn v10 => ((Rbrackt) = v10)), mktoklf, (Lrge))) :: [])))) (mknt (Ntybase))) :: [])))))) :: (((Inl (Ntyapp)), (choicel ((Seq_1 ((Tok_1 (capname_tok, mktoklf, (Lrge))), (Choice ((rpt1 (((nt (Ntybase)) id) (Lrge))), (Empty []), sumid)), (fn v12 => (fn v11 => (if (CML_List.null v11)
 then ((mknt (Ntyapp)) ((mknt (Ntybase)) v12))
 else ((mknt (Ntyapp)) (v12 @ v11))))))) :: (((pegf (((nt (Ntybase)) id) (Lrge))) (mknt (Ntyapp))) :: [])))) :: (((Inl (Nty)), ((pegf ((sepby1 (((nt (Ntyapp)) id) (Lrge))) (Tok_1 ((fn v13 => ((Symbolt (#"-" :: (#">" :: []))) = v13)), mktoklf, (Lrge))))) (mknt (Nty)))) :: (((Inl (Neqbindseq)), (choicel (((seql ((Tok_1 ((fn v14 => ((Lbracet) = v14)), mktoklf, (Lrgt))) :: (((sepby (((nt (Nfreeeqbind)) id) (Lrok))) (Tok_1 ((fn v15 => ((Semicolont) = v15)), mktoklf, (Lrok)))) :: ((choicel ((Tok_1 ((fn v16 => ((Semicolont) = v16)), mktoklf, (Lrok))) :: ((Empty []) :: []))) :: ((Tok_1 ((fn v17 => ((Rbracet) = v17)), mktoklf, (Lrok))) :: []))))) (mknt (Neqbindseq))) :: ((((nt (Neqbindseq')) id) (Lrgt)) :: [])))) :: (((Inl (Neqbindseq')), ((pegf (Rpt ((((nt (Neqbind)) id) (Lreq)), flat))) (mknt (Neqbindseq)))) :: (((Inl (Nfreeeqbind)), (choicel (((seql ((((nt (Nexp)) id) (Lrok)) :: ((Tok_1 ((fn v18 => ((Equalst) = v18)), mktoklf, (Lrok))) :: ((((nt (Nexp)) id) (Lrok)) :: [])))) (mknt (Neqbind))) :: (((seql ((Tok_1 (lcname_tok, mktoklf, (Lrok))) :: ((Tok_1 ((fn v19 => ((Symbolt (#":" :: (#":" :: []))) = v19)), mktoklf, (Lrok))) :: ((((nt (Nty)) id) (Lrok)) :: [])))) (mknt (Neqbind))) :: [])))) :: (((Inl (Neqbind)), (choicel (((seql ((((nt (Nexpeq)) id) (Lreq)) :: ((Tok_1 ((fn v20 => ((Equalst) = v20)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lrgt)) :: [])))) (mknt (Neqbind))) :: (((seql ((Tok_1 (lcname_tok, mktoklf, (Lreq))) :: ((Tok_1 ((fn v21 => ((Symbolt (#":" :: (#":" :: []))) = v21)), mktoklf, (Lrgt))) :: ((((nt (Nty)) id) (Lrgt)) :: [])))) (mknt (Neqbind))) :: [])))) :: (((Inl (Nop)), (choicel (((pegf (Tok_1 (issymbolopt, mktoklf, (Lreq)))) (mknt (Nop))) :: (((seql ((Tok_1 ((fn v22 => ((Symbolt (#"`" :: [])) = v22)), mktoklf, (Lreq))) :: ((Tok_1 (isalphat, mktoklf, (Lrge))) :: ((Tok_1 ((fn v23 => ((Symbolt (#"`" :: [])) = v23)), mktoklf, (Lrge))) :: [])))) (mknt (Nop))) :: [])))) :: (((Inl (Niexp)), ((seql ((((nt (Nfexp)) id) (Lreq)) :: ((Rpt (((seql ((((nt (Nop)) id) (Lrgt)) :: ((((nt (Nfexp2)) id) (Lreq)) :: []))) id), flat)) :: []))) (mknt (Niexp)))) :: (((Inl (Niexpeq)), ((seql ((((nt (Nfexpeq)) id) (Lreq)) :: ((Rpt (((seql ((((nt (Nop)) id) (Lrge)) :: ((((nt (Nfexp2)) id) (Lrge)) :: []))) id), flat)) :: []))) (mknt (Niexp)))) :: (((Inl (Nfexp2)), ((pegf (choicel ((((nt (Nlsafeexp)) id) (Lrge)) :: ((((nt (Nfexp)) id) (Lrge)) :: [])))) (mknt (Nfexp2)))) :: (((Inl (Nfexp)), ((seql ((((nt (Naexp)) id) (Lreq)) :: ((Rpt ((((nt (Naexp)) id) (Lreq)), flat)) :: []))) (mknt (Nfexp)))) :: (((Inl (Nfexpeq)), ((seql ((((nt (Naexpeq)) id) (Lreq)) :: ((Rpt ((((nt (Naexp)) id) (Lreq)), flat)) :: []))) (mknt (Nfexp)))) :: (((Inl (Ndoblock)), (choicel (((seql ((Tok_1 ((fn v24 => ((Lbracet) = v24)), mktoklf, (Lrgt))) :: ((((nt (Ndostmtseq)) id) (Lrok)) :: ((Tok_1 ((fn v25 => ((Rbracet) = v25)), mktoklf, (Lrok))) :: [])))) ((cml_o (mknt (Ndoblock))) ((cml_o CML_List.front) (drop_1 1)))) :: (((pegf (((nt (Ndoblocklayout)) id) (Lrgt))) (mknt (Ndoblock))) :: [])))) :: (((Inl (Ndoblocklayout)), (rpt1 (((nt (Ndostmtseqeq)) id) (Lreq)))) :: (((Inl (Ndostmtseq)), ((pegf ((sepby1 (((nt (Ndostmt)) id) (Lreq))) (Tok_1 ((fn v26 => ((Semicolont) = v26)), mktoklf, (Lrgt))))) odds)) :: (((Inl (Ndostmtseqeq)), ((seql ((((nt (Ndostmteq)) id) (Lreq)) :: ((Rpt (((seql ((Tok_1 ((fn v27 => ((Semicolont) = v27)), mktoklf, (Lrgt))) :: ((((nt (Ndostmt)) id) (Lreq)) :: []))) id), flat)) :: []))) odds)) :: (((Inl (Ndostmt)), (choicel (((seql ((((nt (Nexp)) id) (Lreq)) :: ((choicel (((seql ((Tok_1 ((fn v28 => ((Symbolt (#"<" :: (#"-" :: []))) = v28)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lrgt)) :: []))) id) :: ((Empty []) :: []))) :: []))) (mknt (Ndostmt))) :: (((seql ((Tok_1 ((fn v29 => ((Lett) = v29)), mktoklf, (Lrgt))) :: ((((nt (Neqbindseq')) id) (Lrgt)) :: []))) (mknt (Ndostmt))) :: [])))) :: (((Inl (Ndostmteq)), (choicel (((seql ((((nt (Nexpeq)) id) (Lreq)) :: ((choicel (((seql ((Tok_1 ((fn v30 => ((Symbolt (#"<" :: (#"-" :: []))) = v30)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lrgt)) :: []))) id) :: ((Empty []) :: []))) :: []))) (mknt (Ndostmt))) :: (((seql ((Tok_1 ((fn v31 => ((Lett) = v31)), mktoklf, (Lreq))) :: ((((nt (Neqbindseq')) id) (Lrgt)) :: []))) (mknt (Ndostmt))) :: [])))) :: (((Inl (Nlsafeexp)), (choicel (((seql ((Tok_1 ((fn v32 => ((Symbolt (#"\\" :: [])) = v32)), mktoklf, (Lrgt))) :: ((rpt1 (((nt (Napat)) id) (Lreq))) :: ((Tok_1 ((fn v33 => ((Symbolt (#"-" :: (#">" :: []))) = v33)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: []))))) (mknt (Nexp))) :: (((seql ((Tok_1 ((fn v34 => ((Ift) = v34)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: ((Tok_1 ((fn v35 => ((Thent) = v35)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: ((Tok_1 ((fn v36 => ((Elset) = v36)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: []))))))) (mknt (Nexp))) :: (((seql ((Tok_1 ((fn v37 => ((Lett) = v37)), mktoklf, (Lrgt))) :: ((((nt (Neqbindseq)) id) (Lreq)) :: ((Tok_1 ((fn v38 => ((Int_1) = v38)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: []))))) (mknt (Nexp))) :: (((seql ((Tok_1 ((fn v39 => ((Alphat (#"d" :: (#"o" :: []))) = v39)), mktoklf, (Lrgt))) :: ((((nt (Ndoblock)) id) (Lreq)) :: []))) (mknt (Nexp))) :: (((seql ((Tok_1 ((fn v40 => ((Caset) = v40)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: ((Tok_1 ((fn v41 => ((Oft) = v41)), mktoklf, (Lrgt))) :: ((((nt (Npatalts)) id) (Lrgt)) :: []))))) (mknt (Nexp))) :: []))))))) :: (((Inl (Nlsafeexpeq)), (choicel (((seql ((Tok_1 ((fn v42 => ((Symbolt (#"\\" :: [])) = v42)), mktoklf, (Lreq))) :: ((rpt1 (((nt (Napat)) id) (Lreq))) :: ((Tok_1 ((fn v43 => ((Symbolt (#"-" :: (#">" :: []))) = v43)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: []))))) (mknt (Nexp))) :: (((seql ((Tok_1 ((fn v44 => ((Ift) = v44)), mktoklf, (Lreq))) :: ((((nt (Nexp)) id) (Lreq)) :: ((Tok_1 ((fn v45 => ((Thent) = v45)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: ((Tok_1 ((fn v46 => ((Elset) = v46)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: []))))))) (mknt (Nexp))) :: (((seql ((Tok_1 ((fn v47 => ((Lett) = v47)), mktoklf, (Lreq))) :: ((((nt (Neqbindseq)) id) (Lreq)) :: ((Tok_1 ((fn v48 => ((Int_1) = v48)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lreq)) :: []))))) (mknt (Nexp))) :: (((seql ((Tok_1 ((fn v49 => ((Alphat (#"d" :: (#"o" :: []))) = v49)), mktoklf, (Lreq))) :: ((((nt (Ndoblock)) id) (Lrgt)) :: []))) (mknt (Nexp))) :: (((seql ((Tok_1 ((fn v50 => ((Caset) = v50)), mktoklf, (Lreq))) :: ((((nt (Nexp)) id) (Lreq)) :: ((Tok_1 ((fn v51 => ((Oft) = v51)), mktoklf, (Lrgt))) :: ((((nt (Npatalts)) id) (Lrgt)) :: []))))) (mknt (Nexp))) :: []))))))) :: (((Inl (Napat)), (choicel (((pegf (Tok_1 (lcname_tok, mktoklf, (Lrgt)))) (mknt (Napat))) :: (((pegf (((nt (Nlit)) id) (Lreq))) (mknt (Napat))) :: (((pegf (Tok_1 ((fn v52 => ((Underbart) = v52)), mktoklf, (Lrgt)))) (mknt (Napat))) :: []))))) :: (((Inl (Npat)), ((pegf (((nt (Napat)) id) (Lreq))) (mknt (Npat)))) :: (((Inl (Npatalts)), ((pegf (Rpt ((((nt (Npatalt)) id) (Lreq)), flat))) (mknt (Npatalts)))) :: (((Inl (Npatalt)), ((seql ((((nt (Nexpeq)) id) (Lreq)) :: ((Tok_1 ((fn v53 => ((Symbolt (#"-" :: (#">" :: []))) = v53)), mktoklf, (Lrgt))) :: ((((nt (Nexp)) id) (Lrgt)) :: [])))) (mknt (Npatalt)))) :: (((Inl (Nexp)), (choicel ((((nt (Nlsafeexp)) id) (Lreq)) :: (((pegf (((nt (Niexp)) id) (Lreq))) (mknt (Nexp))) :: [])))) :: (((Inl (Nexpeq)), (choicel ((((nt (Nlsafeexpeq)) id) (Lreq)) :: (((pegf (((nt (Niexpeq)) id) (Lreq))) (mknt (Nexp))) :: [])))) :: (((Inl (Naexp)), (choicel (((pegf (((nt (Nlit)) id) (Lrgt))) (mknt (Naexp))) :: (((seql ((Tok_1 ((fn v54 => ((Lpart) = v54)), mktoklf, (Lrgt))) :: (((sepby (((nt (Nexp)) id) (Lreq))) (Tok_1 ((fn v55 => ((Commat) = v55)), mktoklf, (Lrgt)))) :: ((Tok_1 ((fn v56 => ((Rpart) = v56)), mktoklf, (Lrgt))) :: [])))) (mknt (Naexp))) :: (((seql ((Tok_1 ((fn v57 => ((Lbrackt) = v57)), mktoklf, (Lrgt))) :: (((sepby (((nt (Nexp)) id) (Lreq))) (Tok_1 ((fn v58 => ((Commat) = v58)), mktoklf, (Lrgt)))) :: ((Tok_1 ((fn v59 => ((Rbrackt) = v59)), mktoklf, (Lrgt))) :: [])))) (mknt (Naexp))) :: (((pegf (Tok_1 (isalphat, mktoklf, (Lrgt)))) (mknt (Naexp))) :: (((pegf (Tok_1 ((fn v60 => ((Underbart) = v60)), mktoklf, (Lrgt)))) (mknt (Naexp))) :: (((pegf (Tok_1 (((cml_o CML_Option.isSome) destffit), mktoklf, (Lrgt)))) (mknt (Naexp))) :: [])))))))) :: (((Inl (Naexpeq)), (choicel (((pegf (((nt (Nlit)) id) (Lreq))) (mknt (Naexp))) :: (((seql ((Tok_1 ((fn v61 => ((Lpart) = v61)), mktoklf, (Lreq))) :: (((sepby (((nt (Nexp)) id) (Lreq))) (Tok_1 ((fn v62 => ((Commat) = v62)), mktoklf, (Lrgt)))) :: ((Tok_1 ((fn v63 => ((Rpart) = v63)), mktoklf, (Lrgt))) :: [])))) (mknt (Naexp))) :: (((seql ((Tok_1 ((fn v64 => ((Lbrackt) = v64)), mktoklf, (Lreq))) :: (((sepby (((nt (Nexp)) id) (Lreq))) (Tok_1 ((fn v65 => ((Commat) = v65)), mktoklf, (Lrgt)))) :: ((Tok_1 ((fn v66 => ((Rbrackt) = v66)), mktoklf, (Lrgt))) :: [])))) (mknt (Naexp))) :: (((pegf (Tok_1 (isalphat, mktoklf, (Lreq)))) (mknt (Naexp))) :: (((pegf (Tok_1 ((fn v67 => ((Underbart) = v67)), mktoklf, (Lreq)))) (mknt (Naexp))) :: (((pegf (Tok_1 (((cml_o CML_Option.isSome) destffit), mktoklf, (Lreq)))) (mknt (Naexp))) :: [])))))))) :: (((Inl (Nlit)), (choicel ((Tok_1 (isint, ((cml_o (mknt (Nlit))) mktoklf), (Lreq))) :: ((Tok_1 (isstring, ((cml_o (mknt (Nlit))) mktoklf), (Lreq))) :: [])))) :: [])))))))))))))))))))))))))))))))))))));

val locnle = (fn v7 => (fn v8 => (case v7 of
   (Unknownpt) => (0 <= 0)
 | (Eofpt) => (case v8 of
   (Unknownpt) => (0 < 0)
 | (Eofpt) => (0 <= 0)
 | (Posn (v2, v1)) => (0 < 0))
 | (Posn (v6, v5)) => (case v8 of
   (Unknownpt) => (0 < 0)
 | (Eofpt) => (0 <= 0)
 | (Posn (v4, v3)) => ((v6 < v4) orelse ((v6 = v4) andalso (v5 <= v3)))))));

datatype ispeg_locpred = Lpxge of int | Lpbot | Lpival of int * int;

datatype ('a, 'c, 'e) ispeg_pegresult = Failure of location_locs * 'e | Success of 'a * 'c * ((location_locs * 'e)) option * ispeg_locpred;

datatype ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont = Failed | Done | Listsym of ('atok, 'bnt, 'cvalue, 'err) ispeg_ispegsym * (('cvalue) list -> 'cvalue) * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Poplist of (('cvalue) list -> 'cvalue) * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Restoreeo of ((location_locs * 'err)) option * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Returnto of (('atok * location_locs)) list * (('cvalue) option) list * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Cmpeo of ((location_locs * 'err)) option * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Cmperrs of ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Adderr of location_locs * 'err * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Droperr of ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Setlps of ispeg_locpred * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Genifail of ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Lpcomp of ispeg_locpred * ispeg_locrel * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Appf2 of ('cvalue -> ('cvalue -> 'cvalue)) * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Appf1 of ('cvalue -> 'cvalue) * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont | Ksym of ('atok, 'bnt, 'cvalue, 'err) ispeg_ispegsym * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont;

datatype ('atok, 'bnt, 'cvalue, 'err) ispegexec_evalcase = Looped | Result of ((('atok * location_locs)) list, 'cvalue, 'err) ispeg_pegresult | Ap of ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont * (('atok * location_locs)) list * ispeg_locpred * (('cvalue) option) list * ((location_locs * 'err)) option * ((location_locs * 'err)) list | Ev of ('atok, 'bnt, 'cvalue, 'err) ispeg_ispegsym * (('atok * location_locs)) list * ispeg_locpred * (('cvalue) option) list * ((location_locs * 'err)) option * ((location_locs * 'err)) list * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont * ('atok, 'bnt, 'cvalue, 'err) ispegexec_kont;

val sloc = (fn v3 => (case v3 of
   [] => (Locs ((Eofpt), (Eofpt)))
 | (v2 :: v1) => (snd v2)));

val optmax = (fn v4 => (fn v5 => (fn v6 => (case v5 of
   (NONE) => (case v6 of
   (NONE) => (NONE)
 | (SOME v1) => (SOME v1))
 | (SOME v3) => (case v6 of
   (NONE) => (SOME v3)
 | (SOME v2) => (SOME ((v4 v3) v2)))))));

val locsle = (fn v6 => (fn v5 => (case v6 of
   (Locs (v4, v3)) => (case v5 of
   (Locs (v2, v1)) => ((locnle v4) v2)))));

val maxerr = (fn v6 => (fn v5 => (case v6 of
   (v4, v3) => (case v5 of
   (v2, v1) => (if ((locsle v4) v2)
 then (v2, v1)
 else (v4, v3))))));

val conjpred = (fn v13 => (fn v14 => (case v13 of
   (Lpival (v7, v6)) => (case v14 of
   (Lpival (v3, v2)) => (if (((v7 + v6) < v3) orelse ((v3 + v2) < v7))
 then (Lpbot)
 else (let val v1 = ((max v7) v3)
 in (Lpival (v1, (let val k = (((min (v7 + v6)) (v3 + v2)) - v1)
 in (if (k < 0)
 then 0
 else k) end))) end))
 | (Lpbot) => (Lpbot)
 | (Lpxge v5) => (if ((v7 + v6) < v5)
 then (Lpbot)
 else (let val v4 = ((max v7) v5)
 in (Lpival (((max v7) v5), (let val k = ((v7 + v6) - v4)
 in (if (k < 0)
 then 0
 else k) end))) end)))
 | (Lpbot) => (Lpbot)
 | (Lpxge v12) => (case v14 of
   (Lpival (v10, v9)) => (if ((v10 + v9) < v12)
 then (Lpbot)
 else (let val v8 = ((max v10) v12)
 in (Lpival (((max v10) v12), (let val k = ((v10 + v9) - v8)
 in (if (k < 0)
 then 0
 else k) end))) end))
 | (Lpbot) => (Lpbot)
 | (Lpxge v11) => (Lpxge ((max v12) v11))))));

val rel_at_col = (fn v1 => (fn v2 => (case v1 of
   (Lreq) => (Lpival (v2, 0))
 | (Lrge) => (Lpival (0, v2))
 | (Lrgt) => (if (v2 = 0)
 then (Lpbot)
 else (Lpival (0, (let val k = (v2 - 1)
 in (if (k < 0)
 then 0
 else k) end))))
 | (Lrok) => (Lpxge 0))));

val loccol = (fn v3 => (case v3 of
   (Unknownpt) => 0
 | (Eofpt) => 0
 | (Posn (v2, v1)) => v1));

val precomp = (fn v4 => (fn v5 => (case v4 of
   (Lpival (v2, v1)) => (case v5 of
   (Lreq) => (Lpival (v2, v1))
 | (Lrge) => (Lpxge v2)
 | (Lrgt) => (Lpxge (v2 + 1))
 | (Lrok) => (Lpxge 0))
 | (Lpbot) => (Lpbot)
 | (Lpxge v3) => (case v5 of
   (Lreq) => (Lpxge v3)
 | (Lrge) => (Lpxge v3)
 | (Lrgt) => (Lpxge (v3 + 1))
 | (Lrok) => (Lpxge 0)))));

val comppred = (fn v4 => (fn v5 => (case v5 of
   (Lpival (v2, v1)) => (case v4 of
   (Lreq) => (Lpival (v2, v1))
 | (Lrge) => (Lpival (0, (v2 + v1)))
 | (Lrgt) => (if ((v2 = 0) andalso (v1 = 0))
 then (Lpbot)
 else (Lpival (0, (let val k = ((v2 + v1) - 1)
 in (if (k < 0)
 then 0
 else k) end))))
 | (Lrok) => (Lpxge 0))
 | (Lpbot) => (Lpbot)
 | (Lpxge v3) => (case v4 of
   (Lreq) => (Lpxge v3)
 | (Lrge) => (Lpxge 0)
 | (Lrgt) => (Lpxge 0)
 | (Lrok) => (Lpxge 0)))));

fun poplist_aux v4 = (fn v5 => (case v5 of
   [] => (v4, [])
 | (v3 :: v2) => (case v3 of
   (NONE) => (v4, v2)
 | (SOME v1) => ((poplist_aux (v1 :: v4)) v2))));

val poplistval = (fn v4 => (fn v5 => (let val v3 = ((poplist_aux []) v5)
 in (case v3 of
   (v2, v1) => ((SOME (v4 v2)) :: v1)) end)));

val coreloop = (fn v138 => (fn v139 => (((owhile (fn v16 => (case v16 of
   (Ev (v8, v7, v6, v5, v4, v3, v2, v1)) => (0 <= 0)
 | (Ap (v14, v13, v12, v11, v10, v9)) => (0 <= 0)
 | (Result v15) => (0 < 0)
 | (Looped) => (0 <= 0)))) (fn v137 => (case v137 of
   (Ev (v64, v63, v62, v61, v60, v59, v58, v57)) => (case v64 of
   (Empty v18) => (if (v62 = (Lpbot))
 then (let val v17 = ((sloc v63), (recordtypeispegseldefifail v138))
 in (Ap (v57, v63, (Lpbot), v61, (((optmax maxerr) v60) (SOME v17)), (v17 :: v59))) end)
 else (Ap (v58, v63, v62, ((SOME v18) :: v61), v60, v59)))
 | (Any v23) => (case v63 of
   [] => (let val v19 = ((Locs ((Eofpt), (Eofpt))), (recordtypeispegseldefanyeof v138))
 in (Ap (v57, v63, v62, v61, (((optmax maxerr) v60) (SOME v19)), (v19 :: v59))) end)
 | (v22 :: v21) => (if (v62 = (Lpbot))
 then (let val v20 = ((snd v22), (recordtypeispegseldefifail v138))
 in (Ap (v57, v63, (Lpbot), v61, (((optmax maxerr) v60) (SOME v20)), (v20 :: v59))) end)
 else (Ap (v58, v21, v62, ((SOME (v23 v22)) :: v61), v60, v59))))
 | (Tok_1 (v36, v35, v34)) => (case v63 of
   [] => (let val v24 = ((Locs ((Eofpt), (Eofpt))), (recordtypeispegseldeftokeof v138))
 in (Ap (v57, v63, v62, v61, (((optmax maxerr) v60) (SOME v24)), (v24 :: v59))) end)
 | (v33 :: v32) => (case v33 of
   (v31, v30) => (case v30 of
   (Locs (v29, v28)) => (if (v36 v31)
 then (let val v26 = ((conjpred v62) ((rel_at_col v34) (loccol v29)))
 in (if (v26 = (Lpbot))
 then (let val v25 = ((sloc v63), (recordtypeispegseldefifail v138))
 in (Ap (v57, v63, v62, v61, (((optmax maxerr) v60) (SOME v25)), (v25 :: v59))) end)
 else (Ap (v58, v32, v26, ((SOME (v35 (v31, (Locs (v29, v28))))) :: v61), v60, v59))) end)
 else (let val v27 = ((sloc v63), (recordtypeispegseldeftokfalse v138))
 in (Ap (v57, v63, v62, v61, (((optmax maxerr) v60) (SOME v27)), (v27 :: v59))) end)))))
 | (Nt_1 (v40, v39, v38)) => (case ((CML_Alist.lookup (recordtypeispegseldefrules v138)) v40) of
   (NONE) => (Looped)
 | (SOME v37) => (Ev (v37, v63, ((precomp v62) v38), v61, v60, v59, (Lpcomp (v62, v38, (Appf1 (v39, v58)), (Setlps (v62, (Restoreeo (v60, (Returnto (v63, v61, (Genifail v57))))))))), (Setlps (v62, v57)))))
 | (Seq_1 (v43, v42, v41)) => (Ev (v43, v63, v62, v61, v60, v59, (Restoreeo (v60, (Ksym (v42, (Appf2 (v41, v58)), (Returnto (v63, v61, (Setlps (v62, v57)))))))), (Setlps (v62, (Cmpeo (v60, (Returnto (v63, v61, v57))))))))
 | (Choice (v48, v47, v46)) => (Ev (v48, v63, v62, v61, v60, v59, (Appf1 (((cml_o v46) (fn v44 => (Inl v44))), v58)), (Returnto (v63, v61, (Setlps (v62, (Ksym (v47, (Droperr (Appf1 (((cml_o v46) (fn v45 => (Inr v45))), v58))), (Cmperrs v57)))))))))
 | (Rpt (v51, v50)) => (if (v62 = (Lpbot))
 then (let val v49 = ((sloc v63), (recordtypeispegseldefifail v138))
 in (Ap (v57, v63, (Lpbot), v61, (((optmax maxerr) v60) (SOME v49)), (v49 :: v59))) end)
 else (Ev (v51, v63, v62, ((NONE) :: v61), v60, v59, (Restoreeo (v60, (Listsym (v51, v50, v58)))), (Setlps (v62, (Poplist (v50, v58)))))))
 | (Not (v54, v53)) => (if (v62 = (Lpbot))
 then (let val v52 = ((sloc v63), (recordtypeispegseldefifail v138))
 in (Ap (v57, v63, (Lpbot), v61, (((optmax maxerr) v60) (SOME v52)), (v52 :: v59))) end)
 else (Ev (v54, v63, v62, v61, v60, v59, (Restoreeo (v60, (Returnto (v63, v61, (Setlps (v62, (Adderr ((sloc v63), (recordtypeispegseldefnotfail v138), v57)))))))), (Restoreeo (v60, (Returnto (v63, ((SOME v53) :: v61), (Droperr v58))))))))
 | (Error v56) => (let val v55 = ((sloc v63), v56)
 in (Ap (v57, v63, v62, v61, (((optmax maxerr) v60) (SOME v55)), (v55 :: v59))) end))
 | (Ap (v135, v134, v133, v132, v131, v130)) => (case v135 of
   (Ksym (v67, v66, v65)) => (Ev (v67, v134, v133, v132, v131, v130, v66, v65))
 | (Appf1 (v72, v71)) => (case v132 of
   [] => (Looped)
 | (v70 :: v69) => (case v70 of
   (NONE) => (Looped)
 | (SOME v68) => (Ap (v71, v134, v133, ((SOME (v72 v68)) :: v69), v131, v130))))
 | (Appf2 (v80, v79)) => (case v132 of
   [] => (Looped)
 | (v78 :: v77) => (case v77 of
   [] => (Looped)
 | (v76 :: v75) => (case v76 of
   (NONE) => (Looped)
 | (SOME v74) => (case v78 of
   (NONE) => (Looped)
 | (SOME v73) => (Ap (v79, v134, v133, ((SOME ((v80 v74) v73)) :: v75), v131, v130))))))
 | (Lpcomp (v85, v84, v83, v82)) => (let val v81 = ((conjpred v85) ((comppred v84) v133))
 in (if (v81 = (Lpbot))
 then (Ap (v82, v134, v133, v132, v131, v130))
 else (Ap (v83, v134, v81, v132, v131, v130))) end)
 | (Genifail v87) => (let val v86 = ((sloc v134), (recordtypeispegseldefifail v138))
 in (Ap (v87, v134, v133, v132, (((optmax maxerr) v131) (SOME v86)), (v86 :: v130))) end)
 | (Setlps (v89, v88)) => (Ap (v88, v134, v89, v132, v131, v130))
 | (Droperr v92) => (case v130 of
   [] => (Looped)
 | (v91 :: v90) => (Ap (v92, v134, v133, v132, v131, v90)))
 | (Adderr (v95, v94, v93)) => (Ap (v93, v134, v133, v132, (((optmax maxerr) v131) (SOME (v95, v94))), ((v95, v94) :: v130)))
 | (Cmperrs v104) => (case v130 of
   [] => (Looped)
 | (v103 :: v102) => (case v102 of
   [] => (Looped)
 | (v101 :: v100) => (case v101 of
   (v99, v98) => (case v103 of
   (v97, v96) => (Ap (v104, v134, v133, v132, v131, ((if ((locsle v99) v97)
 then (v97, v96)
 else (v99, v98)) :: v100)))))))
 | (Cmpeo (v110, v109)) => (case v130 of
   [] => (Looped)
 | (v108 :: v107) => (case v108 of
   (v106, v105) => (Ap (v109, v134, v133, v132, (((optmax maxerr) v110) (SOME (v106, v105))), ((v106, v105) :: v107)))))
 | (Returnto (v113, v112, v111)) => (Ap (v111, v113, v133, v112, v131, v130))
 | (Restoreeo (v115, v114)) => (Ap (v114, v134, v133, v132, v115, v130))
 | (Poplist (v119, v118)) => (case v130 of
   [] => (Looped)
 | (v117 :: v116) => (Ap (v118, v134, v133, ((poplistval v119) v132), v131, v116)))
 | (Listsym (v122, v121, v120)) => (Ev (v122, v134, v133, v132, v131, v130, (Restoreeo (v131, (Listsym (v122, v121, v120)))), (Setlps (v133, (Poplist (v121, v120))))))
 | (Done) => (case v132 of
   [] => (Looped)
 | (v125 :: v124) => (case v125 of
   (NONE) => (Looped)
 | (SOME v123) => (Result (Success (v134, v123, v131, v133)))))
 | (Failed) => (case v130 of
   [] => (Looped)
 | (v129 :: v128) => (case v129 of
   (v127, v126) => (Result (Failure (v127, v126))))))
 | (Result v136) => (Result v136)
 | (Looped) => (Looped)))) v139)));

val ispeg_exec = (fn v3 => (fn v4 => (fn v8 => (fn v10 => (fn v2 => (fn v5 => (fn v6 => (fn v9 => (fn v7 => (case ((coreloop v3) (Ev (v4, v8, v10, v2, v5, v6, v9, v7))) of
   (NONE) => (Looped)
 | (SOME v1) => v1))))))))));

val option_choice = (fn v3 => (fn v2 => (case v3 of
   (NONE) => v2
 | (SOME v1) => (SOME v1))));

fun grab' v7 = (fn v8 => (case v7 of
   [] => (SOME ([], []))
 | (v6 :: v5) => ((option_choice (case v6 of
   (NONE) => (NONE)
 | (SOME v4) => (case ((grab' v5) (CML_List.tl v8)) of
   (NONE) => (NONE)
 | (SOME v3) => (case v3 of
   (v2, v1) => (SOME ((v4 :: v2), v1)))))) (SOME ([], v8)))));

val destlf = (fn v6 => (case v6 of
   (Lf v3) => (case v3 of
   (v2, v1) => (SOME v2))
 | (Nd (v5, v4)) => (NONE)));

val desttok = (fn v3 => (case v3 of
   (Tok v1) => (SOME v1)
 | (Nt v2) => (NONE)));

val tokcheck = (fn v2 => (fn v3 => ((case (destlf v2) of
   (NONE) => (NONE)
 | (SOME v1) => (desttok v1)) = (SOME v3))));

fun grabsepby' v12 = (fn v13 => (fn v14 => (case v13 of
   [] => ([], [])
 | (v11 :: v10) => (case v10 of
   [] => (case v11 of
   (NONE) => ([], v14)
 | (SOME v1) => ((v1 :: []), []))
 | (v9 :: v8) => (case v11 of
   (NONE) => ([], v14)
 | (SOME v7) => (case v14 of
   [] => ([], [])
 | (v6 :: v5) => (case v5 of
   [] => ([], [])
 | (v4 :: v3) => (if ((tokcheck v4) v12)
 then (((CML_Pair.map (fn v2 => (v7 :: v2))) id) (((grabsepby' v12) v8) v3))
 else ((v7 :: []), (CML_List.tl v14))))))))));

fun grabpairs' v7 = (fn v8 => (case v8 of
   [] => (SOME (CML_List.rev v7))
 | (v6 :: v5) => (case v5 of
   [] => (NONE)
 | (v4 :: v3) => (case (snd v6) of
   (NONE) => (NONE)
 | (SOME v2) => (case (fst v4) of
   (NONE) => (NONE)
 | (SOME v1) => ((grabpairs' ((Inr v1) :: ((Inl v2) :: v7))) v3))))));

val mksym = (fn v3 => (case (case (ohd v3) of
   (NONE) => (NONE)
 | (SOME v1) => (if (isupper v1)
 then (SOME (Expcon (v3, [])))
 else (if (if (v1 = #":")
 then (isalpha #":")
 else (0 <= 0))
 then (SOME (Expvar v3))
 else (if (v3 = (#":" :: []))
 then (SOME (Expcon ((#":" :: (#":" :: [])), [])))
 else (SOME (Expcon (v3, []))))))) of
   (NONE) => (Expvar v3)
 | (SOME v2) => v2));

fun mkfunty v5 = (case v5 of
   [] => (Tyop ((#"B" :: (#"o" :: (#"o" :: (#"l" :: [])))), []))
 | (v4 :: v3) => (case v3 of
   [] => v4
 | (v2 :: v1) => (Tyop ((#"F" :: (#"u" :: (#"n" :: []))), (v4 :: ((mkfunty (v2 :: v1)) :: []))))));

fun asttype v37 = (fn v38 => (case v38 of
   (Lf v1) => (NONE)
 | (Nd (v36, v35)) => (if (((fst v36) = (Inl v37)) = (0 < 0))
 then (NONE)
 else (if (v37 = (Ntybase))
 then (case v35 of
   [] => (NONE)
 | (v20 :: v19) => (case v19 of
   [] => (case (case (case (destlf v20) of
   (NONE) => (NONE)
 | (SOME v2) => (desttok v2)) of
   (NONE) => (NONE)
 | (SOME v3) => (destalphat v3)) of
   (NONE) => (NONE)
 | (SOME v5) => (case (ohd v5) of
   (NONE) => (NONE)
 | (SOME v4) => (if (isupper v4)
 then (SOME (Tyop (v5, [])))
 else (SOME (Tyvar v5)))))
 | (v18 :: v17) => (case v17 of
   [] => (if (((tokcheck v20) (Lpart)) andalso ((tokcheck v18) (Rpart)))
 then (SOME (Tytup []))
 else (NONE))
 | (v16 :: v15) => (case v15 of
   [] => (case (case (destlf v20) of
   (NONE) => (NONE)
 | (SOME v6) => (desttok v6)) of
   (NONE) => (NONE)
 | (SOME v8) => (case ((asttype (Nty)) v18) of
   (NONE) => (NONE)
 | (SOME v7) => (if (v8 = (Lpart))
 then (if ((tokcheck v16) (Rpart))
 then (SOME v7)
 else (NONE))
 else (if (v8 = (Lbrackt))
 then (if ((tokcheck v16) (Rbrackt))
 then (SOME (Tyop ((#"[" :: (#"]" :: [])), (v7 :: []))))
 else (NONE))
 else (NONE)))))
 | (v14 :: v13) => (if ((tokcheck v20) (Lpart))
 then (case ((asttype (Nty)) v18) of
   (NONE) => (NONE)
 | (SOME v12) => (case (((astseptype (Commat)) (Nty)) (v16 :: (v14 :: v13))) of
   (NONE) => (NONE)
 | (SOME v11) => (case v11 of
   (v10, v9) => (if (((list_rel tokcheck) v9) ((Rpart) :: []))
 then (SOME (Tytup (v12 :: v10)))
 else (NONE)))))
 else (NONE))))))
 else (if (v37 = (Nty))
 then (case v35 of
   [] => (NONE)
 | (v26 :: v25) => (case ((asttype (Ntyapp)) v26) of
   (NONE) => (NONE)
 | (SOME v24) => (case (((astseptype (Symbolt (#"-" :: (#">" :: [])))) (Ntyapp)) v25) of
   (NONE) => (NONE)
 | (SOME v23) => (case v23 of
   (v22, v21) => (SOME (mkfunty (v24 :: v22)))))))
 else (if (v37 = (Ntyapp))
 then (case v35 of
   [] => (NONE)
 | (v34 :: v33) => (case v33 of
   [] => ((asttype (Ntybase)) v34)
 | (v32 :: v31) => (case (case (case (destlf v34) of
   (NONE) => (NONE)
 | (SOME v27) => (desttok v27)) of
   (NONE) => (NONE)
 | (SOME v28) => (destalphat v28)) of
   (NONE) => (NONE)
 | (SOME v30) => (case (asttypebasel (v32 :: v31)) of
   (NONE) => (NONE)
 | (SOME v29) => (SOME (Tyop (v30, v29)))))))
 else (NONE)))))))
and astseptype v11 = (fn v9 => (fn v10 => (case v10 of
   [] => (SOME ([], []))
 | (v8 :: v7) => (case v7 of
   [] => (SOME ([], (v8 :: [])))
 | (v6 :: v5) => ((option_choice (if ((tokcheck v8) v11)
 then (case ((asttype v9) v6) of
   (NONE) => (NONE)
 | (SOME v4) => (case (((astseptype v11) v9) v5) of
   (NONE) => (NONE)
 | (SOME v3) => (case v3 of
   (v2, v1) => (SOME ((v4 :: v2), v1)))))
 else (NONE))) (SOME ([], (v8 :: (v6 :: v5)))))))))
and asttypebasel v5 = (case v5 of
   [] => (SOME [])
 | (v4 :: v3) => (case ((asttype (Ntybase)) v4) of
   (NONE) => (NONE)
 | (SOME v2) => (case (asttypebasel v3) of
   (NONE) => (NONE)
 | (SOME v1) => (SOME (v2 :: v1)))));

fun optlast v7 = (fn v8 => (fn v9 => (case v9 of
   [] => (NONE)
 | (v6 :: v5) => (case v5 of
   [] => ((CML_Option.map (v7 [])) (v8 v6))
 | (v4 :: v3) => (((optlast (fn v2 => (fn v1 => ((v7 (v6 :: v2)) v1)))) v8) (v4 :: v3))))));

val isfinal = (fn v11 => (case v11 of
   (v10, v9) => (case v10 of
   [] => (0 < 0)
 | (v8 :: v7) => (case v8 of
   (Inl v1) => (0 < 0)
 | (Inr v6) => (case v7 of
   [] => (case v9 of
   [] => (0 <= 0)
 | (v3 :: v2) => (0 < 0))
 | (v5 :: v4) => (0 < 0))))));

datatype precparser_tokrel = Shift_1 | Reduce;

datatype ('tok, 'trm) precparser_pMachine = Recordtypepmachine of (('tok * 'tok) -> (precparser_tokrel) option) * ('trm -> ('tok -> ('trm -> ('trm) option))) * ('tok -> 'trm) * ('tok -> bool) * ('trm -> ('trm -> ('trm) option));

val recordtypepmachineseldefrules = (fn v6 => (case v6 of
   (Recordtypepmachine (v5, v4, v3, v2, v1)) => v5));

val recordtypepmachineseldefreduce = (fn v6 => (case v6 of
   (Recordtypepmachine (v5, v4, v3, v2, v1)) => v4));

val recordtypepmachineseldeflift = (fn v6 => (case v6 of
   (Recordtypepmachine (v5, v4, v3, v2, v1)) => v3));

val recordtypepmachineseldefisop = (fn v6 => (case v6 of
   (Recordtypepmachine (v5, v4, v3, v2, v1)) => v2));

val recordtypepmachineseldefmkapp = (fn v6 => (case v6 of
   (Recordtypepmachine (v5, v4, v3, v2, v1)) => v1));

val precparse1 = (fn v37 => (fn v38 => (case v38 of
   (v36, v35) => (case v35 of
   [] => (case v36 of
   [] => (NONE)
 | (v13 :: v12) => (case v12 of
   [] => (NONE)
 | (v11 :: v10) => (case v10 of
   [] => (NONE)
 | (v9 :: v8) => (case v9 of
   (Inl v1) => (NONE)
 | (Inr v7) => (case v11 of
   (Inl v5) => (case v13 of
   (Inl v2) => (NONE)
 | (Inr v4) => ((CML_Option.map (fn v3 => (((Inr v3) :: v8), []))) ((((recordtypepmachineseldefreduce v37) v7) v5) v4)))
 | (Inr v6) => (NONE))))))
 | (v34 :: v33) => (if ((recordtypepmachineseldefisop v37) v34)
 then (case v36 of
   [] => (NONE)
 | (v27 :: v26) => (case v27 of
   (Inl v14) => (NONE)
 | (Inr v25) => (case v26 of
   [] => (SOME (((Inl v34) :: ((Inr v25) :: [])), v33))
 | (v24 :: v23) => (case v24 of
   (Inl v21) => (case v23 of
   [] => (NONE)
 | (v20 :: v19) => (case v20 of
   (Inl v15) => (NONE)
 | (Inr v18) => (case ((recordtypepmachineseldefrules v37) (v21, v34)) of
   (NONE) => (NONE)
 | (SOME v17) => (case v17 of
   (Reduce) => ((CML_Option.map (fn v16 => (((Inr v16) :: v19), (v34 :: v33)))) ((((recordtypepmachineseldefreduce v37) v18) v21) v25))
 | (Shift_1) => (SOME (((Inl v34) :: v36), v33))))))
 | (Inr v22) => (NONE)))))
 else (case v36 of
   [] => (SOME (((Inr ((recordtypepmachineseldeflift v37) v34)) :: []), v33))
 | (v32 :: v31) => (case v32 of
   (Inl v28) => (SOME (((Inr ((recordtypepmachineseldeflift v37) v34)) :: v36), v33))
 | (Inr v30) => ((CML_Option.map (fn v29 => (((Inr v29) :: v31), v33))) (((recordtypepmachineseldefmkapp v37) v30) ((recordtypepmachineseldeflift v37) v34))))))))));

val outr = (fn v => (case v of
   (Inl v1) => (raise (Bind))
 | (Inr v2) => v2));

fun precparse v6 = (fn v7 => (case v7 of
   (v5, v4) => (if (isfinal (v5, v4))
 then (SOME (outr (CML_List.hd v5)))
 else (case ((precparse1 v6) (v5, v4)) of
   (NONE) => (NONE)
 | (SOME v3) => (case v3 of
   (v2, v1) => ((precparse v6) (v2, v1)))))));

datatype cst_to_ast_associativity = Nonassoc | Right | Left;

val tokprec = (fn v1 => (if (v1 = (#"!" :: (#"!" :: [])))
 then (SOME (10, (Left)))
 else (if (v1 = (#"." :: []))
 then (SOME (9, (Right)))
 else (if (v1 = (#"^" :: []))
 then (SOME (8, (Right)))
 else (if (v1 = (#"^" :: (#"^" :: [])))
 then (SOME (8, (Right)))
 else (if (v1 = (#"*" :: (#"*" :: [])))
 then (SOME (8, (Right)))
 else (if (v1 = (#"*" :: []))
 then (SOME (7, (Left)))
 else (if (v1 = (#"/" :: []))
 then (SOME (7, (Left)))
 else (if (v1 = (#"m" :: (#"o" :: (#"d" :: []))))
 then (SOME (7, (Left)))
 else (if (v1 = (#"d" :: (#"i" :: (#"v" :: []))))
 then (SOME (7, (Left)))
 else (if (v1 = (#"q" :: (#"u" :: (#"o" :: (#"t" :: [])))))
 then (SOME (7, (Left)))
 else (if (v1 = (#"r" :: (#"e" :: (#"m" :: []))))
 then (SOME (7, (Left)))
 else (if (v1 = (#"+" :: []))
 then (SOME (6, (Left)))
 else (if (v1 = (#"-" :: []))
 then (SOME (6, (Left)))
 else (if (v1 = (#":" :: []))
 then (SOME (5, (Right)))
 else (if (v1 = (#"+" :: (#"+" :: [])))
 then (SOME (5, (Right)))
 else (if (v1 = (#"=" :: (#"=" :: [])))
 then (SOME (4, (Nonassoc)))
 else (if (v1 = (#"e" :: (#"l" :: (#"e" :: (#"m" :: [])))))
 then (SOME (4, (Nonassoc)))
 else (if (v1 = (#"n" :: (#"o" :: (#"t" :: (#"E" :: (#"l" :: (#"e" :: (#"m" :: []))))))))
 then (SOME (4, (Nonassoc)))
 else (if (v1 = (#"/" :: (#"=" :: [])))
 then (SOME (4, (Nonassoc)))
 else (if (v1 = (#"<" :: []))
 then (SOME (4, (Nonassoc)))
 else (if (v1 = (#"<" :: (#"=" :: [])))
 then (SOME (4, (Nonassoc)))
 else (if (v1 = (#">" :: []))
 then (SOME (4, (Nonassoc)))
 else (if (v1 = (#">" :: (#"=" :: [])))
 then (SOME (4, (Nonassoc)))
 else (if (v1 = (#"&" :: (#"&" :: [])))
 then (SOME (3, (Right)))
 else (if (v1 = (#"|" :: (#"|" :: [])))
 then (SOME (2, (Right)))
 else (if (v1 = (#">" :: (#">" :: [])))
 then (SOME (1, (Left)))
 else (if (v1 = (#">" :: (#">" :: (#"=" :: []))))
 then (SOME (1, (Left)))
 else (if (v1 = (#"$" :: []))
 then (SOME (0, (Right)))
 else (if (v1 = (#"s" :: (#"e" :: (#"q" :: []))))
 then (SOME (0, (Right)))
 else (if (v1 = (#"$" :: (#"!" :: [])))
 then (SOME (0, (Right)))
 else (SOME (9, (Left))))))))))))))))))))))))))))))))));

val tok_action = (fn v13 => (case v13 of
   (v12, v11) => (case v12 of
   (Inl v9) => (case v11 of
   (Inl v7) => (case (tokprec v9) of
   (NONE) => (NONE)
 | (SOME v6) => (case v6 of
   (v5, v4) => (case (tokprec v7) of
   (NONE) => (NONE)
 | (SOME v3) => (case v3 of
   (v2, v1) => (if (v2 < v5)
 then (SOME (Reduce))
 else (if (v5 < v2)
 then (SOME (Shift_1))
 else (if (if (v4 = v1)
 then (v1 = (Nonassoc))
 else (0 <= 0))
 then (NONE)
 else (if (v1 = (Left))
 then (SOME (Reduce))
 else (SOME (Shift_1))))))))))
 | (Inr v8) => (NONE))
 | (Inr v10) => (NONE))));

val mkapp = (fn v40 => (fn v39 => (case v40 of
   (Expvar v3) => (((foldl_1 (fn v2 => (fn v1 => (Expapp (v2, v1))))) v40) v39)
 | (Expcon (v5, v4)) => (Expcon (v5, (v4 @ v39)))
 | (Expop (v7, v6)) => (Expop (v7, (v6 @ v39)))
 | (Exptup v10) => (((foldl_1 (fn v9 => (fn v8 => (Expapp (v9, v8))))) v40) v39)
 | (Expapp (v14, v13)) => (((foldl_1 (fn v12 => (fn v11 => (Expapp (v12, v11))))) v40) v39)
 | (Expabs (v18, v17)) => (((foldl_1 (fn v16 => (fn v15 => (Expapp (v16, v15))))) v40) v39)
 | (Expif (v23, v22, v21)) => (((foldl_1 (fn v20 => (fn v19 => (Expapp (v20, v19))))) v40) v39)
 | (Explit v26) => (((foldl_1 (fn v25 => (fn v24 => (Expapp (v25, v24))))) v40) v39)
 | (Explet (v30, v29)) => (((foldl_1 (fn v28 => (fn v27 => (Expapp (v28, v27))))) v40) v39)
 | (Expdo (v34, v33)) => (((foldl_1 (fn v32 => (fn v31 => (Expapp (v32, v31))))) v40) v39)
 | (Expcase (v38, v37)) => (((foldl_1 (fn v36 => (fn v35 => (Expapp (v36, v35))))) v40) v39))));

val str_outl = (fn v3 => (case v3 of
   (Inl v1) => v1
 | (Inr v2) => []));

val ast_outr = (fn v3 => (case v3 of
   (Inl v1) => (Exptup [])
 | (Inr v2) => v2));

val isl = (fn v3 => (case v3 of
   (Inl v1) => (0 <= 0)
 | (Inr v2) => (0 < 0)));

val handleprecs = (fn v6 => ((precparse (Recordtypepmachine (tok_action, (fn v3 => (fn v2 => (fn v1 => (SOME ((mkapp (mksym (str_outl v2))) (v3 :: (v1 :: []))))))), ast_outr, isl, (fn v5 => (fn v4 => (SOME (Expapp (v5, v4)))))))) ([], v6)));

fun opt_mmap v5 = (fn v6 => (case v6 of
   [] => (SOME [])
 | (v4 :: v3) => (case (v5 v4) of
   (NONE) => (NONE)
 | (SOME v2) => (case ((opt_mmap v5) v3) of
   (NONE) => (NONE)
 | (SOME v1) => (SOME (v2 :: v1))))));

fun exp_to_pat v25 = (case v25 of
   (Expvar v1) => (if (v1 = (#"_" :: []))
 then (SOME (Patuscore))
 else (SOME (Patvar v1)))
 | (Expcon (v5, v4)) => ((CML_Option.map (fn v2 => (Patapp (v5, v2)))) ((opt_mmap id) ((CML_List.map (fn v3 => (exp_to_pat v3))) v4)))
 | (Expop (v7, v6)) => (NONE)
 | (Exptup v10) => ((CML_Option.map (fn v8 => (Pattup v8))) ((opt_mmap id) ((CML_List.map (fn v9 => (exp_to_pat v9))) v10)))
 | (Expapp (v12, v11)) => (NONE)
 | (Expabs (v14, v13)) => (NONE)
 | (Expif (v17, v16, v15)) => (NONE)
 | (Explit v18) => (SOME (Patlit v18))
 | (Explet (v20, v19)) => (NONE)
 | (Expdo (v22, v21)) => (NONE)
 | (Expcase (v24, v23)) => (NONE));

fun strip_comb v22 = (case v22 of
   (Expvar v1) => ((Expvar v1), [])
 | (Expcon (v3, v2)) => ((Expcon (v3, v2)), [])
 | (Expop (v5, v4)) => ((Expop (v5, v4)), [])
 | (Exptup v6) => ((Exptup v6), [])
 | (Expapp (v9, v8)) => (((CML_Pair.map id) (fn v7 => (v7 @ (v8 :: [])))) (strip_comb v9))
 | (Expabs (v11, v10)) => ((Expabs (v11, v10)), [])
 | (Expif (v14, v13, v12)) => ((Expif (v14, v13, v12)), [])
 | (Explit v15) => ((Explit v15), [])
 | (Explet (v17, v16)) => ((Explet (v17, v16)), [])
 | (Expdo (v19, v18)) => ((Expdo (v19, v18)), [])
 | (Expcase (v21, v20)) => ((Expcase (v21, v20)), []));

datatype cst_to_ast_resolve_decl = Resolve_declfun of (char) list * (pureAST_patAST) list | Resolve_declpattern of pureAST_patAST;

val destintt = (fn v15 => (case v15 of
   (Whitespacet v1) => (NONE)
 | (Newlinet) => (NONE)
 | (Lexerrort) => (NONE)
 | (Hasht) => (NONE)
 | (Lpart) => (NONE)
 | (Rpart) => (NONE)
 | (Start) => (NONE)
 | (Commat) => (NONE)
 | (Arrowt) => (NONE)
 | (Dotst) => (NONE)
 | (Colont) => (NONE)
 | (Sealt) => (NONE)
 | (Semicolont) => (NONE)
 | (Equalst) => (NONE)
 | (Darrowt) => (NONE)
 | (Lbrackt) => (NONE)
 | (Rbrackt) => (NONE)
 | (Underbart) => (NONE)
 | (Lbracet) => (NONE)
 | (Bart) => (NONE)
 | (Rbracet) => (NONE)
 | (Andt) => (NONE)
 | (Andalsot) => (NONE)
 | (Ast) => (NONE)
 | (Caset) => (NONE)
 | (Datatypet) => (NONE)
 | (Elset) => (NONE)
 | (Endt) => (NONE)
 | (Eqtypet) => (NONE)
 | (Exceptiont) => (NONE)
 | (Fnt) => (NONE)
 | (Funt) => (NONE)
 | (Handlet) => (NONE)
 | (Ift) => (NONE)
 | (Int_1) => (NONE)
 | (Includet) => (NONE)
 | (Lett) => (NONE)
 | (Localt) => (NONE)
 | (Oft) => (NONE)
 | (Opt_1) => (NONE)
 | (Opent) => (NONE)
 | (Orelset) => (NONE)
 | (Raiset) => (NONE)
 | (Rect) => (NONE)
 | (Sharingt) => (NONE)
 | (Sigt) => (NONE)
 | (Signaturet) => (NONE)
 | (Structt) => (NONE)
 | (Structuret) => (NONE)
 | (Thent) => (NONE)
 | (Typet) => (NONE)
 | (Valt) => (NONE)
 | (Wheret) => (NONE)
 | (Whilet) => (NONE)
 | (Witht) => (NONE)
 | (Withtypet) => (NONE)
 | (Intt v2) => (SOME v2)
 | (Hexintt v3) => (NONE)
 | (Wordt v4) => (NONE)
 | (Realt v5) => (NONE)
 | (Stringt v6) => (NONE)
 | (Chart v7) => (NONE)
 | (Tyvart v8) => (NONE)
 | (Alphat v9) => (NONE)
 | (Symbolt v10) => (NONE)
 | (Longidt (v12, v11)) => (NONE)
 | (Ffit v13) => (NONE)
 | (Replidt v14) => (NONE)));

val deststringt = (fn v15 => (case v15 of
   (Whitespacet v1) => (NONE)
 | (Newlinet) => (NONE)
 | (Lexerrort) => (NONE)
 | (Hasht) => (NONE)
 | (Lpart) => (NONE)
 | (Rpart) => (NONE)
 | (Start) => (NONE)
 | (Commat) => (NONE)
 | (Arrowt) => (NONE)
 | (Dotst) => (NONE)
 | (Colont) => (NONE)
 | (Sealt) => (NONE)
 | (Semicolont) => (NONE)
 | (Equalst) => (NONE)
 | (Darrowt) => (NONE)
 | (Lbrackt) => (NONE)
 | (Rbrackt) => (NONE)
 | (Underbart) => (NONE)
 | (Lbracet) => (NONE)
 | (Bart) => (NONE)
 | (Rbracet) => (NONE)
 | (Andt) => (NONE)
 | (Andalsot) => (NONE)
 | (Ast) => (NONE)
 | (Caset) => (NONE)
 | (Datatypet) => (NONE)
 | (Elset) => (NONE)
 | (Endt) => (NONE)
 | (Eqtypet) => (NONE)
 | (Exceptiont) => (NONE)
 | (Fnt) => (NONE)
 | (Funt) => (NONE)
 | (Handlet) => (NONE)
 | (Ift) => (NONE)
 | (Int_1) => (NONE)
 | (Includet) => (NONE)
 | (Lett) => (NONE)
 | (Localt) => (NONE)
 | (Oft) => (NONE)
 | (Opt_1) => (NONE)
 | (Opent) => (NONE)
 | (Orelset) => (NONE)
 | (Raiset) => (NONE)
 | (Rect) => (NONE)
 | (Sharingt) => (NONE)
 | (Sigt) => (NONE)
 | (Signaturet) => (NONE)
 | (Structt) => (NONE)
 | (Structuret) => (NONE)
 | (Thent) => (NONE)
 | (Typet) => (NONE)
 | (Valt) => (NONE)
 | (Wheret) => (NONE)
 | (Whilet) => (NONE)
 | (Witht) => (NONE)
 | (Withtypet) => (NONE)
 | (Intt v2) => (NONE)
 | (Hexintt v3) => (NONE)
 | (Wordt v4) => (NONE)
 | (Realt v5) => (NONE)
 | (Stringt v6) => (SOME v6)
 | (Chart v7) => (NONE)
 | (Tyvart v8) => (NONE)
 | (Alphat v9) => (NONE)
 | (Symbolt v10) => (NONE)
 | (Longidt (v12, v11)) => (NONE)
 | (Ffit v13) => (NONE)
 | (Replidt v14) => (NONE)));

val astlit = (fn v14 => (case v14 of
   (Lf v1) => (NONE)
 | (Nd (v13, v12)) => (if (((fst v13) = (Inl (Nlit))) = (0 < 0))
 then (NONE)
 else (case v12 of
   [] => (NONE)
 | (v11 :: v10) => (case v10 of
   [] => ((option_choice ((CML_Option.map (fn v2 => (Litint v2))) (case (case (destlf v11) of
   (NONE) => (NONE)
 | (SOME v3) => (desttok v3)) of
   (NONE) => (NONE)
 | (SOME v4) => (destintt v4)))) ((CML_Option.map (fn v5 => (Litstring v5))) (case (case (destlf v11) of
   (NONE) => (NONE)
 | (SOME v6) => (desttok v6)) of
   (NONE) => (NONE)
 | (SOME v7) => (deststringt v7))))
 | (v9 :: v8) => (NONE))))));

val mkffisym = (fn v1 => (if (v1 = (#"_" :: (#"_" :: (#"L" :: (#"e" :: (#"n" :: []))))))
 then (Len)
 else (if (v1 = (#"_" :: (#"_" :: (#"E" :: (#"l" :: (#"e" :: (#"m" :: [])))))))
 then (Elem)
 else (if (v1 = (#"_" :: (#"_" :: (#"C" :: (#"o" :: (#"n" :: (#"c" :: (#"a" :: (#"t" :: [])))))))))
 then (Concat)
 else (if (v1 = (#"_" :: (#"_" :: (#"I" :: (#"m" :: (#"p" :: (#"l" :: (#"o" :: (#"d" :: (#"e" :: []))))))))))
 then (Implode)
 else (if (v1 = (#"_" :: (#"_" :: (#"S" :: (#"u" :: (#"b" :: (#"s" :: (#"t" :: (#"r" :: (#"i" :: (#"n" :: (#"g" :: []))))))))))))
 then (Substring)
 else (if (v1 = (#"_" :: (#"_" :: (#"S" :: (#"t" :: (#"r" :: (#"E" :: (#"q" :: []))))))))
 then (Streq)
 else (if (v1 = (#"_" :: (#"_" :: (#"S" :: (#"t" :: (#"r" :: (#"L" :: (#"t" :: []))))))))
 then (Strlt)
 else (if (v1 = (#"_" :: (#"_" :: (#"S" :: (#"t" :: (#"r" :: (#"L" :: (#"e" :: (#"q" :: [])))))))))
 then (Strleq)
 else (if (v1 = (#"_" :: (#"_" :: (#"S" :: (#"t" :: (#"r" :: (#"G" :: (#"t" :: []))))))))
 then (Strgt)
 else (if (v1 = (#"_" :: (#"_" :: (#"S" :: (#"t" :: (#"r" :: (#"G" :: (#"e" :: (#"q" :: [])))))))))
 then (Strgeq)
 else (Message v1))))))))))));

val dostmt_to_exp = (fn v5 => (case v5 of
   (Expdostmtexp v1) => (SOME v1)
 | (Expdostmtbind (v3, v2)) => (NONE)
 | (Expdostmtlet v4) => (NONE)));

val astalpha = (fn v3 => (case (case (destlf v3) of
   (NONE) => (NONE)
 | (SOME v1) => (desttok v1)) of
   (NONE) => (NONE)
 | (SOME v2) => (destalphat v2)));

val astpat = (fn v11 => (fn v10 => (case v10 of
   (Lf v1) => (NONE)
 | (Nd (v9, v8)) => (if (((Inl v11) = (fst v9)) = (0 < 0))
 then (NONE)
 else (if (v11 = (Napat))
 then (case v8 of
   [] => (NONE)
 | (v7 :: v6) => (case v6 of
   [] => ((option_choice ((option_choice (case (astalpha v7) of
   (NONE) => (NONE)
 | (SOME v2) => (SOME (Patvar v2)))) ((CML_Option.map (fn v3 => (Patlit v3))) (astlit v7)))) (if ((tokcheck v7) (Underbart))
 then (SOME (Patuscore))
 else (NONE)))
 | (v5 :: v4) => (NONE)))
 else (NONE))))));

val dest_explet = (fn v21 => (case v21 of
   (Expvar v1) => (NONE)
 | (Expcon (v3, v2)) => (NONE)
 | (Expop (v5, v4)) => (NONE)
 | (Exptup v6) => (NONE)
 | (Expapp (v8, v7)) => (NONE)
 | (Expabs (v10, v9)) => (NONE)
 | (Expif (v13, v12, v11)) => (NONE)
 | (Explit v14) => (NONE)
 | (Explet (v16, v15)) => (SOME (v16, v15))
 | (Expdo (v18, v17)) => (NONE)
 | (Expcase (v20, v19)) => (NONE)));

val astop = (fn v16 => (case v16 of
   (Lf v1) => (NONE)
 | (Nd (v15, v14)) => (if (((fst v15) = (Inl (Nop))) = (0 < 0))
 then (NONE)
 else (case v14 of
   [] => (NONE)
 | (v13 :: v12) => (case v12 of
   [] => (case (case (destlf v13) of
   (NONE) => (NONE)
 | (SOME v2) => (desttok v2)) of
   (NONE) => (NONE)
 | (SOME v3) => ((option_choice (destsymbolt v3)) (if (v3 = (Start))
 then (SOME (#"*" :: []))
 else (if (v3 = (Colont))
 then (SOME (#":" :: []))
 else (NONE)))))
 | (v11 :: v10) => (case v10 of
   [] => (NONE)
 | (v9 :: v8) => (case v8 of
   [] => (if (((tokcheck v13) (Symbolt (#"`" :: []))) andalso ((tokcheck v9) (Symbolt (#"`" :: []))))
 then (case (case (destlf v11) of
   (NONE) => (NONE)
 | (SOME v4) => (desttok v4)) of
   (NONE) => (NONE)
 | (SOME v5) => (destalphat v5))
 else (NONE))
 | (v7 :: v6) => (NONE))))))));

val resolve_decl = (fn v30 => (case (exp_to_pat v30) of
   (NONE) => (case (strip_comb v30) of
   (v23, v22) => (case v23 of
   (Expvar v2) => ((CML_Option.map (fn v1 => (Resolve_declfun (v2, v1)))) ((opt_mmap exp_to_pat) v22))
 | (Expcon (v4, v3)) => (NONE)
 | (Expop (v6, v5)) => (NONE)
 | (Exptup v7) => (NONE)
 | (Expapp (v9, v8)) => (NONE)
 | (Expabs (v11, v10)) => (NONE)
 | (Expif (v14, v13, v12)) => (NONE)
 | (Explit v15) => (NONE)
 | (Explet (v17, v16)) => (NONE)
 | (Expdo (v19, v18)) => (NONE)
 | (Expcase (v21, v20)) => (NONE)))
 | (SOME v29) => (case v29 of
   (Patvar v24) => (SOME (Resolve_declfun (v24, [])))
 | (Patapp (v26, v25)) => (SOME (Resolve_declpattern (Patapp (v26, v25))))
 | (Pattup v27) => (SOME (Resolve_declpattern (Pattup v27)))
 | (Patlit v28) => (SOME (Resolve_declpattern (Patlit v28)))
 | (Patuscore) => (SOME (Resolve_declpattern (Patuscore))))));

fun astexp v88 = (fn v89 => (case v89 of
   (Lf v1) => (NONE)
 | (Nd (v87, v86)) => (if (((Inl v88) = (fst v87)) = (0 < 0))
 then (NONE)
 else (if (v88 = (Naexp))
 then (case v86 of
   [] => (NONE)
 | (v19 :: v18) => (case v18 of
   [] => ((option_choice ((option_choice ((option_choice (case (case (case (destlf v19) of
   (NONE) => (NONE)
 | (SOME v2) => (desttok v2)) of
   (NONE) => (NONE)
 | (SOME v3) => (destalphat v3)) of
   (NONE) => (NONE)
 | (SOME v4) => (SOME (mksym v4)))) ((CML_Option.map (fn v5 => (Explit v5))) (astlit v19)))) (if ((tokcheck v19) (Underbart))
 then (SOME (Expvar (#"_" :: [])))
 else (NONE)))) (case (case (case (destlf v19) of
   (NONE) => (NONE)
 | (SOME v6) => (desttok v6)) of
   (NONE) => (NONE)
 | (SOME v7) => (destffit v7)) of
   (NONE) => (NONE)
 | (SOME v8) => (SOME (Expop ((mkffisym v8), [])))))
 | (v17 :: v16) => (case v16 of
   [] => ((option_choice (if (((tokcheck v19) (Lpart)) andalso ((tokcheck v17) (Rpart)))
 then (SOME (Exptup []))
 else (NONE))) (if (((tokcheck v19) (Lbrackt)) andalso ((tokcheck v17) (Rbrackt)))
 then (SOME (Expcon ((#"[" :: (#"]" :: [])), [])))
 else (NONE)))
 | (v15 :: v14) => (case ((option_choice (if ((tokcheck v19) (Lpart))
 then (SOME (Rpart))
 else (NONE))) (if ((tokcheck v19) (Lbrackt))
 then (SOME (Rbrackt))
 else (NONE))) of
   (NONE) => (NONE)
 | (SOME v13) => (case ((astexp (Nexp)) v17) of
   (NONE) => (NONE)
 | (SOME v12) => (case ((astsepexp v13) (v15 :: v14)) of
   (NONE) => (NONE)
 | (SOME v11) => (if (v13 = (Rpart))
 then (if (CML_List.null v11)
 then (SOME v12)
 else (SOME (Exptup (v12 :: v11))))
 else (SOME (((foldr_1 (fn v10 => (fn v9 => (Expcon ((#":" :: (#":" :: [])), (v10 :: (v9 :: []))))))) (Expcon ((#"[" :: (#"]" :: [])), []))) (v12 :: v11))))))))))
 else (if (v88 = (Nexp))
 then (case v86 of
   [] => (NONE)
 | (v60 :: v59) => (case v59 of
   [] => ((astexp (Niexp)) v60)
 | (v58 :: v57) => (case v57 of
   [] => (if ((tokcheck v60) (Alphat (#"d" :: (#"o" :: []))))
 then (case (astdoblock v58) of
   (NONE) => (NONE)
 | (SOME v22) => (((optlast (fn v21 => (fn v20 => (Expdo (v21, v20))))) dostmt_to_exp) v22))
 else (NONE))
 | (v56 :: v55) => ((option_choice ((option_choice ((option_choice (if ((((tokcheck v60) (Ift)) andalso ((CML_List.length (v58 :: (v56 :: v55))) = 5)) andalso (((list_rel (fn v24 => (fn v23 => (v24 v23)))) ((const (0 <= 0)) :: (((flip tokcheck) (Thent)) :: ((const (0 <= 0)) :: (((flip tokcheck) (Elset)) :: ((const (0 <= 0)) :: [])))))) (v58 :: (v56 :: v55))))
 then (case (case ((oel 0) (v58 :: (v56 :: v55))) of
   (NONE) => (NONE)
 | (SOME v25) => ((astexp (Nexp)) v25)) of
   (NONE) => (NONE)
 | (SOME v30) => (case (case ((oel 2) (v58 :: (v56 :: v55))) of
   (NONE) => (NONE)
 | (SOME v26) => ((astexp (Nexp)) v26)) of
   (NONE) => (NONE)
 | (SOME v29) => (case (case ((oel 4) (v58 :: (v56 :: v55))) of
   (NONE) => (NONE)
 | (SOME v27) => ((astexp (Nexp)) v27)) of
   (NONE) => (NONE)
 | (SOME v28) => (SOME (Expif (v30, v29, v28))))))
 else (NONE))) (if ((tokcheck v60) (Symbolt (#"\\" :: [])))
 then (case ((grab' (((astpat (Napat)) v58) :: (((astpat (Napat)) v56) :: ((CML_List.map (astpat (Napat))) v55)))) (v58 :: (v56 :: v55))) of
   (NONE) => (NONE)
 | (SOME v39) => (case v39 of
   (v38, v37) => (if (((list_rel (fn v32 => (fn v31 => (v32 v31)))) (((flip tokcheck) (Symbolt (#"-" :: (#">" :: [])))) :: ((const (0 <= 0)) :: []))) v37)
 then (case (case ((oel 1) v37) of
   (NONE) => (NONE)
 | (SOME v33) => ((astexp (Nexp)) v33)) of
   (NONE) => (NONE)
 | (SOME v36) => (SOME (((foldr_1 (fn v35 => (fn v34 => (Expabs (v35, v34))))) v36) v38)))
 else (NONE))))
 else (NONE)))) (if ((((tokcheck v60) (Lett)) andalso ((CML_List.length (v58 :: (v56 :: v55))) = 3)) andalso (((list_rel (fn v41 => (fn v40 => (v41 v40)))) ((const (0 <= 0)) :: (((flip tokcheck) (Int_1)) :: ((const (0 <= 0)) :: [])))) (v58 :: (v56 :: v55))))
 then (case ((oel 0) (v58 :: (v56 :: v55))) of
   (NONE) => (NONE)
 | (SOME v48) => (case ((astexp (Neqbindseq)) v48) of
   (NONE) => (NONE)
 | (SOME v47) => (case (dest_explet v47) of
   (NONE) => (NONE)
 | (SOME v46) => (case v46 of
   (v45, v44) => (case (case ((oel 2) (v58 :: (v56 :: v55))) of
   (NONE) => (NONE)
 | (SOME v42) => ((astexp (Nexp)) v42)) of
   (NONE) => (NONE)
 | (SOME v43) => (SOME (Explet (v45, v43))))))))
 else (NONE)))) (if (((tokcheck v60) (Caset)) andalso (((list_rel (fn v50 => (fn v49 => (v50 v49)))) ((const (0 <= 0)) :: (((flip tokcheck) (Oft)) :: ((const (0 <= 0)) :: [])))) (v58 :: (v56 :: v55))))
 then (case ((oel 0) (v58 :: (v56 :: v55))) of
   (NONE) => (NONE)
 | (SOME v54) => (case ((astexp (Nexp)) v54) of
   (NONE) => (NONE)
 | (SOME v53) => (case ((oel 2) (v58 :: (v56 :: v55))) of
   (NONE) => (NONE)
 | (SOME v52) => (case (astpatalts v52) of
   (NONE) => (NONE)
 | (SOME v51) => (SOME (Expcase (v53, v51)))))))
 else (NONE))))))
 else (if (v88 = (Niexp))
 then (case v86 of
   [] => (NONE)
 | (v65 :: v64) => (case ((astexp (Nfexp)) v65) of
   (NONE) => (NONE)
 | (SOME v63) => (case ((grabpairs' ((Inr v63) :: [])) (CML_List.zip (((CML_List.map (fn v61 => ((astexp (Nfexp2)) v61))) v64), ((CML_List.map astop) v64)))) of
   (NONE) => (NONE)
 | (SOME v62) => (handleprecs v62))))
 else (if (v88 = (Nfexp2))
 then (case v86 of
   [] => (NONE)
 | (v69 :: v68) => (case v68 of
   [] => ((option_choice ((astexp (Nexp)) v69)) ((astexp (Nfexp)) v69))
 | (v67 :: v66) => (NONE)))
 else (if (v88 = (Nfexp))
 then (case v86 of
   [] => (NONE)
 | (v76 :: v75) => (case ((astexp (Naexp)) v76) of
   (NONE) => (NONE)
 | (SOME v74) => (case ((grab' ((CML_List.map (fn v70 => ((astexp (Naexp)) v70))) v75)) v75) of
   (NONE) => (NONE)
 | (SOME v73) => (case v73 of
   (v72, v71) => (if (CML_List.null v71)
 then (SOME ((mkapp v74) v72))
 else (NONE))))))
 else (if (v88 = (Neqbindseq))
 then (case v86 of
   [] => (SOME (Explet ([], (Expvar []))))
 | (v85 :: v84) => ((option_choice (if ((tokcheck v85) (Lbracet))
 then (let val v80 = (((grabsepby' (Semicolont)) ((CML_List.map (fn v81 => (astexpdec v81))) v84)) v84)
 in (case v80 of
   (v79, v78) => (case (ohd v78) of
   (NONE) => (NONE)
 | (SOME v77) => (if (((tokcheck v77) (Rbracet)) andalso ((CML_List.length v78) = 1))
 then (SOME (Explet (v79, (Expvar []))))
 else (NONE)))) end)
 else (NONE))) ((CML_Option.map (fn v82 => (Explet (v82, (Expvar []))))) ((opt_mmap id) ((CML_List.map (fn v83 => (astexpdec v83))) (v85 :: v84))))))
 else (NONE))))))))))
and astsepexp v7 = (fn v8 => (case v8 of
   [] => (NONE)
 | (v6 :: v5) => (case v5 of
   [] => (if ((tokcheck v6) v7)
 then (SOME [])
 else (NONE))
 | (v4 :: v3) => (if ((tokcheck v6) (Commat))
 then (case ((astexp (Nexp)) v4) of
   (NONE) => (NONE)
 | (SOME v2) => (case ((astsepexp v7) v3) of
   (NONE) => (NONE)
 | (SOME v1) => (SOME (v2 :: v1))))
 else (NONE)))))
and astexpdec v22 = (case v22 of
   (Lf v1) => (NONE)
 | (Nd (v21, v20)) => (if (((fst v21) = (Inl (Neqbind))) = (0 < 0))
 then (NONE)
 else (case v20 of
   [] => (NONE)
 | (v19 :: v18) => (case v18 of
   [] => (NONE)
 | (v17 :: v16) => (case v16 of
   [] => (NONE)
 | (v15 :: v14) => (case v14 of
   [] => ((option_choice (if ((tokcheck v17) (Equalst))
 then (case ((astexp (Nexp)) v19) of
   (NONE) => (NONE)
 | (SOME v7) => (case ((astexp (Nexp)) v15) of
   (NONE) => (NONE)
 | (SOME v6) => (case (resolve_decl v7) of
   (NONE) => (NONE)
 | (SOME v5) => (case v5 of
   (Resolve_declpattern v2) => (SOME (Expdecpatbind (v2, v6)))
 | (Resolve_declfun (v4, v3)) => (SOME (Expdecfunbind (v4, v3, v6)))))))
 else (NONE))) (if ((tokcheck v17) (Symbolt (#":" :: (#":" :: []))))
 then (case (case (case (destlf v19) of
   (NONE) => (NONE)
 | (SOME v8) => (desttok v8)) of
   (NONE) => (NONE)
 | (SOME v9) => (destalphat v9)) of
   (NONE) => (NONE)
 | (SOME v11) => (case ((asttype (Nty)) v15) of
   (NONE) => (NONE)
 | (SOME v10) => (SOME (Expdectysig (v11, v10)))))
 else (NONE)))
 | (v13 :: v12) => (NONE)))))))
and astdostmt v20 = (case v20 of
   (Lf v1) => (NONE)
 | (Nd (v19, v18)) => (if (((fst v19) = (Inl (Ndostmt))) = (0 < 0))
 then (NONE)
 else (case v18 of
   [] => (NONE)
 | (v17 :: v16) => (case v16 of
   [] => ((CML_Option.map (fn v2 => (Expdostmtexp v2))) ((astexp (Nexp)) v17))
 | (v15 :: v14) => (case v14 of
   [] => (if ((tokcheck v17) (Lett))
 then (case ((astexp (Neqbindseq)) v15) of
   (NONE) => (NONE)
 | (SOME v6) => (case (dest_explet v6) of
   (NONE) => (NONE)
 | (SOME v5) => (case v5 of
   (v4, v3) => (SOME (Expdostmtlet v4)))))
 else (NONE))
 | (v13 :: v12) => (case v12 of
   [] => (if ((tokcheck v15) (Symbolt (#"<" :: (#"-" :: []))))
 then (case ((astexp (Nexp)) v17) of
   (NONE) => (NONE)
 | (SOME v9) => (case (exp_to_pat v9) of
   (NONE) => (NONE)
 | (SOME v8) => (case ((astexp (Nexp)) v13) of
   (NONE) => (NONE)
 | (SOME v7) => (SOME (Expdostmtbind (v8, v7))))))
 else (NONE))
 | (v11 :: v10) => (NONE)))))))
and astdoblock v5 = (case v5 of
   (Lf v1) => (NONE)
 | (Nd (v4, v3)) => (if (((fst v4) = (Inl (Ndoblock))) = (0 < 0))
 then (NONE)
 else ((opt_mmap id) ((CML_List.map (fn v2 => (astdostmt v2))) v3))))
and astpatalts v5 = (case v5 of
   (Lf v1) => (NONE)
 | (Nd (v4, v3)) => (if (((fst v4) = (Inl (Npatalts))) = (0 < 0))
 then (NONE)
 else ((opt_mmap id) ((CML_List.map (fn v2 => (astpatalt v2))) v3))))
and astpatalt v15 = (case v15 of
   (Lf v1) => (NONE)
 | (Nd (v14, v13)) => (if (((fst v14) = (Inl (Npatalt))) = (0 < 0))
 then (NONE)
 else (case v13 of
   [] => (NONE)
 | (v12 :: v11) => (case v11 of
   [] => (NONE)
 | (v10 :: v9) => (case v9 of
   [] => (NONE)
 | (v8 :: v7) => (case v7 of
   [] => (if ((tokcheck v10) (Symbolt (#"-" :: (#">" :: []))))
 then (case ((astexp (Nexp)) v12) of
   (NONE) => (NONE)
 | (SOME v4) => (case (exp_to_pat v4) of
   (NONE) => (NONE)
 | (SOME v3) => (case ((astexp (Nexp)) v8) of
   (NONE) => (NONE)
 | (SOME v2) => (SOME (v3, v2)))))
 else (NONE))
 | (v6 :: v5) => (NONE)))))));

datatype pureAST_declAST = Declpatbind of pureAST_patAST * pureAST_expAST | Declfunbind of (char) list * (pureAST_patAST) list * pureAST_expAST | Decldata of (char) list * ((char) list) list * (((char) list * (pureAST_tyAST) list)) list | Decltysig of (char) list * pureAST_tyAST;

val dest_expvar = (fn v21 => (case v21 of
   (Expvar v1) => (SOME v1)
 | (Expcon (v3, v2)) => (NONE)
 | (Expop (v5, v4)) => (NONE)
 | (Exptup v6) => (NONE)
 | (Expapp (v8, v7)) => (NONE)
 | (Expabs (v10, v9)) => (NONE)
 | (Expif (v13, v12, v11)) => (NONE)
 | (Explit v14) => (NONE)
 | (Explet (v16, v15)) => (NONE)
 | (Expdo (v18, v17)) => (NONE)
 | (Expcase (v20, v19)) => (NONE)));

val astfunpatbindf = (fn v9 => ((option_choice (case (exp_to_pat v9) of
   (NONE) => (NONE)
 | (SOME v2) => (SOME (fn v1 => (Declpatbind (v2, v1)))))) (let val v8 = (strip_comb v9)
 in (case v8 of
   (v7, v6) => (case (dest_expvar v7) of
   (NONE) => (NONE)
 | (SOME v5) => (case ((opt_mmap exp_to_pat) v6) of
   (NONE) => (NONE)
 | (SOME v4) => (SOME (fn v3 => (Declfunbind (v5, v4, v3))))))) end)));

val astvalbinding = (fn v15 => (case v15 of
   (Lf v1) => (NONE)
 | (Nd (v14, v13)) => (if (((fst v14) = (Inl (Nvalbinding))) = (0 < 0))
 then (NONE)
 else (case v13 of
   [] => (NONE)
 | (v12 :: v11) => (case v11 of
   [] => (NONE)
 | (v10 :: v9) => (case v9 of
   [] => (NONE)
 | (v8 :: v7) => (case v7 of
   [] => (if ((tokcheck v10) (Equalst))
 then (case ((astexp (Nexp)) v12) of
   (NONE) => (NONE)
 | (SOME v4) => (case (astfunpatbindf v4) of
   (NONE) => (NONE)
 | (SOME v3) => (case ((astexp (Nexp)) v8) of
   (NONE) => (NONE)
 | (SOME v2) => (SOME (v3 v2)))))
 else (NONE))
 | (v6 :: v5) => (NONE))))))));

val astlcname = (fn v2 => (case (astalpha v2) of
   (NONE) => (NONE)
 | (SOME v1) => (if (lcname v1)
 then (SOME v1)
 else (NONE))));

val astcapname = (fn v2 => (case (astalpha v2) of
   (NONE) => (NONE)
 | (SOME v1) => (if (capname v1)
 then (SOME v1)
 else (NONE))));

val asttycondecl = (fn v10 => (case v10 of
   (Lf v1) => (NONE)
 | (Nd (v9, v8)) => (if (((fst v9) = (Inl (Ntycondecl))) = (0 < 0))
 then (NONE)
 else (case v8 of
   [] => (NONE)
 | (v7 :: v6) => (case (astcapname v7) of
   (NONE) => (NONE)
 | (SOME v5) => (case ((grab' ((CML_List.map (asttype (Ntybase))) v6)) v6) of
   (NONE) => (NONE)
 | (SOME v4) => (case v4 of
   (v3, v2) => (if (v2 = [])
 then (SOME (v5, v3))
 else (NONE)))))))));

fun asttycons v8 = (case v8 of
   [] => (NONE)
 | (v7 :: v6) => (case v6 of
   [] => (case (asttycondecl v7) of
   (NONE) => (NONE)
 | (SOME v1) => (SOME (v1 :: [])))
 | (v5 :: v4) => (case (asttycondecl v7) of
   (NONE) => (NONE)
 | (SOME v3) => (if ((tokcheck v5) (Bart))
 then (case (asttycons v4) of
   (NONE) => (NONE)
 | (SOME v2) => (SOME (v3 :: v2)))
 else (NONE)))));

val astdecl = (fn v24 => (case v24 of
   (Lf v1) => (NONE)
 | (Nd (v23, v22)) => (if (((fst v23) = (Inl (Ndecl))) = (0 < 0))
 then (NONE)
 else (case v22 of
   [] => (NONE)
 | (v21 :: v20) => (case v20 of
   [] => (astvalbinding v21)
 | (v19 :: v18) => (case v18 of
   [] => (NONE)
 | (v17 :: v16) => (case v16 of
   [] => (if ((tokcheck v19) (Symbolt (#":" :: (#":" :: []))))
 then (case (case (case (destlf v21) of
   (NONE) => (NONE)
 | (SOME v2) => (desttok v2)) of
   (NONE) => (NONE)
 | (SOME v3) => (destalphat v3)) of
   (NONE) => (NONE)
 | (SOME v5) => (case ((asttype (Nty)) v17) of
   (NONE) => (NONE)
 | (SOME v4) => (SOME (Decltysig (v5, v4)))))
 else (NONE))
 | (v15 :: v14) => (if ((tokcheck v21) (Alphat (#"d" :: (#"a" :: (#"t" :: (#"a" :: []))))))
 then (case (case (case (destlf v19) of
   (NONE) => (NONE)
 | (SOME v6) => (desttok v6)) of
   (NONE) => (NONE)
 | (SOME v7) => (destalphat v7)) of
   (NONE) => (NONE)
 | (SOME v13) => (case ((grab' ((astlcname v17) :: ((astlcname v15) :: ((CML_List.map astlcname) v14)))) (v17 :: (v15 :: v14))) of
   (NONE) => (NONE)
 | (SOME v12) => (case v12 of
   (v11, v10) => (if (2 <= (CML_List.length v10))
 then (case ((oel 0) v10) of
   (NONE) => (NONE)
 | (SOME v9) => (if ((tokcheck v9) (Equalst))
 then (case (asttycons (CML_List.tl v10)) of
   (NONE) => (NONE)
 | (SOME v8) => (SOME (Decldata (v13, v11, v8))))
 else (NONE)))
 else (NONE)))))
 else (NONE)))))))));

val astdecls = (fn v4 => (case v4 of
   (Lf v1) => (NONE)
 | (Nd (v3, v2)) => (if (((fst v3) = (Inl (Ndecls))) = (0 < 0))
 then (NONE)
 else ((opt_mmap astdecl) v2))));

val bench_cst = (fn v24 => (case (((((((((ispeg_exec purepeg) (Nt_1 ((Inl (Ndecls)), id, (Lrok)))) v24) (Lpxge 0)) []) (NONE)) []) (Done)) (Failed)) of
   (Ev (v8, v7, v6, v5, v4, v3, v2, v1)) => (NONE)
 | (Ap (v14, v13, v12, v11, v10, v9)) => (NONE)
 | (Result v23) => (case v23 of
   (Success (v20, v19, v18, v17)) => (case v20 of
   [] => (SOME v19)
 | (v16 :: v15) => (NONE))
 | (Failure (v22, v21)) => (NONE))
 | (Looped) => (NONE)));

val pr_num = (fn v2 => ((CML_List.map (fn v1 => (if (v1 = #"~")
 then #"-"
 else v1))) (String.explode (CML_Int.toString v2))));

val qchar = (fn v1 => (if (v1 = #"\"")
 then (#"\\" :: (#"\"" :: []))
 else (if (v1 = #"\\")
 then (#"\\" :: (#"\\" :: []))
 else (if (((Char.ord v1) < 32) orelse (126 < (Char.ord v1)))
 then (((#"\\" :: []) @ (pr_num (Char.ord v1))) @ (#";" :: []))
 else (v1 :: [])))));

val qstr = (fn v1 => (((#"\"" :: []) @ (flat ((CML_List.map qchar) v1))) @ (#"\"" :: [])));

val pr_lit = (fn v3 => (case v3 of
   (Litint v1) => (((#"(" :: (#"i" :: (#"n" :: (#"t" :: (#" " :: []))))) @ (pr_num v1)) @ (#")" :: []))
 | (Litstring v2) => (((#"(" :: (#"s" :: (#"t" :: (#"r" :: (#" " :: []))))) @ (qstr v2)) @ (#")" :: []))));

fun pr_ty v5 = (case v5 of
   (Tyop (v2, v1)) => ((((#"(" :: (#"o" :: (#"p" :: (#" " :: [])))) @ (qstr v2)) @ (pr_tys v1)) @ (#")" :: []))
 | (Tyvar v3) => (((#"(" :: (#"v" :: (#"a" :: (#"r" :: (#" " :: []))))) @ (qstr v3)) @ (#")" :: []))
 | (Tytup v4) => (((#"(" :: (#"t" :: (#"u" :: (#"p" :: [])))) @ (pr_tys v4)) @ (#")" :: [])))
and pr_tys v3 = (case v3 of
   [] => []
 | (v2 :: v1) => (((#" " :: []) @ (pr_ty v2)) @ (pr_tys v1)));

fun pr_pat v6 = (case v6 of
   (Patvar v1) => (((#"(" :: (#"p" :: (#"v" :: (#"a" :: (#"r" :: (#" " :: [])))))) @ (qstr v1)) @ (#")" :: []))
 | (Patapp (v3, v2)) => ((((#"(" :: (#"p" :: (#"a" :: (#"p" :: (#"p" :: (#" " :: [])))))) @ (qstr v3)) @ (pr_pats v2)) @ (#")" :: []))
 | (Pattup v4) => (((#"(" :: (#"p" :: (#"t" :: (#"u" :: (#"p" :: []))))) @ (pr_pats v4)) @ (#")" :: []))
 | (Patlit v5) => (((#"(" :: (#"p" :: (#"l" :: (#"i" :: (#"t" :: (#" " :: [])))))) @ (pr_lit v5)) @ (#")" :: []))
 | (Patuscore) => (#"(" :: (#"w" :: (#"i" :: (#"l" :: (#"d" :: (#")" :: [])))))))
and pr_pats v3 = (case v3 of
   [] => []
 | (v2 :: v1) => (((#" " :: []) @ (pr_pat v2)) @ (pr_pats v1)));

val pr_op = (fn v3 => (case v3 of
   (Lit v1) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Add) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Sub) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Mul) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Div_1) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Mod) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Eq) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Lt) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Leq) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Gt) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Geq) => (#"o" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: [])))))
 | (Len) => (#"L" :: (#"e" :: (#"n" :: [])))
 | (Elem) => (#"E" :: (#"l" :: (#"e" :: (#"m" :: []))))
 | (Concat) => (#"C" :: (#"o" :: (#"n" :: (#"c" :: (#"a" :: (#"t" :: []))))))
 | (Implode) => (#"I" :: (#"m" :: (#"p" :: (#"l" :: (#"o" :: (#"d" :: (#"e" :: [])))))))
 | (Substring) => (#"S" :: (#"u" :: (#"b" :: (#"s" :: (#"t" :: (#"r" :: (#"i" :: (#"n" :: (#"g" :: [])))))))))
 | (Streq) => (#"S" :: (#"t" :: (#"r" :: (#"E" :: (#"q" :: [])))))
 | (Strlt) => (#"S" :: (#"t" :: (#"r" :: (#"L" :: (#"t" :: [])))))
 | (Strleq) => (#"S" :: (#"t" :: (#"r" :: (#"L" :: (#"e" :: (#"q" :: []))))))
 | (Strgt) => (#"S" :: (#"t" :: (#"r" :: (#"G" :: (#"t" :: [])))))
 | (Strgeq) => (#"S" :: (#"t" :: (#"r" :: (#"G" :: (#"e" :: (#"q" :: []))))))
 | (Message v2) => (((#"(" :: (#"m" :: (#"s" :: (#"g" :: (#" " :: []))))) @ (qstr v2)) @ (#")" :: []))));

fun pr_exp v21 = (fn v22 => (if (v21 = 0)
 then []
 else (case v22 of
   (Expvar v1) => (((#"(" :: (#"v" :: (#"a" :: (#"r" :: (#" " :: []))))) @ (qstr v1)) @ (#")" :: []))
 | (Expcon (v3, v2)) => ((((#"(" :: (#"c" :: (#"o" :: (#"n" :: (#" " :: []))))) @ (qstr v3)) @ ((pr_exps (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v2)) @ (#")" :: []))
 | (Expop (v5, v4)) => ((((#"(" :: (#"p" :: (#"r" :: (#"i" :: (#"m" :: (#" " :: [])))))) @ (pr_op v5)) @ ((pr_exps (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v4)) @ (#")" :: []))
 | (Exptup v6) => (((#"(" :: (#"t" :: (#"u" :: (#"p" :: [])))) @ ((pr_exps (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v6)) @ (#")" :: []))
 | (Expapp (v8, v7)) => (((((#"(" :: (#"a" :: (#"p" :: (#"p" :: (#" " :: []))))) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v8)) @ (#" " :: [])) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v7)) @ (#")" :: []))
 | (Expabs (v10, v9)) => (((((#"(" :: (#"a" :: (#"b" :: (#"s" :: (#" " :: []))))) @ (pr_pat v10)) @ (#" " :: [])) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v9)) @ (#")" :: []))
 | (Expif (v13, v12, v11)) => (((((((#"(" :: (#"i" :: (#"f" :: (#" " :: [])))) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v13)) @ (#" " :: [])) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v12)) @ (#" " :: [])) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v11)) @ (#")" :: []))
 | (Explit v14) => (((#"(" :: (#"l" :: (#"i" :: (#"t" :: (#" " :: []))))) @ (pr_lit v14)) @ (#")" :: []))
 | (Explet (v16, v15)) => (((((#"(" :: (#"l" :: (#"e" :: (#"t" :: (#" " :: (#"(" :: [])))))) @ ((pr_decs (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v16)) @ (#")" :: (#" " :: []))) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v15)) @ (#")" :: []))
 | (Expdo (v18, v17)) => (((((#"(" :: (#"d" :: (#"o" :: (#" " :: (#"(" :: []))))) @ ((pr_stmts (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v18)) @ (#")" :: (#" " :: []))) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v17)) @ (#")" :: []))
 | (Expcase (v20, v19)) => (((((#"(" :: (#"c" :: (#"a" :: (#"s" :: (#"e" :: (#" " :: [])))))) @ ((pr_exp (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v20)) @ (#" " :: (#"(" :: []))) @ ((pr_alts (let val k = (v21 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v19)) @ (#")" :: (#")" :: []))))))
and pr_exps v3 = (fn v4 => (if (v3 = 0)
 then []
 else (case v4 of
   [] => []
 | (v2 :: v1) => (((#" " :: []) @ ((pr_exp (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v2)) @ ((pr_exps (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v1)))))
and pr_alts v5 = (fn v6 => (if (v5 = 0)
 then []
 else (case v6 of
   [] => []
 | (v4 :: v3) => (case v4 of
   (v2, v1) => ((((((#"(" :: []) @ (pr_pat v2)) @ (#" " :: [])) @ ((pr_exp (let val k = (v5 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v1)) @ (#")" :: [])) @ ((pr_alts (let val k = (v5 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v3))))))
and pr_decs v3 = (fn v4 => (if (v3 = 0)
 then []
 else (case v4 of
   [] => []
 | (v2 :: v1) => (((pr_dec (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v2) @ ((pr_decs (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v1)))))
and pr_dec v8 = (fn v9 => (if (v8 = 0)
 then []
 else (case v9 of
   (Expdectysig (v2, v1)) => (((((#"(" :: (#"t" :: (#"y" :: (#"s" :: (#"i" :: (#"g" :: (#" " :: []))))))) @ (qstr v2)) @ (#" " :: [])) @ (pr_ty v1)) @ (#")" :: []))
 | (Expdecpatbind (v4, v3)) => (((((#"(" :: (#"p" :: (#"a" :: (#"t" :: (#"b" :: (#"i" :: (#"n" :: (#"d" :: (#" " :: []))))))))) @ (pr_pat v4)) @ (#" " :: [])) @ ((pr_exp (let val k = (v8 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v3)) @ (#")" :: []))
 | (Expdecfunbind (v7, v6, v5)) => (((((((#"(" :: (#"f" :: (#"u" :: (#"n" :: (#"b" :: (#"i" :: (#"n" :: (#"d" :: (#" " :: []))))))))) @ (qstr v7)) @ (#" " :: (#"(" :: []))) @ (pr_pats v6)) @ (#")" :: (#" " :: []))) @ ((pr_exp (let val k = (v8 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v5)) @ (#")" :: [])))))
and pr_stmts v3 = (fn v4 => (if (v3 = 0)
 then []
 else (case v4 of
   [] => []
 | (v2 :: v1) => (((pr_stmt (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v2) @ ((pr_stmts (let val k = (v3 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v1)))))
and pr_stmt v5 = (fn v6 => (if (v5 = 0)
 then []
 else (case v6 of
   (Expdostmtexp v1) => (((#"(" :: (#"e" :: (#"x" :: (#"p" :: (#" " :: []))))) @ ((pr_exp (let val k = (v5 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v1)) @ (#")" :: []))
 | (Expdostmtbind (v3, v2)) => (((((#"(" :: (#"b" :: (#"i" :: (#"n" :: (#"d" :: (#" " :: [])))))) @ (pr_pat v3)) @ (#" " :: [])) @ ((pr_exp (let val k = (v5 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v2)) @ (#")" :: []))
 | (Expdostmtlet v4) => (((#"(" :: (#"l" :: (#"e" :: (#"t" :: (#" " :: (#"(" :: [])))))) @ ((pr_decs (let val k = (v5 - 1)
 in (if (k < 0)
 then 0
 else k) end)) v4)) @ (#")" :: (#")" :: []))))));

val fuel = 1000000000;

fun pr_strs v3 = (case v3 of
   [] => []
 | (v2 :: v1) => (((#" " :: []) @ (qstr v2)) @ (pr_strs v1)));

fun pr_cons v5 = (case v5 of
   [] => []
 | (v4 :: v3) => (case v4 of
   (v2, v1) => (((((#"(" :: []) @ (qstr v2)) @ (pr_tys v1)) @ (#")" :: [])) @ (pr_cons v3))));

val pr_decl = (fn v11 => (case v11 of
   (Decltysig (v2, v1)) => (((((#"(" :: (#"t" :: (#"y" :: (#"s" :: (#"i" :: (#"g" :: (#" " :: []))))))) @ (qstr v2)) @ (#" " :: [])) @ (pr_ty v1)) @ (#")" :: []))
 | (Decldata (v5, v4, v3)) => (((((((#"(" :: (#"d" :: (#"a" :: (#"t" :: (#"a" :: (#" " :: [])))))) @ (qstr v5)) @ (#" " :: (#"(" :: []))) @ (pr_strs v4)) @ (#")" :: (#" " :: (#"(" :: [])))) @ (pr_cons v3)) @ (#")" :: (#")" :: [])))
 | (Declfunbind (v8, v7, v6)) => (((((((#"(" :: (#"f" :: (#"u" :: (#"n" :: (#"b" :: (#"i" :: (#"n" :: (#"d" :: (#" " :: []))))))))) @ (qstr v8)) @ (#" " :: (#"(" :: []))) @ (pr_pats v7)) @ (#")" :: (#" " :: []))) @ ((pr_exp fuel) v6)) @ (#")" :: []))
 | (Declpatbind (v10, v9)) => (((((#"(" :: (#"p" :: (#"a" :: (#"t" :: (#"b" :: (#"i" :: (#"n" :: (#"d" :: (#" " :: []))))))))) @ (pr_pat v10)) @ (#" " :: [])) @ ((pr_exp fuel) v9)) @ (#")" :: []))));

fun pr_decls v3 = (case v3 of
   [] => []
 | (v2 :: v1) => (((#"\n" :: (#" " :: [])) @ (pr_decl v2)) @ (pr_decls v1)));

val bench_res = (fn v5 => (String.implode (case (bench_cst v5) of
   (NONE) => (#"N" :: (#"O" :: (#"P" :: (#"A" :: (#"R" :: (#"S" :: (#"E" :: (#"\n" :: []))))))))
 | (SOME v4) => (case v4 of
   [] => (#"N" :: (#"O" :: (#"A" :: (#"S" :: (#"T" :: (#"\n" :: []))))))
 | (v3 :: v2) => (case (astdecls v3) of
   (NONE) => (#"N" :: (#"O" :: (#"A" :: (#"S" :: (#"T" :: (#"\n" :: []))))))
 | (SOME v1) => (((#"(" :: (#"d" :: (#"e" :: (#"c" :: (#"l" :: (#"s" :: [])))))) @ (pr_decls v1)) @ (#")" :: (#"\n" :: []))))))));

val bench_ok = (fn v5 => (case (bench_cst v5) of
   (NONE) => 0
 | (SOME v4) => (case v4 of
   [] => 1
 | (v3 :: v2) => (case (astdecls v3) of
   (NONE) => 1
 | (SOME v1) => 2))));

val tok_class = (fn v15 => (case v15 of
   (Whitespacet v1) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Newlinet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Lexerrort) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Hasht) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Lpart) => (#"P" :: (#"L" :: (#"p" :: (#"a" :: (#"r" :: [])))))
 | (Rpart) => (#"P" :: (#"R" :: (#"p" :: (#"a" :: (#"r" :: [])))))
 | (Start) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Commat) => (#"P" :: (#"C" :: (#"o" :: (#"m" :: (#"m" :: (#"a" :: []))))))
 | (Arrowt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Dotst) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Colont) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Sealt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Semicolont) => (#"P" :: (#"S" :: (#"e" :: (#"m" :: (#"i" :: [])))))
 | (Equalst) => (#"P" :: (#"E" :: (#"q" :: (#"u" :: (#"a" :: (#"l" :: (#"s" :: [])))))))
 | (Darrowt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Lbrackt) => (#"P" :: (#"L" :: (#"b" :: (#"r" :: (#"a" :: (#"c" :: (#"k" :: [])))))))
 | (Rbrackt) => (#"P" :: (#"R" :: (#"b" :: (#"r" :: (#"a" :: (#"c" :: (#"k" :: [])))))))
 | (Underbart) => (#"P" :: (#"U" :: (#"n" :: (#"d" :: (#"e" :: (#"r" :: []))))))
 | (Lbracet) => (#"P" :: (#"L" :: (#"b" :: (#"r" :: (#"a" :: (#"c" :: (#"e" :: [])))))))
 | (Bart) => (#"P" :: (#"B" :: (#"a" :: (#"r" :: []))))
 | (Rbracet) => (#"P" :: (#"R" :: (#"b" :: (#"r" :: (#"a" :: (#"c" :: (#"e" :: [])))))))
 | (Andt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Andalsot) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Ast) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Caset) => (#"P" :: (#"C" :: (#"a" :: (#"s" :: (#"e" :: [])))))
 | (Datatypet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Elset) => (#"P" :: (#"E" :: (#"l" :: (#"s" :: (#"e" :: [])))))
 | (Endt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Eqtypet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Exceptiont) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Fnt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Funt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Handlet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Ift) => (#"P" :: (#"I" :: (#"f" :: [])))
 | (Int_1) => (#"P" :: (#"I" :: (#"n" :: [])))
 | (Includet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Lett) => (#"P" :: (#"L" :: (#"e" :: (#"t" :: []))))
 | (Localt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Oft) => (#"P" :: (#"O" :: (#"f" :: [])))
 | (Opt_1) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Opent) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Orelset) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Raiset) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Rect) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Sharingt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Sigt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Signaturet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Structt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Structuret) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Thent) => (#"P" :: (#"T" :: (#"h" :: (#"e" :: (#"n" :: [])))))
 | (Typet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Valt) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Wheret) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Whilet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Witht) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Withtypet) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Intt v2) => (#"P" :: (#"I" :: (#"n" :: (#"t" :: []))))
 | (Hexintt v3) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Wordt v4) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Realt v5) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Stringt v6) => (#"P" :: (#"S" :: (#"t" :: (#"r" :: []))))
 | (Chart v7) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Tyvart v8) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Alphat v9) => (if (v9 = (#"d" :: (#"a" :: (#"t" :: (#"a" :: [])))))
 then (#"P" :: (#"D" :: (#"a" :: (#"t" :: (#"a" :: [])))))
 else (if (v9 = (#"d" :: (#"o" :: [])))
 then (#"P" :: (#"D" :: (#"o" :: [])))
 else (if (capname_tok v15)
 then (#"P" :: (#"C" :: (#"a" :: (#"p" :: []))))
 else (if (lcname_tok v15)
 then (#"P" :: (#"L" :: (#"c" :: [])))
 else (#"P" :: (#"A" :: (#"l" :: (#"p" :: (#"h" :: (#"a" :: []))))))))))
 | (Symbolt v10) => (if (v10 = (#":" :: (#":" :: [])))
 then (#"P" :: (#"D" :: (#"C" :: (#"o" :: (#"l" :: (#"o" :: (#"n" :: [])))))))
 else (if (v10 = (#"-" :: (#">" :: [])))
 then (#"P" :: (#"A" :: (#"r" :: (#"r" :: (#"o" :: (#"w" :: []))))))
 else (if (v10 = (#"<" :: (#"-" :: [])))
 then (#"P" :: (#"L" :: (#"A" :: (#"r" :: (#"r" :: (#"o" :: (#"w" :: [])))))))
 else (if (v10 = (#"`" :: []))
 then (#"P" :: (#"B" :: (#"a" :: (#"c" :: (#"k" :: (#"t" :: (#"i" :: (#"c" :: (#"k" :: [])))))))))
 else (if (v10 = (#"\\" :: []))
 then (#"P" :: (#"B" :: (#"a" :: (#"c" :: (#"k" :: (#"s" :: (#"l" :: (#"a" :: (#"s" :: (#"h" :: []))))))))))
 else (#"P" :: (#"S" :: (#"y" :: (#"m" :: [])))))))))
 | (Longidt (v12, v11)) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))
 | (Ffit v13) => (#"P" :: (#"F" :: (#"F" :: (#"I" :: []))))
 | (Replidt v14) => (#"P" :: (#"O" :: (#"t" :: (#"h" :: (#"e" :: (#"r" :: []))))))));

val tok_payload = (fn v15 => (case v15 of
   (Whitespacet v1) => []
 | (Newlinet) => []
 | (Lexerrort) => []
 | (Hasht) => []
 | (Lpart) => []
 | (Rpart) => []
 | (Start) => []
 | (Commat) => []
 | (Arrowt) => []
 | (Dotst) => []
 | (Colont) => []
 | (Sealt) => []
 | (Semicolont) => []
 | (Equalst) => []
 | (Darrowt) => []
 | (Lbrackt) => []
 | (Rbrackt) => []
 | (Underbart) => []
 | (Lbracet) => []
 | (Bart) => []
 | (Rbracet) => []
 | (Andt) => []
 | (Andalsot) => []
 | (Ast) => []
 | (Caset) => []
 | (Datatypet) => []
 | (Elset) => []
 | (Endt) => []
 | (Eqtypet) => []
 | (Exceptiont) => []
 | (Fnt) => []
 | (Funt) => []
 | (Handlet) => []
 | (Ift) => []
 | (Int_1) => []
 | (Includet) => []
 | (Lett) => []
 | (Localt) => []
 | (Oft) => []
 | (Opt_1) => []
 | (Opent) => []
 | (Orelset) => []
 | (Raiset) => []
 | (Rect) => []
 | (Sharingt) => []
 | (Sigt) => []
 | (Signaturet) => []
 | (Structt) => []
 | (Structuret) => []
 | (Thent) => []
 | (Typet) => []
 | (Valt) => []
 | (Wheret) => []
 | (Whilet) => []
 | (Witht) => []
 | (Withtypet) => []
 | (Intt v2) => (pr_num v2)
 | (Hexintt v3) => []
 | (Wordt v4) => []
 | (Realt v5) => []
 | (Stringt v6) => v6
 | (Chart v7) => []
 | (Tyvart v8) => []
 | (Alphat v9) => v9
 | (Symbolt v10) => v10
 | (Longidt (v12, v11)) => []
 | (Ffit v13) => v13
 | (Replidt v14) => []));

val loc_rc = (fn v5 => (case v5 of
   (Locs (v4, v3)) => (case v4 of
   (Unknownpt) => (0, 0)
 | (Eofpt) => (0, 0)
 | (Posn (v2, v1)) => (v2, v1))));

val tok_line = (fn v6 => (case v6 of
   (v5, v4) => (let val v3 = (loc_rc v4)
 in (case v3 of
   (v2, v1) => ((((((((tok_class v5) @ (#" " :: [])) @ (pr_num v2)) @ (#" " :: [])) @ (pr_num v1)) @ (#" " :: [])) @ (qstr (tok_payload v5))) @ (#"\n" :: []))) end)));

val tok_dump = (fn v1 => (String.implode (flat ((CML_List.map tok_line) v1))));

fun lex_loop n = (fn s => (fn acc => (let val cml_x32v0 = ((cml_x60x61 n) 0)
 in (if cml_x32v0
 then acc
 else (let val cml_x32v2 = (CML_String.explode s)
 in (let val cml_x32v3 = (lexer_fun cml_x32v2)
 in (let val cml_x32v4 = (CML_List.length cml_x32v3)
 in (let val cml_x32v5 = ((cml_x43 acc) cml_x32v4)
 in (let val cml_x32v1 = ((cml_x45 n) 1)
 in (((lex_loop cml_x32v1) s) cml_x32v5) end) end) end) end) end)) end)));

fun parse_loop n = (fn toks => (fn acc => (let val cml_x32v0 = ((cml_x60x61 n) 0)
 in (if cml_x32v0
 then acc
 else (let val cml_x32v2 = (bench_ok toks)
 in (let val cml_x32v3 = ((cml_x43 acc) cml_x32v2)
 in (let val cml_x32v1 = ((cml_x45 n) 1)
 in (((parse_loop cml_x32v1) toks) cml_x32v3) end) end) end)) end)));

fun main u = (let val cml_x32v0 = ()
 in (let val args = (CML_CommandLine.arguments cml_x32v0)
 in (let val mode = ((CML_List.nth args) 0)
 in (let val fname = ((CML_List.nth args) 1)
 in (let val cml_x32v1 = (CML_List.length args)
 in (let val cml_x32v2 = ((cml_x62 cml_x32v1) 2)
 in (let val reps = (if cml_x32v2
 then (let val cml_x32v3 = ((CML_List.nth args) 2)
 in (let val cml_x32v4 = (CML_Int.fromString cml_x32v3)
 in (case cml_x32v4 of
   (SOME n) => n
 | (NONE) => 1) end) end)
 else 1)
 in (let val is = (CML_TextIO.openIn fname)
 in (let val s = (CML_TextIO.inputAll is)
 in (let val u = (CML_TextIO.closeIn is)
 in (let val cml_x32v5 = (CML_String.explode s)
 in (let val toks = (lexer_fun cml_x32v5)
 in (let val cml_x32v6 = ((cml_x61 mode) "tokens")
 in (if cml_x32v6
 then (let val cml_x32v7 = (tok_dump toks)
 in (CML_TextIO.cml_print cml_x32v7) end)
 else (let val cml_x32v8 = ((cml_x61 mode) "ast")
 in (if cml_x32v8
 then (let val cml_x32v9 = (bench_res toks)
 in (CML_TextIO.cml_print cml_x32v9) end)
 else (let val cml_x32v10 = ((cml_x61 mode) "lex")
 in (if cml_x32v10
 then (let val cml_x32v11 = (((lex_loop reps) s) 0)
 in (let val cml_x32v12 = (CML_Int.toString cml_x32v11)
 in (let val cml_x32v13 = ((cml_x94 cml_x32v12) "\n")
 in (CML_TextIO.cml_print cml_x32v13) end) end) end)
 else (let val cml_x32v14 = ((cml_x61 mode) "parse")
 in (if cml_x32v14
 then (let val cml_x32v15 = (((parse_loop reps) toks) 0)
 in (let val cml_x32v16 = (CML_Int.toString cml_x32v15)
 in (let val cml_x32v17 = ((cml_x94 cml_x32v16) "\n")
 in (CML_TextIO.cml_print cml_x32v17) end) end) end)
 else (CML_TextIO.cml_print "usage: purebench tokens|ast|lex|parse FILE [REPS]\n")) end)) end)) end)) end) end) end) end) end) end) end) end) end) end) end) end) end);


(* polyc's entry point: CakeML's main, reporting what escapes it *)
val main = fn () =>
  main () handle e =>
    (TextIO.output (TextIO.stdErr,
                    "uncaught exception: " ^ General.exnMessage e ^ "\n");
     OS.Process.exit OS.Process.failure);
