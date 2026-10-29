(* HOL-Library.IArray prints IArray.sub'/length' as Vector.sub/length on
   IntInf.int indices, which only type-checks where int = IntInf.int
   (Isabelle's Poly/ML); distro Poly/ML has a fixed-precision int *)
structure Vector = struct
  open Vector
  fun sub (v, i : IntInf.int) = Vector.sub (v, IntInf.toInt i)
  fun length v : IntInf.int = IntInf.fromInt (Vector.length v)
end;
