(* Sets as red-black trees (Okasaki), with the usual operations on them. *)

type color = Red | Black

type 'a tree =
  | Empty
  | Node of color * 'a tree * 'a * 'a tree

type 'a set = { cmp : 'a -> 'a -> int; root : 'a tree; size : int }

let empty cmp = { cmp = cmp; root = Empty; size = 0 }

let is_empty s = s.size = 0

let rec mem cmp x = function
  | Empty -> false
  | Node (_, l, y, r) ->
      let c = cmp x y in
      if c = 0 then true else if c < 0 then mem cmp x l else mem cmp x r

let balance = function
  | Black, Node (Red, Node (Red, a, x, b), y, c), z, d
  | Black, Node (Red, a, x, Node (Red, b, y, c)), z, d
  | Black, a, x, Node (Red, Node (Red, b, y, c), z, d)
  | Black, a, x, Node (Red, b, y, Node (Red, c, z, d)) ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
  | color, l, v, r -> Node (color, l, v, r)

let insert x s =
  let added = ref false in
  let rec ins = function
    | Empty -> added := true; Node (Red, Empty, x, Empty)
    | Node (color, l, y, r) as t ->
        let c = s.cmp x y in
        if c < 0 then balance (color, ins l, y, r)
        else if c > 0 then balance (color, l, y, ins r)
        else t
  in
  let root =
    match ins s.root with
    | Node (_, l, y, r) -> Node (Black, l, y, r)
    | Empty -> Empty
  in
  { s with root = root; size = if !added then s.size + 1 else s.size }

let member x s = mem s.cmp x s.root

let rec fold f t acc =
  match t with
  | Empty -> acc
  | Node (_, l, x, r) -> fold f r (f x (fold f l acc))

let elements s = List.rev (fold (fun x acc -> x :: acc) s.root [])

let of_list cmp xs = List.fold_left (fun s x -> insert x s) (empty cmp) xs

let union a b = fold insert b.root a

let filter p s =
  fold (fun x acc -> if p x then insert x acc else acc) s.root (empty s.cmp)

let rec height = function
  | Empty -> 0
  | Node (_, l, _, r) -> 1 + max (height l) (height r)

let rec black_height = function
  | Empty -> Some 1
  | Node (color, l, _, r) ->
      begin match black_height l, black_height r with
      | Some a, Some b when a = b -> Some (if color = Black then a + 1 else a)
      | _ -> None
      end

let rec no_red_red = function
  | Empty -> true
  | Node (Red, Node (Red, _, _, _), _, _) | Node (Red, _, _, Node (Red, _, _, _)) -> false
  | Node (_, l, _, r) -> no_red_red l && no_red_red r

let invariant s = black_height s.root <> None && no_red_red s.root

let min_elt s =
  let rec go = function
    | Empty -> None
    | Node (_, Empty, x, _) -> Some x
    | Node (_, l, _, _) -> go l
  in
  go s.root

let to_string show s =
  "{" ^ String.concat ", " (List.map show (elements s)) ^ "}"

let () =
  let s = of_list compare [5; 3; 8; 1; 4; 7; 9; 2; 6; 0] in
  let evens = filter (fun x -> x mod 2 = 0) s in
  let both = union s (of_list compare [10; 11; 12]) in
  print_endline (to_string string_of_int s);
  print_endline (to_string string_of_int evens);
  Printf.printf "size %d, height %d, ok %b\n" both.size (height both.root) (invariant both);
  match min_elt both with
  | Some x -> Printf.printf "min %d\n" x
  | None -> print_endline "empty"
