(* Queues three ways: a functional two-list queue, a mutable ring buffer
   over a list of cells, and a leftist heap as a priority queue; then a
   memoised shortest-path search that uses the heap. *)

open Printf

type 'a fqueue = { front : 'a list; back : 'a list }

let fempty = { front = []; back = [] }

let fpush x q = { q with back = x :: q.back }

let fpop q =
  match q.front with
  | x :: front -> Some (x, { q with front = front })
  | [] ->
      match List.rev q.back with
      | [] -> None
      | x :: front -> Some (x, { front = front; back = [] })

let rec fdrain q acc =
  match fpop q with
  | None -> List.rev acc
  | Some (x, q) -> fdrain q (x :: acc)

type 'a cell = { mutable value : 'a option; mutable next : 'a cell option }

type 'a mqueue = {
  mutable head : 'a cell option;
  mutable tail : 'a cell option;
  mutable length : int;
}

let mcreate () = { head = None; tail = None; length = 0 }

let mpush q x =
  let c = { value = Some x; next = None } in
  (match q.tail with
   | None -> q.head <- Some c
   | Some t -> t.next <- Some c);
  q.tail <- Some c;
  q.length <- q.length + 1

let mpop q =
  match q.head with
  | None -> None
  | Some c ->
      q.head <- c.next;
      if q.head = None then q.tail <- None;
      q.length <- q.length - 1;
      c.value

type 'a heap =
  | E
  | T of int * 'a * 'a heap * 'a heap

let rank = function E -> 0 | T (r, _, _, _) -> r

let make x a b =
  if rank a >= rank b then T (rank b + 1, x, a, b) else T (rank a + 1, x, b, a)

let rec merge cmp h1 h2 =
  match h1, h2 with
  | E, h | h, E -> h
  | T (_, x, a1, b1), T (_, y, a2, b2) ->
      if cmp x y <= 0 then make x a1 (merge cmp b1 h2)
      else make y a2 (merge cmp h1 b2)

let hpush cmp x h = merge cmp (T (1, x, E, E)) h

let hpop cmp = function
  | E -> None
  | T (_, x, a, b) -> Some (x, merge cmp a b)

let heap_sort cmp xs =
  let h = List.fold_left (fun h x -> hpush cmp x h) E xs in
  let rec go h acc =
    match hpop cmp h with
    | None -> List.rev acc
    | Some (x, h) -> go h (x :: acc)
  in
  go h []

(* a graph as adjacency lists; Dijkstra with the heap, distances memoised *)

let graph = [
  "a", ["b", 7; "c", 9; "f", 14];
  "b", ["a", 7; "c", 10; "d", 15];
  "c", ["a", 9; "b", 10; "d", 11; "f", 2];
  "d", ["b", 15; "c", 11; "e", 6];
  "e", ["d", 6; "f", 9];
  "f", ["a", 14; "c", 2; "e", 9];
]

let neighbours v = try List.assoc v graph with Not_found -> []

let memo = Hashtbl.create 16

let dijkstra source =
  match Hashtbl.find_opt memo source with
  | Some d -> d
  | None ->
      let dist = Hashtbl.create 16 in
      let cmp (d1, _) (d2, _) = compare d1 d2 in
      let rec loop h =
        match hpop cmp h with
        | None -> ()
        | Some ((d, v), h) when Hashtbl.mem dist v -> ignore d; loop h
        | Some ((d, v), h) ->
            Hashtbl.add dist v d;
            let h =
              List.fold_left (fun h (w, len) ->
                  if Hashtbl.mem dist w then h else hpush cmp (d + len, w) h)
                h (neighbours v)
            in
            loop h
      in
      loop (hpush cmp (0, source) E);
      Hashtbl.add memo source dist;
      dist

let () =
  let q = List.fold_left (fun q x -> fpush x q) fempty [1; 2; 3; 4; 5] in
  printf "fqueue: %s\n" (String.concat " " (List.map string_of_int (fdrain q [])));
  let m = mcreate () in
  List.iter (mpush m) ["x"; "y"; "z"];
  let rec drain acc =
    match mpop m with
    | Some s -> drain (s :: acc)
    | None -> List.rev acc
  in
  printf "mqueue: %s (length now %d)\n" (String.concat " " (drain [])) m.length;
  printf "sorted: %s\n"
    (String.concat " " (List.map string_of_int (heap_sort compare [5; 1; 4; 1; 5; 9; 2; 6])));
  let d = dijkstra "a" in
  List.iter (fun (v, _) ->
      printf "a -> %s: %d\n" v (try Hashtbl.find d v with Not_found -> -1)) graph
