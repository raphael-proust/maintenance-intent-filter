(* couple helpers *)

let rec insert_in_bin
  (cmp : 'a -> 'a -> int)
  (bins: ('a * ('a list)) list)
  (x : 'a)
  : ('a * 'a list) list =
  match bins with
  | [] -> [(x, [x])]
  | (sample, _) :: _ when cmp x sample < 0 -> (x, [x]) :: bins
  | (sample, bin) :: bins when cmp x sample = 0 -> (sample, (x :: bin)) :: bins
  | bin :: bins -> bin :: (insert_in_bin cmp bins x)
let bin (cmp : 'a -> 'a -> int) (xs : 'a list) : ('a * 'a list) list =
  List.fold_left
    (insert_in_bin cmp)
    []
    xs
let list_nmaxes cmp n xs =
  bin cmp xs
  |> List.rev
  |> List.to_seq
  |> Seq.take n
  |> List.of_seq
  |> List.rev

let () = assert begin
  list_nmaxes Int.compare 0 [] = []
  && list_nmaxes Int.compare 0 [0;0;2;2] = []
  && list_nmaxes Int.compare 1 [] = []
  && list_nmaxes Int.compare 1 [0;0;2;2] = [(2, [2;2])]
  && list_nmaxes Int.compare 2 [0;1;2;3;3;1;2;1] = [(2,[2;2]);(3,[3;3])]
end



module M
: sig
  type separator = Dot | Dash
  type atom = (* the part of an intent in brackets *)
    | Last of int (**)
    | Any
    | Equal of int
  type 'atom t = (* an intent is a "list" of alternating atoms and separators *)
    | (::) of 'atom * 'atom s
  and 'atom s =
    | []
    | (::) of separator * 'atom t

  type intent = atom t
  type version = int t

  val catt : 'a t -> separator -> 'a t -> 'a t
  val ntht : 'a t -> int -> 'a
  val depth : 'a t -> int (* depth but not counting seps *)
  val get : 'a t -> separator list -> [> `Some of 'a | `Unfit | `Too_short ]

  val string_of_intent : intent -> string
  val version_of_string : string -> version
  val string_of_version : version -> string

end
= struct

type separator = Dot | Dash
type atom = (* the part of an intent in brackets *)
  | Last of int (**)
  | Any
  | Equal of int
type 'atom t = (* an intent is a "list" of alternating atoms and separators *)
  | (::) of 'atom * 'atom s
and 'atom s =
  | []
  | (::) of separator * 'atom t

let rec mapt (f : 'a -> 'b) : 'a t -> 'b t = function
  | [x] -> [f x]
  | x :: s :: xs -> f x :: s :: mapt f xs
let rec ntht t n =
  assert (n >= 0);
  match n, t with
  | 0, x :: _ -> x
  | n, _ :: _ :: xs -> ntht xs (n - 1)
  | _, [_] -> invalid_arg "index out of bound"
let catt xs s ys =
  let rec catt = function
    | [ x ] -> x :: s :: ys
    | x :: s :: xs -> x :: s :: catt xs
  in
  catt xs
let flattent (t: 'a t t) : 'a t =
  let rec flattent = function
    | [ x ] -> x
    | x :: s :: ys -> catt x s (flattent ys)
  in
  flattent t
let rec depth t =
  match t with
  | _ :: _ :: xs -> 1 + depth xs
  | [_] -> 1
let rec get t (ss : separator list) =
  match t, ss with
  | x :: _, [] -> `Some x
  | _ :: st :: t, s :: ss ->
      if st = s then
        get t ss
      else
        `Unfit
  | [_], _ :: _ -> `Too_short

type intent = atom t
type version = int t

let char_of_separator = function Dot -> '.' | Dash -> '-'
let string_of_separator = function Dot -> "." | Dash -> "-"

let rec string_of_t (p : 'a -> string) : 'a t -> string = function
  | [x] -> p x
  | x :: s :: xs -> p x ^ string_of_separator s ^ string_of_t p xs

let string_of_intent : intent -> string =
  string_of_t (function
  | Last 1 -> "(latest)"
  | Last n -> "(last " ^ string_of_int n ^ ")"
  | Any -> "(any)"
  | Equal i -> "("^ string_of_int i ^")" )
let string_of_version : version -> string = string_of_t string_of_int


(* splits a version string into the difference constituent that correspond to
   the different atoms of an intent *)
let intersperse (x : separator) (xs : 'a list) : 'a t =
  let rec intersperse : 'a list -> 'a t = function
    | [y] -> [y]
    | y :: ys -> y :: x :: intersperse ys
    | [] -> assert false
  in
  if xs = [] then invalid_arg "empty list to intersperse" else
  intersperse xs
let split sep (v : string) =
  v |> String.split_on_char (char_of_separator sep) |> intersperse sep
let version_of_string (v: string) : version =
  v
  |> split Dot
  |> mapt (split Dash)
  |> flattent
  |> mapt int_of_string

let () = assert begin
  version_of_string "0.1" = [0; Dot; 1]
  && version_of_string "0.1.1" = [0; Dot; 1; Dot; 1]
  && version_of_string "0.1.1-20250115" = [0; Dot; 1; Dot; 1; Dash; 20250115]
end

end

let nmaxes_versions seps n vs =
  List.map snd
          (list_nmaxes
            (fun v w ->
              match M.get v seps, M.get w seps with
              | `Some iv, `Some iw -> Int.compare iv iw
              | `Some _, `Too_short -> 1
              | `Too_short, `Some _ -> -1
              | `Too_short, `Too_short -> 0
              | `Unfit, _ | _, `Unfit -> assert false)
            n
            vs)

let filter intent versions =
  let rec filter
    (visited_separators: M.separator list)
    (remaining_intent: M.intent)
    (versions: M.version list)
  : M.version list
  =
    let versions = List.filter (fun v -> M.get v visited_separators <> `Unfit) versions in
    match remaining_intent with
    | [Any] -> versions
    | [Equal i] ->
        List.filter
          (fun v ->
            match M.get v visited_separators with
            | `Some ii -> i = ii
            | `Too_short -> false
            | `Unfit -> assert false)
          versions
    | [Last n] -> List.flatten ( nmaxes_versions visited_separators n versions )
    | Any :: sep :: intent ->
        let vss =
          (* sorting into buckets of same atom: max-int to mimic "Any" *)
          nmaxes_versions visited_separators Int.max_int versions
        in
        List.concat_map (filter (visited_separators @ [sep]) intent) vss
    | Equal i :: sep :: intent ->
        let vs =
          List.filter
            (fun v ->
              match M.get v visited_separators with
              | `Some ii -> i = ii
              | `Too_short -> false
              | `Unfit -> assert false)
            versions
        in
        filter (visited_separators @ [sep]) intent vs
    | Last n :: sep :: intent ->
        let vss = nmaxes_versions visited_separators n versions in
        List.concat_map (filter (visited_separators @ [sep]) intent) vss
  in
  filter [] intent versions


let ( == ) xs ys = List.sort compare xs = List.sort compare ys
let check i vs ws =
  let got = filter i (List.map M.version_of_string vs) in
  let exp = List.map M.version_of_string ws in
  if got = exp then true else begin
    Format.eprintf "Got [%s]\nExpected [%s]\n%!"
      (String.concat " ; " @@ List.map M.string_of_version got)
      (String.concat " ; " @@ List.map M.string_of_version exp)
    ;
    false
  end

let () = assert ( check [Any] [] [] )
let () = assert ( check [Equal 1] [] [] )
let () = assert ( check [Last 1] [] [] )

let () = assert ( check [Any] (["0.0.1"; "0.1"; "0.3-1"]) (["0.0.1"; "0.1"; "0.3-1"]) )
let () = assert ( check [Any; Dot; Equal 1] (["0.0.1"; "0.1"; "0.3-1"]) (["0.1"]) )

let () = assert ( check [Any; Dot; Last 1] ["0.0"; "0.1"; "0.3"] ["0.3"] )
let () = assert ( check [Any; Dot; Last 1; Dot; Last 1] ["0.0.1"; "0.1"; "0.3"] ["0.3"] )
let () = assert ( check [Any; Dot; Last 2] ["0.0.1"; "0.1"; "0.3"] ["0.1"; "0.3"] )
