(* Honor code comes here:

   First Name: Ethan
   Last Name: Seow
   BU ID: U45823198

   I pledge that this program represents my own program code and
   that I have coded on my own. I received help from no one in
   designing and debugging my program.  I have read the course
   syllabus of CS 320 and have read the sections on Collaboration
   and Academic Misconduct. I also understand that I may be asked
   to meet the instructor or the TF for a follow up interview on
   Zoom. I may be asked to explain my solution in person and may
   also ask you to solve a related problem. *)

(* Problem 1. *)
(* Determine the length of a list.
   Examples:
   length [] = 0
   length [1; 2; 3] = 3
*)
let rec length (l : 'a list): int =
  match l with
  | [] -> 0
  | h::t -> 1 + length(t);;

(*
   Using 'type' we may define aliases for types. In this case, anywhere we write
   'matrix' in our types OCaml will see 'float list list' instead.

   A float is a whole number with a decimal value as well. In OCaml, the
   operators to work with them have a trailing '.' e.g.:
   3. +. 4.2 = 7.2
   2. *. 1.4 = 2.8
*)
type matrix = float list list

(* Problem 2. *)
(* Determine if a matrix is square (n by n, for any n >= 0).
   Examples:
   is_square [[1.; 2.]] = false
   is_square [[1.; 2.]; [3.; 4.]] = true
*)
let rec is_square (m : matrix): bool =
  let rec helper (const : int) (m : matrix) = 
    match m with
    | [] -> true
    | h::t -> length(h) = const && helper const t
  in 
    helper (length(m)) m
  (*
      let rec helper (prev : int) (m2 : matrix) : bool = 
    match m2 with
    | [] -> true
    | h::t -> 
      if length(h) <> prev
        then 
          false
      else
        true && helper (length(h)) t
  in
    match m with
    | [] -> true
    | h::t -> helper (length(h)) t;;
  *)


(* Problem 3. *)
(* With an option type, we care about the value (possibly) stored inside. We
   will often write code that looks like the following:
   match my_option with
   | None -> None
   | Some(x) -> do calculation on x...

  To make avoid having to write this over and over, we can write a simple
  function which works with a function as an argument to make it easier! Write
  that function.

  Examples:
  let x = Some(3) in
    and_then x (fun y -> Some(y + 1))
  = Some(4)

  let x = None in
    and_then x (fun y -> Some(y + 1))
  = None
*)
let and_then (o : 'a option) (f : 'a -> 'b option) : 'b option =
  match o with
  | None -> None
  | Some(x) -> f x



(* Problem 4. *)
(* Add the elements of two lists together,
   if they are different lengths return None.

   Examples:
   add_lists [1.; 2.] [3.; 4.] = Some([4.; 6.])
   add_lists [] [1.2] = None
*)
let rec add_lists (xs : float list) (ys : float list): float list option =
  let rec helper (xs : float list) (ys : float list): float list =
    match xs with
    | [] -> []
    | h1::t1 -> 
      match ys with
      | [] -> []
      | h2::t2 -> ((h1 +. h2)::(helper t1 t2))
    in
  if length(xs) <> length(ys)
      then
        None
  else
    Some (helper xs ys);;

add_lists [1.; 2.] [3.; 4.];;
add_lists [] [1.2];;
(* Problem 5. *)
(* Add the elements of two matrices together,
   if they are different dimensions return None.

   Examples:
   add_matrices [[1.; 2.]; [3.; 4.]] [[0.; 0.5]; [1.4; 4.7]]
   = Some([[1.; 2.5]; [4.4; 8.7]])
*)
let rec add_matrices (m1 : matrix) (m2 : matrix): matrix option =
  let rec checker (m1 : matrix) (m2 : matrix) : bool = 
    let pair = (m1,m2) in 
    match pair with
    | ([],[]) -> true
    | (h1::t1,[])-> false
    | ([],h2::t2) -> false
    | (h1::t1, h2::t2) -> 
        match add_lists h1 h2 with
        | None -> false
        | Some(l) -> true && (checker t1 t2)
  in
  if checker m1 m2 = true
    then
      let rec helper (m1 : matrix) (m2 : matrix) : matrix =
        let pair = (m1,m2) in
        match pair with
        | ([],[]) -> []
        | (h1::t1, h2::t2) -> 
            match (add_lists h1 h2) with
            | None -> []
            | Some(l) -> l :: helper t1 t2
      in
      Some(helper m1 m2)
  else
      None

   

(* Problem 6. *)
(* Scale each element of the list by the given constant.
   Examples:
   scale_list 3. [1.; 2.; 4.] = [3.; 6.; 12.]
*)
let rec scale_list (s : float) (l : float list): float list =
  match l with
  | [] -> []
  | h::t -> (s *. h) :: scale_list s t;;

(* Problem 7. *)
(* Scale each element of the matrix by the given constant.
   Examples:
   scale_matrix 3. [[1.; 2.]; [3.; 4.]] = [[3.; 6.]; [9.; 12.]]
*)
let rec scale_matrix (s : float) (m : matrix): matrix =
  match m with
  | [] -> []
  | h::t -> (scale_list s h) :: scale_matrix s t
      

(* Problem 8. *)
(* Convert the matrix into a list by flattening it.
   Examples:
   into_list [[1.]] = [1.]
   into_list [[1.; 2.]; [3.; 4.]] = [1.; 2.; 3.; 4.]
*)
let rec into_list (m : matrix): float list =
  match m with
  | [] -> []
  | h1::t1 ->
    let rec oneByOne (l : float list) =
      match l with
      | [] -> into_list t1
      | h::t -> h:: oneByOne t
    in
      oneByOne h1

(* Problem 9. *)
(* Transpose the matrix.

   Given a matrix of dimensions M x N, the transpose is a matrix with dimensions
   N x M produced by swapping columns and rows.

   For a 4x3 matrix:

   0  1  2  3
   4  5  6  7
   8  9  10 11
   ==>
   0 4 8
   1 5 9
   2 6 10
   3 7 11

   Examples:
   transpose [[1.; 2.]; [3.; 4.]] = [[1.; 3.]; [2.; 4.]]

   transpose
    
   =
    [[0.; 1.; 2.; 3.]; [4.; 5.; 6.; 7.]; [8.; 9.; 10.; 11.]]

   Notes:
   * You may assume all nested int lists are of the same length (aka matrix is well-formed).
*)
let transpose (lss : matrix) : matrix =
  let reverse (l : 'a list) =
    let rec rev (l : 'a list) (acc:'a list): 'a list = 
      match l with
      | [] -> acc
      | h::t -> rev (t) (h::acc)
    in 
    rev l []
  in
  let rec column (lss:matrix) : float list = 
    match lss with 
    | [] -> []
    | row::restRows ->
      match row with
      | [] -> []
      | h::t -> h::column(restRows)
    in
  let rec otherColumns (lss : matrix) (acc:matrix): matrix = 
    match lss with
    | [] -> reverse(acc)
    | row::restRows -> 
      match row with
      | [] -> []
      | _::t -> otherColumns (restRows) (t::acc)
    in
  let rec helper (lss : matrix): matrix = 
    match lss with
    | [] -> []
    | _::restRows ->
      if column(lss) = []
        then
          []
      else
        column(lss)::helper(otherColumns lss [])
  in
  helper lss

(* Problem 10. *)
(* Generate the cofactor of the matrix.

   Given a matrix, invert the sign of its elements in an alternating
   ('checkerboard') fashion. This is used in the process of inverting matrices.
   Specifically, for a 4x3 matrix, we would want to apply the follow change
   (where '-' means to invert the sign):

    +  -  +  -
    -  +  -  +
    +  -  +  -

    0 -1 -2  3
   -4  5  6 -7
   -8  9 10 11
   ==>
    0  1 -2 -3
    4  5 -6 -7
   -8 -9 10 -11

  Examples:
  cofactor [[1.; 1.; 1.]]     = [[1.; -1.; 1.]]
  cofactor [[1.]; [1.]; [1.]] = [[1.]; [-1.]; [1.]]

  cofactor
    [[0.; -4.; -8.]; [-1.; 5.; 9.]; [-2.; 6.; 10.]; [3.; -7.; 11.]]
  =
    [[0.; 4.; -8.]; [1.; 5.; -9.]; [-2.; -6.; 10.]; [-3.; -7.; -11.]]

  cofactor [[2.; -2.; 0.]; [2.; 3.; -10.]; [2.; 3.; 0.]]
    = [[2.; 2.; 0.]; [-2.; 3.; 10.]; [2.; -3.; 0.]]
*)
let rec cofactor (m : matrix) : matrix =
  let rec helper (m : matrix) (acc : float) : matrix = 
    match m with
    | [] -> []
    | row::restRows ->
      let rec scaler (l : float list) (acc : float) = 
        match l with 
        | [] -> []
        | h::t -> acc *. h ::scaler t (-1. *. acc)
      in scaler row acc::helper restRows (-1. *. acc)
  in helper m 1.
