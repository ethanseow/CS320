(* Honor code comes here:

   First Name: Ethan
   Last Name: Seow 
   BU ID: U45823198

   I pledge that this program represents my own program code and that I have
   coded on my own. I received help from no one in designing and debugging my
   program. I have read the course syllabus of CS 320 and have read the sections
   on Collaboration and Academic Misconduct. I also understand that I may be
   asked to meet the instructor or the TF for a follow up interview on Zoom. I
   may be asked to explain my solution in person and may also ask you to solve a
   related problem. *)

(* IMPORTANT, same requirements as PA3, standard library is disabled, no rec.

   Problems that do not satisfy requirements will have points deducted from your
   Gradescope score during manual grading.

   Requirements for the assignemnt.
   * You may NOT add or remove the 'rec' keyword.
   * Your helper functions may NOT use the 'rec' keyword.
   * You may not use ANY library functions.
   * You may not use list operators such as '@'.
   * The standard library will be disabled during grading, code
     dependent on library code will fail to compile. *)

(**************************************** Problem 1 ****************************************)
(* Simple functions

   Just like our list-manipulating higher-order functions, we often want similar
   sorts of functions on /functions/. These make it easier to pass and compose
   our utilities together, since all our abstractions are functions.
*)

(* Implement the identity function.

   Why? Sometimes we want to pass this to another function to have it do
   nothing. (See in 'const' below)
*)
let id (x : 'a): 'a = x

(* Implement the constant function.

   Why? Sometimes we don't care about the input.

   We can combine this with fold_left:
     let last_or: 'a -> 'a list -> 'a = fold_left (const id)
     (* What does this function do? *)
*)  
let const (x : 'a): 'ignored -> 'a = fun (y : 'ignored) -> x

(* Implement the function composition operator.

   Why? Putting two functions together to make 1 function is often useful.
     ((+) % length) [1; 2] 1
     (* A bit silly, but this produces 3. The type is:
        (+) % length : 'a list -> int -> int *)
*)
(* NOTE Binary operators are defined with '(operator)' in OCaml. *)

let (%) (f : 'a -> 'output) (g : 'input -> 'a): 'input -> 'output = 
  fun(y : 'input) -> f (g y)

     
  
(* Implement the 'flip' function, which swaps arguments.

   Why? Sometimes we have a function which takes arguments one way, but we need
   them to be taken the other way.
      let divide : int -> int -> int = fun n m -> n / m
      let divide_by_2 = flip divide 2
*)
let flip (f : 'a -> 'b -> 'c): 'b -> 'a -> 'c =
  fun (x : 'b) (y: 'a) -> f y x

(* Implement the application operator.

   Why? Parsing! Instead of wrapping our arguments in parenthesis:

   You cannot pass constructors directly to functions:
     my_fun MyConstructor(3)      (* WRONG! *)
     my_fun (MyConstructor(3))    (* RIGHT! *)
     my_fun @@ MyConstructor(3)   (* RIGHT! *)

     or, use with fun and and_then where parenthesis usually pile up (shown below)
*)

type 'a t = Nil
  | MyConstructor of 'a
let my_fun = fun x -> 1
let (@@) (f : 'a -> 'b) (a : 'a): 'b =
  f (a)

(* Implement the /reverse/ application operator.

   Why? To give a method of writing 'sequenced' operators in a cleaner way.
     More examples will be given later.
     This operator is used /extensively/ throughout the assignment.
*)
let (|>) (a : 'a) (f : 'a -> 'b): 'b =
  f (a)

(* We can write map functions for pairs.

   map_fst not (true, 3) = (false, 3)
*)
let map_fst (f : 'a -> 'c) ((a, b) : 'a * 'b): 'c * 'b = 
  (f a, b)

let map_snd (f : 'b -> 'c) ((a, b) : 'a * 'b): 'a * 'c = (a, f b)

(**************************************** Problem 2 ****************************************)
(* As with the previous assignment, we will begin with defining our basic
   datatypes and their functions. *)

(* Unlike the last programming assignment, we will 'properly' define list with
   the typical operator version of cons.
   NOTE: utop, etc. will still PRINT in prefix notation: (::) (1, []).
*)
type 'a list =
  | []
  | (::) of 'a * 'a list

(* For all our data types define functions to wrap our constructors, so we can
   this function as a value. You /cannot/ pass constructors as values.
   e.g.
     fold_right Cons my_list []    (* Does *not* work. *)
     fold_right cons my_list []    (* Does work. *)
*)
let nil : 'a list = []
let cons (hd : 'a) (tl : 'a list): 'a list = hd :: tl

(* Standard fold_left *)
let rec fold_left (f : 'a -> 'b -> 'a) (acc : 'a) (ls : 'b list): 'a =
  match ls with
  | [] -> acc
  | hd::rest -> fold_left f (f acc hd) rest

(* Reverse can be implemented with fold_left, note the use of flip! *)
let reverse (ls : 'a list): 'a list =
  fold_left (flip cons) [] ls
(* vs *)
(* fold_left (fun acc x -> x :: acc) [] ls *)

(* A more thorough example of using our function utilities. *)
(* Notice how this reads,
   fold_right is:
   - fold_left with its second and third arguments flipped.
   - fold_left with its function argument's arguments flipped.
   - fold_left with its output order reversed.
*)
let fold_right (f : 'a -> 'b -> 'b) =
  flip (fold_left (flip f)) % reverse

(* NOTE There is no use to fold_right in this assignment, this is an example *)

(* Implement map making use of "@@", "flip" and "%". *)
let map (f : 'a -> 'b) (ls : 'a list): 'b list = 
  reverse(fold_left (fun acc h -> 
    (f h) :: acc
  ) nil ls)

(* Implement length making use of "@@", "flip", and "const"

   Hint: You can turn "+" into a function by wrapping it in parenthesis "(+)".
*)
let length (ls : 'a list): int =
  fold_left (fun acc h -> acc+1) 0 ls

(* Standard append. *)
let append (ls1 : 'a list) (ls2 : 'a list): 'a list =
  fold_left (flip cons) ls2 @@ reverse ls1

(**************************************** Problem 3 ****************************************)
(* Standard definition of options *)
type 'a option =
  | None
  | Some of 'a

(* Wrappers again! *)
let none: 'a option = None
let some (x : 'a) : 'a option = Some(x)

(*******************************************
   A result is a type with two type parameters (list and option have one type
   parameter). Unlike option, which holds nothing or one thing, a result holds
   one thing or another thing (sometimes called an 'either' type).

   Result types let us represent errors better than option types, because we
   either have the value we expect or we have an error value.

   Let us see an example:
*)

type ('a, 'e) result =
  | Ok of 'a
  | Err of 'e

let ok  (res : 'a): ('a, 'e) result = Ok(res)
let err (err : 'e): ('a, 'e) result = Err(err)

(* EXAMPLE *)
type numeric_err =
  | DivisionByZero
  | IDoNotLikeNegatives

(* EXAMPLE Safe divide, which can not go wrong, or be negative! *)
let divide (n : int) (m : int): (int, numeric_err) result =
  if n < 0 || m < 0 then
    Err(IDoNotLikeNegatives)
  else if m = 0 then
    Err(DivisionByZero)
  else
    Ok(n / m)

(* Let's write some helpful library functions for result: *)

(* Implement 'fold' on results. *)
let fold_result (f : 'a -> 'b) (g : 'e -> 'b) (res : ('a, 'e) result): 'b =
  match res with
  | Ok x -> (f x)
  | Err y -> (g y)

(* Implement map(s) on results.

   Hint: Should be a call to fold_result and NO anonymous functions. (Use the
   operators on functions above!)
*)
let map_ok (f : 'a -> 'b) (res : ('a, 'e) result): ('b, 'e) result =
  fold_result (ok % f) err res

let map_err (f : 'e -> 'g) (res : ('a, 'e) result): ('a, 'g) result =
  fold_result ok (err % f) res


(* Implement and_then on results.

   This is an extremely powerful function, just like we had on options before.
   Now, we can also make use of reverse application (|>) to make very readable
   error handling.

   Suppose we want to implement the equation: (n / m) + (a / b) + (r / s)
   We can do it like so:

   If we did NOT use our utilities:

   let my_equation n m a b r s: (int, numeric_err) result =
     match divide n m with
     | Err(e) -> Err(e)
     | Ok(x) -> match divide a b with
                | Err(e) -> Err(e)
                | Ok(y) -> match divide r s with
                           | Err(e) -> Err(e)
                           | Ok(z) -> Ok(x + y + a)

   let my_equation n m a b r s : (int, numeric_err) result =
     divide n m |> and_then @@ fun x ->
     divide a b |> and_then @@ fun y ->
     divide r s |> and_then @@ fun z ->
     Ok(x + y + z)

   Nested pattern matching is definitely much nastier to deal with, while the
   above reads almost like English (with a lot of silly punctuation)! You should
   make heavy use of and_then in this assignment, or it will get very messy.
*)
let and_then (f : 'a -> ('b, 'e) result) (res : ('a, 'e) result): ('b, 'e) result =
  match res with
  | Ok a -> f a
  | Err e -> Err(e)

(* Implement combine_result, which combines two results.
   If either is an Err, the result is an Err.

   Hint: Use and_then
*)
let combine_result
    (f : 'a -> 'b -> 'c)
    (r1 : ('a, 'e) result)
    (r2 : ('b, 'e) result): ('c, 'e) result =
    r1 |> and_then @@ fun x ->
    r2 |> and_then @@ fun y ->
    Ok(f x y)

(* Implement all_ok, which takes a list of results and combines them all.
   If any result in the list is an Err, the result is an Err.
*)
let all_ok (ls : ('a, 'e) result list) : ('a list, 'e) result =
  fold_left (fun acc h -> 
  h |> and_then @@ fun a ->
  acc |> and_then @@ fun l ->
  Ok(a::l)
  ) (Ok([])) (reverse ls)

(* Very useful. Sometimes we call a helper which returns an option, but that is
   an error to us, the caller. *)
let from_option (e : 'e) (o : 'a option): ('a, 'e) result =
  match o with
  | None -> Err(e)
  | Some(a) -> Ok(a)

(*******************************************************************************
 * A history lesson on symbolic expressions (sexprs)
*)
(*
 In the 1950s John McCarthy created symbolic expressions [1], or
 s-expressions (abbreviated as sexprs). Sexprs were, and are still, used as the
 syntax for the LISP family of languages [2]. Sexprs are defined as:

  - an atom (a singular value)
  - something of the form (...) where ... is a space separated list of sexpr

 This definition is really just the English language version of the OCaml
 data type:
   type sexpr =
     | Atom of atom
     | SList of sexpr_list
   and sexpr_list = sexpr list

 What is an atom? It depends on the language you are trying to define; for this
 assignment, we will be defining a simple arithmetic LISP variant, so our atoms
 will include Symbol (stored as string in OCaml) and Number (int).

 What is most interesting about LISP (the name coming from LISt Processing), is
 that the most primitive data values are usually Nil and Cons values, so the
 primitive data type is a list similar to what we have seen in OCaml. Because it
 works on primarily on lists, and its syntax is just lists, LISP is actually
 /homoiconic/, the syntax of the language is itself a primitive data type in the
 language! The language is entirely based on the concept of manipulating lists
 and by extension manipulating itself. In fact, LISP was heavily used in AI
 research for decades (and still is) due to the idea of an AI wanting to be able
 to modify itself.

 So what does a LISP program look like? Because we only have sexprs for syntax,
 besides literals, every expression has the form:
   <literal value>
     or
   (<function> <arguments> ...)
 Where, in our case, <function> will be a symbol and <arguments> are expressions.
 E.g.
   3 is just 3

   (+ 1 (- 4 3) 3 4)
     is the same as OCaml
   1 + (4 - 3) + 3 + 4

   (if (not (= x 0)) (/ y x) 0)
    is the same as
   if not (x = 0) then y / x else 0

 ---- Footnotes
 [1] https://en.wikipedia.org/wiki/S-expression
 [2] https://en.wikipedia.org/wiki/Lisp_(programming_language)
     The most common LISP languages are:
     - Common Lisp: https://common-lisp.net/
     - Clojure: https://clojure.org/
     And some from the Scheme language family/standard, originally designed by
     Steele and Sussman in the 70s:
     - Racket: https://racket-lang.org/
     - Guile: https://www.gnu.org/software/guile/
     - Chicken: https://www.call-cc.org/

********************************************)

(* We define our atoms *)
type atom =
  | Symbol of string
  | Number of int

let symbol (s : string): atom = Symbol(s)
let number (n : int): atom    = Number(n)

(* Now our sexprs, notice the use of 'and' like we have with streams. *)
type sexpr =
  | Atom of atom
  | SList of sexpr_list
and sexpr_list = sexpr list

let atom  (a : atom): sexpr = Atom(a)
let slist (l : sexpr_list): sexpr = SList(l)

let snil: sexpr_list = []
let scons (s : sexpr) (rest : sexpr_list): sexpr_list = s :: rest

let snumber (n : int)   : sexpr = atom @@ number n
let ssymbol (s : string): sexpr = atom @@ symbol s

(* Mutually recursive data types require mutually recursive functions.

   If a function works, by pattern matching, to pull apart a piece of data and
   then calling itself, by recursion, on the recursive parts of the data. Then
   mutual recursion naturally has the step of:

    Function A:
   - pulls apart the data with pattern matching
   - calls itself on the recursive part
   - calls B on the mutually recursive part
     Function B:
   - pulls apart the data with pattern matching
   - calls itself on the recursive part
   - calls A on the mutually recursive part

   Let's consider a simple example:
*)

(* EXAMPLE *)
type even =
  | Zero
  | PrevOdd of odd
and odd =
  | PrevEven of even

(*
   This data type defines how we think of evenness and oddness over the natural
   numbers: for a number to be even, it is zero or the number before it was odd.
   And vice versa for odd.

   e.g.
     0 (even)
     1 (odd, as previous [0] is even)
     2 (even, as previous [1] is odd, as previous [0] is even)
     3 (odd, as previous  [2] is even, as previous [1] is odd...)
     .
     .
     .
*)
(*
     PrevOdd( PrevEven(0) )

     PrevOdd (PrevEven(0)) -> 1 + from_odd PrevEven(0)
      PrevEven 0 -> 1 + from_even 0
        0
*)
(* EXAMPLE *)
let rec from_even (e : even): int =
  match e with
  | Zero -> 0
  | PrevOdd(o) -> 1 + from_odd o
and from_odd (o : odd): int =
  match o with
  | PrevEven(e) -> 1 + from_even e


(* Going back to our sexprs we will be working with, our recursive functions
   will have a similar shape. Consider if we wanted to calculate the number of
   atoms in an sexpr: *)

(* EXAMPLE *)
let rec size_of_sexpr (s: sexpr): int =
  match s with
  | Atom(_) -> 1
  | SList(sl) -> size_of_sexpr_list sl
and size_of_sexpr_list (sl: sexpr_list): int =
  match sl with
  | [] -> 0
  | hd::rst -> size_of_sexpr hd + size_of_sexpr_list rst


(**************************************** Problem 4 ****************************************)
(*
  You will implement a parser on a stream of 'tokens'. Tokens are just a data
  type representing characters/words that we would get from a file or string.
  You will need to transform a stream of tokens into sexprs.
*)

type token =
  | SYMBOL of string
  | NUMBER of int
  | LPAREN
  | RPAREN
  | EOF

(* Our definition of streams as we have seen in lecture *)
type 'a str =
  | Next of 'a * 'a stream
and 'a stream = unit -> 'a str

let head (st : 'a stream): 'a =
  let Next(h, _) = st () in h

let tail (st : 'a stream): 'a stream =
  let Next(_, t) = st () in t

(* We will define a simple operator for building streams. *)
let (^) (a : token) (st : token stream): token stream =
  fun _ -> Next(a, st)

(* A token stream is terminated by an End Of File (EOF) token forever. *)
let rec eof (_ : unit): token stream =
  fun _ -> Next(EOF, eof ())

(* EXAMPLE: The token stream for a simple "(+ 3 2)" sexpr *)
let example_stream =  LPAREN ^ SYMBOL("+") ^ NUMBER(3) ^ NUMBER(2) ^ RPAREN ^ eof ()

(* We define an error type to return for when parsing fails:
   UnexpectedEOF occurs when we hit EOF but did not expect it,
     e.g. "(+ 2", we expected an ")"
   UnmatchedParen occurs in the other case where the /right/ paren is left open,
     e.g. "(+ 2 3))", we expected one less ")"
*)
type parse_err =
  | UnexpectedEOF
  | UnmatchedParen

(* Implement parse_sexpr and parse_sexpr_list, which take a token stream and
   produce an sexpr (or sexpr_list) and the remainder of the token stream.

   (* parse is a wrapper defined below *)

   parse example_stream
    = Ok(SList(Atom(Symbol("+"))::Atom(Number(3))::Atom(Number(2))::[])::[])

   parse (LPAREN ^ eof ())
    = Err(UnexpectedEOF)

   parse (LPAREN ^ RPAREN ^ RPAREN ^ eof ())
    = Err(UnexpectedParen)
*)
let rec parse_sexpr (st : token stream): (sexpr * token stream, parse_err) result =
  match head st with
  | LPAREN -> 
      parse_sexpr_list (tail st) |> and_then @@ (fun (l,rest) -> (Ok((SList(l)),rest)))
  | NUMBER n -> (Ok(Atom(Number(n)), tail st))
  | SYMBOL s -> (Ok(Atom(Symbol(s)), tail st))
  | RPAREN -> 
      Err(UnmatchedParen)
  | EOF -> 
    Err(UnexpectedEOF)
  
  and parse_sexpr_list (st : token stream): (sexpr_list * token stream, parse_err) result =
    match  head st with
    | RPAREN -> (Ok([],tail st))
    | _ -> 
      parse_sexpr st |> and_then @@ fun(a, aTail) ->
      parse_sexpr_list aTail |> and_then @@ fun(b, bTail) ->
      Ok(((cons a b), bTail))


(* Tries to parse the token stream into sexprs until it hits EOF *)
let parse (st : token stream): (sexpr list, parse_err) result =
  let rec parse_all st acc =
    let Next(tok, _) = st () in
    match tok with
    | EOF -> Ok(reverse acc)
    | _   -> parse_sexpr st
             |> and_then @@ fun (s, ts) ->
      parse_all ts (s :: acc)
  in
  parse_all st []

(**************************************** Problem 5 ****************************************)
(*
  Now we want to evaluate our sexprs to give us a small arithmetic language.

  The language will include: arithmetic, booleans, if-then-else.
  Specifically, here is how our expressions will compare in specific instances to OCaml:
           sexprs                      Ocaml
     ------------------------- ---------------------------
             Can take any number of arguments:
     (and true false true)    ~    true && false && true
     (or  false false)        ~    false || false
     (+ 1 2 3)                ~    1 + 2 + 3
     (- 3 4 1 3)              ~    ((3 - 4) - 1) - 3
     ( * 2 2 2)               ~    2 * 2 * 2
     (/ 5 2 1)                ~    (5 / 2) / 1

                  Can take one argument:
     (not false)              ~    not false

                  Can take two arguments:
     (< 3 2)                  ~    3 < 2
     (= 2 2)                  ~    2 = 2

                  Control structures:
     (if (< 1 3) 0 1)         ~  if 1 < 3 then 0 else 1
*)

(* The type for values. When we e/valu/ate we turn expressions into values. *)
(* In our language, either we have a number or a boolean. *)
type value =
  | Int of int
  | Bool of bool

let val_int (n : int): value = Int(n)
let val_bool (b : bool): value = Bool(b)

(* Our errors for evaluating.

   UnknownSymbol    , if we encounter a symbol we do not know
   NotABool         , if we have (and 1 true), "1" should be a boolean
   NotANumber       , if we have (+ 1 true), "true" should be a number
   InvalidExpr      , if the sexpr is none of the valid sexprs
*)
type eval_err =
  | UnknownSymbol of string
  | NotABool of value
  | NotANumber of value
  | InvalidExpr of sexpr

(* Implement eval_sexpr and eval_sexpr_list
   (* run is a wrapper defined below *)

   run example_stream
     = Ok(Int 5 :: [])
*)
let rec eval_sexpr (e : sexpr): (value, eval_err) result =
  failwith "unimplemented"

and eval_sexpr_list (e : sexpr_list): (value, eval_err) result =
  failwith "unimplemented"

type run_err =
  | ParseError of parse_err
  | EvalError of eval_err

let parse_error x = ParseError(x)
let eval_error  x = EvalError(x)

(* Takes a token stream,
   parses it into a list of sexpr,
   evaluates all the sexpr to get a list of values *)
   (*
      
let run (st : token stream): (value list, run_err) result =
  parse st
  |> map_err parse_error
  |> and_then @@
  map_err eval_error % all_ok % map (eval_sexpr [])
   *)