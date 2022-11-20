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

(*NOTE: There are no restrictions on what you can use*)
#load "str.cma";;
type const = 
  | Int of int
  | String of string
  | Var of string
type com = 
  | Quit
  | Push of const
  | Pop
  | Add
  | Sub
  | Mul
  | Div
  | Swap
  | Neg
  | Concat
  | Begin
  | End
  | Global of const
  | Local of const

let regexp = Str.regexp "[-0-9]+$"
let regexp2 = Str.regexp "\\\"[A-Za-z]+\\\"$"
let regexp3 = Str.regexp "[a-z]+$"
let stringToConst (str : string ) : const =
  if Str.string_match regexp str 0
    then
      let x = int_of_string str
      in
      Int(x)
  else
    if Str.string_match regexp2 str 0
      then
        String(str)
    else
      if Str.string_match regexp3 str 0
        then
          Var(str)
      else
        String("error")

let stringToCom (inp : string list) : com =
  let comm = List.nth inp 0
  in
  match comm with
  | "Quit" -> Quit
  | "Push" -> 
    let v = stringToConst (List.nth inp 1)
    in
    Push(v)
  | "Global" -> 
    let v = stringToConst (List.nth inp 1)
    in
    Global(v)
  | "Local" -> 
    let v = stringToConst(List.nth inp 1)
    in
    Local(v)
  | "Pop" -> Pop
  | "Add" -> Add
  | "Concat" -> Concat
  | "Sub" -> Sub
  | "Mul" -> Mul
  | "Div" -> Div
  | "Swap" -> Swap
  | "Neg" -> Neg
  | "Concat" -> Concat

let printToFile (inp : string list) (file_path : string) : unit = 
  let fp = open_out file_path in
  let lekunga = (String.concat "\n" inp)
  in
  let () = Printf.fprintf fp "%s" lekunga in
    close_out fp

let srcToCom (src : string) : com list = 
  let cmds = String.split_on_char '\n' src
  in
  let helper (inp : string) : com =
    let x = String.split_on_char ' ' inp
    in
    stringToCom x
  in
  List.map helper cmds

let constListToString (c : const list) : string list =
  let helper (co : const) = 
    match co with
    | Int i -> string_of_int i
    | String s -> s
  in
  List.map helper c

let error = (true, (String("\"Error\""))::[])

let isInteger (c : const) : bool = 
  match c with
  | Int _ -> true
  | String _ -> false

let lengthGreaterTwo (accum) : bool =
  List.length accum >= 2

let topTwoInteger (accum : const list) : bool = 
  (isInteger (List.nth accum 0)) && (isInteger (List.nth accum 1))

let divideByZero (accum : const list) : bool = 
  let Int i = List.nth accum 1
  in i != 0

let popStack (accum : const list) = 
    match accum with
      | [] -> [] 
      | _::t -> t

let higherOrderOp (f : 'a -> 'b -> 'c) (a : const) (b: const) : const = 
  let Int i = a
  in
  let Int j = b
  in
  (Int(f i j))

let higherOrderMathCom (errorCheck : (const list -> bool) list) (f : 'a -> 'b -> 'c) (b : bool) (accum : const list) : (bool * (const list)) = 
  let helper acc h = 
    if acc = false
      then
        false
    else
      h accum
  in
  let passedChecks = List.fold_left helper true errorCheck
  in
  if passedChecks = false
    then
      error
  else
        let (one,two) = (List.nth accum 0, List.nth accum 1)
        in
        let a = popStack (popStack accum)
        in
        (b, ((higherOrderOp f one two)::a))

let pop (b : bool) (accum : const list) : (bool * (const list)) =
  if List.length accum < 1
    then
      error
  else
    (b,(popStack accum))

let swap (b : bool) (accum : const list) : (bool * (const list)) =
  if List.length accum < 2
    then
      error
  else
    let one = List.nth accum 0
    in
    let two = List.nth accum 1
    in
    let a = popStack (popStack accum)
    in
    (b, two::one::a)

let neg (b : bool) (accum : const list) : (bool * (const list)) =
    if List.length accum < 1
      then
      error
    else
      if isInteger (List.nth accum 0) = false
        then
          error
      else
        let Int i = List.nth accum 0
        in
        let a = popStack accum
        in
        (b, (Int(-1 * i))::a)

let concat (b : bool) (accum : const list) : (bool * (const list)) =
    if List.length accum < 2
      then
      error
    else
      if topTwoInteger accum = true
        then
          error
      else
        let String i = List.nth accum 0
        in
        let String j = List.nth accum 1
        in
        let a = popStack (popStack accum)
        in
        let removeQuotes (str : string) : string = 
          Str.(global_replace (regexp "\"") "" str)
        in
        (b, (String("\"" ^ removeQuotes (i ^ j) ^ "\""))::a)


let interpret (acc : (bool * (const list))) (comm : com) : (bool * (const list)) = 
  let (b, accum) = acc
  in
  if b == true
    then
      acc
  else
    match comm with
    | Quit -> (true,accum)
    | Push v -> 
      if isInteger v
        then
        (b,v::accum)
      else
        let String a = v
        in
        if a = "error"
          then
          error
        else
          (b,v::accum)
    | Pop -> pop b accum
    | Add -> higherOrderMathCom (lengthGreaterTwo::topTwoInteger::[]) (+) b accum
    | Sub -> higherOrderMathCom (lengthGreaterTwo::topTwoInteger::[]) (-) b accum
    | Mul -> higherOrderMathCom (lengthGreaterTwo::topTwoInteger::[]) ( * ) b accum
    | Div -> higherOrderMathCom (lengthGreaterTwo::topTwoInteger::divideByZero::[]) (/) b accum
    | Swap -> swap b accum
    | Concat -> concat b accum
    | Neg -> neg b accum
    | _ -> acc




let (@@) (f : 'a -> 'b) (a : 'a): 'b =
  f a

let (|>) (a : 'a) (f : 'a -> 'b): 'b =
  f a

  
type env =
 (string * const) list list

type stack = const list


type program = (stack * env)
type ('a, 'e) result =
  | Ok of 'a
  | Err of 'e

let ok  (res : 'a): ('a, 'e) result = Ok(res)
let err (err : 'e): ('a, 'e) result = Err(err)
let fold_result (f : 'a -> 'b) (g : 'e -> 'b) (res : ('a, 'e) result): 'b =
  match res with
  | Ok(o) -> f o
  | Err(e) -> g e

let and_then (f : 'a -> ('b, 'e) result) (res : ('a, 'e) result): ('b, 'e) result =
  fold_result f err res

type parse_error =
  | DivideByZero
  | UnmatchedBegin
  | EmptyStack
  | WrongDatatype
  | Place

let global (x : string) (p : program) : (program, parse_error) result =
  let (stack, e) = p
  in
  let glob = List.hd e
  in
  if List.length stack <= 0
    then
      err(Place)
  else
    let value = List.hd stack
    in
    let tup = (x, value)
    in
    let newP = (List.tl stack, (tup::glob)::(List.tl e))
    in
    ok(newP)

(*   
let findVar (acc : option) (l : (string * const) list) = 
  match acc with
  | None -> List.assoc_opt x l
  | _ -> acc
in
let v = List.fold_left findVar l None
*)
let push (h: const) (t :com list) (p : program) = 
  let (stk, e) = p
  in
  match h with
  | Var vr -> 
    let findVar (acc : const option) (l : (string * const) list) = 
    match acc with
      | None -> List.assoc_opt vr l
      | _ -> acc
    in
    let v = List.fold_left findVar None (List.rev e)
    in
    (match v with
    | Some s -> ok(((s::stk,e),t))
    | _ -> err(Place))
  | _ -> ok(((h::stk,e),t))



let local (x : string) (p : program) : (program, parse_error) result =
  let (stack, e) = p
  in
  if List.length stack <= 0
    then
      err(Place)
  else
    let loc = List.hd (List.rev e)
    in
    let value = List.hd stack
    in
    let tup = (x, value)
    in
    let newP = (List.tl stack, (tup::loc)::(List.tl e))
    in
    ok(newP)
(*
let rec parse_sexpr (st : com list) (p : program) : (program * (com list) , parse_error) result = 
    let h = List.hd st
    in
    let t = List.tl st
    in
    let (_,e) = p
    in
    match h with
    | Quit -> err(Place)
    | Begin -> parse_sexpr_list st ([],e) |> and_then @@ fun (newP, newT) -> 
      ok((newP,newT))
    | End -> err(Place)
    | Push(x) -> push x t p
    | Global(x) -> (global x p) |> and_then @@ fun newP -> ok((newP,t))
    | Local(x) -> local x p |> and_then @@ fun newP -> ok((newP,t))
    | _ -> err(Place)
  and parse_sexpr_list (st : com list) (p : program) : (program * (com list), parse_error) result =
      let h = List.hd st
      in
      match h with
      | End -> ok((p,List.tl st))
      | _ -> parse_sexpr st p
         |> and_then @@ fun (fst, st') ->
         parse_sexpr_list st'
         |> and_then @@ fun (rst, st'') ->
         ok (fst::rst, st'')

let parse (st : com list): (const list, parse_error) result =
  let rec parse_all st (p : program) =
    match st with
    | _ -> err(Place)
    | h::t ->
      match h with
      | Quit -> 
        let (stack, _) = p
        in
        ok @@ stack
      | _   -> parse_sexpr t p
                |> and_then @@ fun (newP, ts) ->
              parse_all ts newP
    in
  parse_all st ([], [[]])

*)












let interpreter (src : string) (output_file_path: string): unit =
  let commList = srcToCom src
  in
  let (b,acc) = List.fold_left interpret  (false,[]) commList
  in
  if b == true
    then
      let s = constListToString acc
      in
      printToFile s output_file_path
  else
    ()