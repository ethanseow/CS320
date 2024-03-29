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

(*
  Init Types   
*)

type const = 
  | Int of int
  | String of string
  | Var of string
  and com = 
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
  | And
  | Or
  | Not
  | Lte
  | IfThen
  | Else
  | Equal
type ('a, 'e) result =
  | Ok of 'a
  | Err of 'e
let ok  (res : 'a): ('a, 'e) result = Ok(res)
let err (err : 'e): ('a, 'e) result = Err(err)
type env = (string * const) list list
type stack = const list
type program = stack * env
type parse_err =
  | PI
type result_out = ((com list) * program)
let fold_result (f : 'a -> 'b) (g : 'e -> 'b) (res : ('a, 'e) result): 'b =
  match res with
  | Ok(o) -> f o
  | Err(e) -> g e

let and_then (f : 'a -> ('b, 'e) result) (res : ('a, 'e) result): ('b, 'e) result =
  fold_result f err res

(*
  Command Parser Utils   
*)
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

let stringToCom (h : string) (t : string list): (com, parse_err) result =
  let x = String.split_on_char ' ' inp
  in
  let c = List.hd x
  in
  if List.length x > 1 then
    match stringToConst List.nth x 1 with
    | Ok(n) -> 
      match c with
      | "Push" -> Push(n)
      | "Global" -> Global(n)
      | "Local" -> Local(n)
    | Err(p) -> err(PI)
  else
    match c with
    | "Begin" -> find_begin_end |> and_then @@ fun (com, string list) ->

    | "IfThen" -> IfThen of (com list * com list)
    | "Quit" -> Quit
    | "Pop" -> Pop
    | "Add" -> Add
    | "Concat" -> Concat
    | "Sub" -> Sub
    | "Mul" -> Mul
    | "Div" -> Div
    | "Swap" -> Swap
    | "Neg" -> Neg
    | "Concat" -> Concat
    | "End" -> End
    | "Else" -> Else
    | "And" -> And
    | "Or" -> Or
    | "Lte" -> Lte
    | "Not" -> Not
    | "Equal" -> Equal
  and find_begin_end (t : string list): ((com * string list), parse_err) result = 

let printToFile (inp : string list) (file_path : string) : unit = 
  let fp = open_out file_path in
  let lekunga = (String.concat "\n" inp)
  in
  let () = Printf.fprintf fp "%s" lekunga in
    close_out fp

let parse (src : string) : (com list, parse_err) result = 
  let cmds = String.split_on_char '\n' src
  in
  let parse_all (cmds : string list) (acc : com list): (com list, parse_err) result = 
    match cmds with
    | [] -> acc
    | h::t -> 
      stringToCom h t |> and_then @@ fun(com, string list) -> 
        
  in
  parse_all cmds []

let constListToString (c : const list) : string list =
  let helper (co : const) = 
    match co with
    | Int i -> string_of_int i
    | String s -> s
  in
  List.map helper c

(*
  Error checks   
*)
let isInteger (c : const) : bool = 
  match c with
  | Int _ -> true
  | String _ -> false

let lengthGreaterTwo (accum) : bool =
  List.length accum >= 2

let stackHasElem (st) : bool = 
  List.length st >= 1 

let topTwoInteger (accum : const list) : bool = 
  (isInteger (List.nth accum 0)) && (isInteger (List.nth accum 1))

let divideByZero (accum : const list) : bool = 
  let Int i = List.nth accum 1
  in i != 0

let topTwoBoolean (accum : const list) = 
  if topTwoInteger accum
    then
      let (Int i,Int j) = (List.nth accum 0, List.nth accum 1)
      in
      (i = 0 || i = 1) && (j = 0 || j = 1)
  else
    false

let topOneBoolean st =
  let hd = List.nth st 0
  in
  match hd with
  | Int i ->
    if i = 0 || i = 1
      then
        true
      else
        false
  | _ -> false

(*
  Command functions   
*)
let popStack (accum : stack) = 
    match accum with
      | [] -> [] 
      | _::t -> t



let higherOrderOp (f : 'a -> 'b -> 'c) (a : const) (b: const) : const = 
  let Int i = a
  in
  let Int j = b
  in
  (Int(f i j))

let bool_of_string (s : string) = 
  if s = "1" then true else false
let bool_of_int (i: int) = 
  bool_of_string (string_of_int i)

let int_of_bool (b : bool) =
  if b then 1 else 0
let bool_op (f : 'a -> 'b -> 'c) (a : const) (b : const) : const = 
    let (Int i,Int j) = (a,b)
    in
    let b1 = bool_of_int i
    in
    let b2 = bool_of_int j
    in
    Int(int_of_bool (f b1  b2))
let pop (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if stackHasElem st
    then
      let a = (popStack st)
      in
      let newStack = a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let swap (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st
    then
      let (one,two) = (List.nth st 0, List.nth st 1)
      in
      let a = popStack (popStack st)
      in
      let newStack = two::one::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let neg (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if isInteger (List.nth st 0) = true && stackHasElem st
    then
      let Int i = List.nth st 0
      in
      let a = popStack st
      in
      let newStack = (Int(-1 * i))::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)


let concat (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
    if topTwoInteger st = true || lengthGreaterTwo st = false
      then
        err(PI)
    else
      let String i = List.nth st 0
      in
      let String j = List.nth st 1
      in
      let a = popStack (popStack st)
      in
      let removeQuotes (str : string) : string = 
        Str.(global_replace (regexp "\"") "" str)
      in
      let newStack = (String("\"" ^ removeQuotes (i ^ j) ^ "\""))::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))


let findGlobalVar (x : string) (e : env) =
  let glo = List.hd e
  in
  List.assoc_opt x glo

let findVar (x: string) (e : env) (i : int) = 
  let currEnv = (List.nth e i)
  in
  List.assoc_opt x currEnv

let updateEnv (vari : string) (toChange : const) (e : env) (index : int) : env = 
    let (_, newEnv) = List.fold_left (fun acc h -> 
      let (i,newEnv) = acc
      in
      if i = index
        then
          let newH = (vari, toChange)::(List.remove_assoc vari h)
          in
          (i+1,newH::newEnv)
      else
        (i+1,h::newEnv)
    ) (0, []) e
    in
    (List.rev newEnv)

let global (tl : com list) (v : const) (p : program) : (result_out, parse_err) result = 
  let (st, e) = p
  in
  let Var vari = v
  in
  match st with
  | [] -> err(PI)
  | topStack::restStack ->
    let newEnv = updateEnv vari topStack e 0
    in 
    let newProgram = (restStack, newEnv)
    in
    ok((tl,newProgram))

let local (tl : com list) (v : const) (p : program) : (result_out, parse_err) result = 
  let (st, e) = p
  in
  let Var vari = v
  in
  match st with
  | [] -> err(PI)
  | topStack::restStack ->
    let newEnv = updateEnv vari topStack e ((List.length e) - 1)
    in 
    let newProgram = (restStack, newEnv)
    in
    ok((tl,newProgram))

let div (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st && topTwoInteger st && divideByZero st
    then
      let (one,two) = (List.nth st 0, List.nth st 1)
      in
      let a = popStack (popStack st)
      in
      let newStack = (higherOrderOp ( / ) one two)::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let mul (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st && topTwoInteger st
    then
      let (one,two) = (List.nth st 0, List.nth st 1)
      in
      let a = popStack (popStack st)
      in
      let newStack = (higherOrderOp ( * ) one two)::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let sub (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st && topTwoInteger st
    then
      let (one,two) = (List.nth st 0, List.nth st 1)
      in
      let a = popStack (popStack st)
      in
      let newStack = (higherOrderOp (-) one two)::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let add (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st && topTwoInteger st
    then
      let (one,two) = (List.nth st 0, List.nth st 1)
      in
      let a = popStack (popStack st)
      in
      let newStack = (higherOrderOp (+) one two)::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let andF (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st && topTwoBoolean st
    then
      let (a,b) = (List.nth st 0, List.nth st 1)
      in
      let a2 = popStack (popStack st)
      in
      let res = bool_op (&&) a b 
      in
      let newStack = res::a2
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let orF (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st && topTwoBoolean st
    then
      let (a,b) = (List.nth st 0, List.nth st 1)
      in
      let a2 = popStack (popStack st)
      in
      let res = bool_op (||) a b 
      in
      let newStack = res::a2
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let notF (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if List.length st >= 1 && topOneBoolean st
    then
      let Int i = List.nth st 0
      in
      let a = popStack st
      in
      let b1 = bool_of_int i
      in
      let res = Int(int_of_bool (not b1))
      in
      let newStack = res::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)
let lteF (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st && topTwoInteger st
    then
      let (one,two) = (List.nth st 0, List.nth st 1)
      in
      let a = popStack (popStack st)
      in
      let newStack = (higherOrderOp ( 
        fun a b ->
          if a <= b
            then
            int_of_bool(true)
          else
          int_of_bool(false)
      ) one two)::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let equalF (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st,e) = p
  in
  if lengthGreaterTwo st && topTwoInteger st
    then
      let (one,two) = (List.nth st 0, List.nth st 1)
      in
      let a = popStack (popStack st)
      in
      let newStack = (higherOrderOp ( 
        fun a b ->
          if a = b
            then
            int_of_bool(true)
          else
          int_of_bool(false)
      ) one two)::a
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  else
    err(PI)

let push (x : const) (tl : com list) (p : program) : (result_out, parse_err) result = 
  let (st, e) = p
  in
  match x with
  | String s -> 
    if s = "error"
      then
        err(PI)
    else
      let newStack = (x::st)
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  | Int i -> 
      let newStack = (x::st)
      in
      let newProgram = (newStack, e)
      in
      ok((tl,newProgram))
  | Var v -> 
      (
      let n = (List.length e) - 1
      in
      let rec trav (i : int) (e : env) = 
        if i < 0
          then
            None
        else
          match findVar v e i with
          | None -> trav (i-1) e
          | Some x -> (Some(x))
      in
      match trav n e with
      | None -> err(PI)
      | Some x -> ok( (tl ,((x::st),e)) )
      )

let rec execCom (cl : com list) (p : program) : (result_out, parse_err) result = 
  let nextCom = List.hd cl
  in
  let tl = List.tl cl
  in
  match nextCom with 
  | Global g -> global tl g p
  | Local l -> local tl l p
  | Push x -> push x tl p
  | Add -> add tl p
  | Sub -> sub tl p
  | Div -> div tl p
  | Mul -> mul tl p
  | Neg -> neg tl p
  | Swap -> swap tl p
  | Concat -> concat tl p
  | Pop -> pop tl p
  | And -> andF tl p
  | Or -> orF tl p
  | Lte -> lteF tl p
  | Equal -> equalF tl p
  | Not -> notF tl p
  | IfThen -> 
      let (st,e) = p
      in
      if List.length st >= 1 && topOneBoolean st
        then
          let Int b = List.hd st
          in
          let stTail = List.tl st 
          in
          if b = 1
            then
              execCond 0 tl (stTail,e)
          else
            execCond 1 tl (stTail,e)
      else
        err(PI)
  | Begin ->
    let (st,e) = p
    in
    let newE = List.rev ([]::(List.rev e))
    in
    let newP = ([],newE)
    in
    let helper (res : result_out) : (result_out, parse_err) result = 
      let (comL, newP) = res
      in
      let (s, newE) = newP
      in
      let newS = (List.hd s)::st
      in
      let newP = (newS,newE)
      in
      ok( (comL, newP) )
    in
    (execBegin (List.tl cl) newP)  |> and_then @@ helper
  and execCond (i : int) (cl : com list) (p : program) : (result_out, parse_err) result = 
    let nextCom = List.hd cl
    in
    let tl = List.tl cl
    in
    match nextCom with
    | Else -> execCond (i-1) tl p
    | Begin -> 
      if i = 0
        then
        (execCom cl p |> and_then @@ (fun (newC, newP) ->
          execCond i newC newP
        ))
      else
        (execCom cl p |> and_then @@ (fun (newC, newP) ->
          execCond i newC p
        ))
    | End -> ok((tl,p))
    | _ -> 
      if i = 1 || i = -1
        then
          execCond i tl p
      else
        execCom cl p |> and_then @@ (fun (newC, newP) -> 
        execCond i newC newP
        )
  and execBegin (cl : com list) (p : program) : (result_out, parse_err) result = 
    let nextCom = List.hd cl
    in
    let tl = List.tl cl
    in
    match nextCom with
    | End -> 
      let (st, e) = p
      in
      let (_,trimmedE) = 
      (List.fold_left 
        (
          fun acc h ->
          let (i,l) = acc
          in
          if i = (List.length e)- 1
            then
            (i+1,l)
          else
            (i+1,h::l) 
        )
      (0,[]) e)
      in
      let newE : env = List.rev trimmedE
      in
      if List.length st < 1
        then
          err(PI)
      else
        let ret : stack = (List.hd st)::[]
        in
        let newP : program = (ret,newE)
        in
        ok( (tl , newP) )
    | _ -> execCom cl p |> and_then @@ fun(newCl,newP) -> 
      execBegin newCl newP
let eval (commList : com list) = 
  let rec eval_all (cl : com list) (p : program) = 
    let nextCom = List.hd cl
    in
    match nextCom with
    | Quit -> 
      let (st,e) = p
      in
      ok(p)
    | _ -> (execCom cl p) |> and_then @@ (fun (newCl, newP) ->
      eval_all newCl newP) 
  in
  eval_all commList ([], ([]::[]::[]))

let interpreter (src : string) (output_file_path: string): unit =
  let commList = parse src
  in
  let outp = eval commList
  in
  match outp with
  | Err _ -> printToFile (("\"Error\"")::[]) output_file_path
  | Ok (st,p) -> 
    let strStk = constListToString st
    in
    printToFile strStk output_file_path
  (*
  let (b,acc) = List.fold_left interpret  (false,[]) commList
  in
  if b == true
    then
      let s = constListToString acc
      in
      printToFile s output_file_path
  else
    ()
  *)