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

let execCom (cl : com list) (p : program) : (result_out, parse_err) result = 
  let nextCom = List.hd cl
  in
  let tl = List.tl cl
  in
  match nextCom with 
    (*
  | Push p -> 
  | Begin ->
  | End ->
  | Local l -> 
    *)
  | Global g -> global tl g p
  | Local l -> local tl l p
  | Push x -> push x tl p
  | Add -> add tl p

let parse (commList : com list) = 
  let rec parse_all (cl : com list) (p : program) = 
    let nextCom = List.hd cl
    in
    match nextCom with
    | Quit -> 
      let (st,e) = p
      in
      ok(st)
    | _ -> (execCom cl p) |> and_then @@ (fun (newCl, newP) ->
      parse_all newCl newP) 
  in
  parse_all commList ([], ([]::[]::[]))

let interpreter (src : string) (output_file_path: string): unit =
  let commList = srcToCom src
  in
  let outp = parse commList
  in
  match outp with
  | Err _ -> printToFile (("\"Error\"")::[]) output_file_path
  | Ok st -> 
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