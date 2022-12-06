#load "str.cma";;

(*
  Init Types   
*)
  type const = 
  | Int of int
  | String of string
  | Var of string
  | Clo of (string * string * com list)
  | Left of const 
  | Right of const
  | TupleConst of (const list)
  and com = 
  | Quit
  | Get of int
  | Case of (com list * com list)
  | Fun of (const list)
  | Push of const
  | Tuple of int
  | Pop
  | Add
  | Sub
  | Call
  | Mul
  | Div
  | Swap
  | Neg
  | Concat
  | Begin of (com list)
  | End
  | Global of const
  | Local of const
  | And
  | Or
  | Not
  | Lte
  | IfThen of ifthen
  | Equal
  | Return
  | InjL
  | InjR
  and ifthen = (com list * com list)
type union 
type ('a, 'e) result =
  | Ok of 'a
  | Err of 'e
let ok  (res : 'a): ('a, 'e) result = Ok(res)
let err (err : 'e): ('a, 'e) result = Err(err)
type env = (string * const) list list
type stack = const list
type program = stack * env
type parse_err =
  | NotValidConst
  | NoEndStatementOnBegin
  | NoEndStatementOnIf
  | NoEndStatementOnLR
  | NoEndStatementOnFun
  | EndNotSkipped
  | ElseNotSkipped
  | Unmatched
  | MissingReturnStatement
  | MissingReturnStatementMut
  | NotInClosure
  | NotBooleanOrEmptyStack
  | EmptyStackInBegin
  | EmptyStackInLocal
  | EmptyStackInGlobal
  | PI
  | NoQuitStatement
  | VariableNotFound
type result_out = ((com list) * program)
let fold_result (f : 'a -> 'b) (g : 'e -> 'b) (res : ('a, 'e) result): 'b =
  match res with
  | Ok(o) -> f o
  | Err(e) -> g e

let and_then (f : 'a -> ('b, 'e) result) (res : ('a, 'e) result): ('b, 'e) result =
  fold_result f err res
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
  Command Parser Utils   
*)
let regexp = Str.regexp "[-0-9]+$"
let regexp2 = Str.regexp "\\\"[A-Za-z]+\\\"$"

(* for variables - may need to change due to f3333 being possible*)
let regexp3 = Str.regexp "[a-z]+\\([0-9]\\|\\_\\)?$"
let stringToConst (str : string ) : (const,parse_err) result =
  if Str.string_match regexp str 0
    then
      let x = int_of_string str
      in
      ok(Int(x))
  else
    if Str.string_match regexp2 str 0
      then
        ok(String(str))
    else
      if Str.string_match regexp3 str 0
        then
          ok(Var(str))
      else
        err(NotValidConst)

let rec stringToCom (cmds : string list): ((com * string list), parse_err) result =
  let x = String.split_on_char ' ' (List.hd cmds)
  in
  let t = List.tl cmds
  in
  let c = List.hd x
  in
  match List.length x with
  | 3 ->
    (
      if c = "Fun" then
        find_fun cmds [] [] |> and_then @@ ( fun(cloList, cmds) ->
          let closure = Fun(cloList)
          in
          ok( (closure, cmds)) )
        
      else
        err(Unmatched)
    )
  | 2 -> 
    (
      match stringToConst (List.nth x 1) with
      | Ok(n) -> 
        (
          match c with
          | "Push" -> ok((Push(n),t))
          | "Global" -> ok((Global(n),t))
          | "Local" -> ok((Local(n),t))
          | "Tuple" -> 
            let Int i = n
            in
            ok( (Tuple(i),t) )
          | "Get" ->
            let Int i = n
            in
            ok( (Get(i),t) )
        )
      | Err(e) -> err(NotValidConst)
    )
  | 1 ->
    (
    match c with
    | "Begin" -> (find_begin_end t []) |> and_then @@ fun (coms, cmds) ->
      ok( (Begin(coms), cmds) )
    | "IfThen" -> (find_ifthen_end t [] [])|> and_then @@ fun (branches, cmds) ->
      ok( (IfThen(branches), cmds) )
    | "CaseLeft" -> (find_lr t [] [])|> and_then @@ fun (branches, cmds) ->
      ok( (Case(branches), cmds) )
    | "Quit" -> ok((Quit,t))
    | "Pop" -> ok((Pop,t))
    | "Add" -> ok((Add,t))
    | "Concat" -> ok((Concat,t))
    | "Sub" -> ok((Sub,t))
    | "Mul" -> ok((Mul,t))
    | "Div" -> ok((Div,t))
    | "Swap" -> ok((Swap,t))
    | "Neg" -> ok((Neg,t))
    | "End" -> err(EndNotSkipped)
    | "Else" -> err(ElseNotSkipped)
    | "Return" -> err(NotInClosure)
    | "And" -> ok((And,t))
    | "InjL" -> ok((InjL,t))
    | "InjR" -> ok((InjR,t))
    | "Or" -> ok((Or,t))
    | "Lte" -> ok((Lte,t))
    | "Not" -> ok((Not,t))
    | "Equal" -> ok((Equal,t))
    | "Call" -> ok((Call,t))
    )
  and find_begin_end (cmds : string list) (acc : com list): ((com list * string list), parse_err) result = 
    match cmds with
    | [] -> err(NoEndStatementOnBegin)
    | h::t -> 
      let x = List.hd (String.split_on_char ' ' h)
      in
      match x with
      | "End" -> 
        ok( ( (List.rev acc) , t ) )
      | _ ->
        stringToCom cmds |> and_then @@ (fun (com,rest) ->
        find_begin_end rest (com::acc) )
  and find_ifthen_end (cmds : string list) (ift : com list) (els : com list) : ((ifthen * string list), parse_err) result = 
    match cmds with
    | [] -> err(NoEndStatementOnIf)
    | h::t -> 
      let x = List.hd(String.split_on_char ' ' h)
      in
      match x with 
      | "End" -> 
        (* swapped because else swaps the two arguments*)
        let branch : ifthen = ( (List.rev els) , (List.rev ift ) )
        in
        ok( ( branch, t) )
      | "Else" -> 
        (* put populated if branch to the side and populate the els branch*)
        find_ifthen_end t els ift
      | _ ->
        stringToCom cmds |> and_then @@ fun (com,rest) ->
        (* first argument always gets populated *)
        find_ifthen_end rest (com::ift) els
  and find_fun (cmds : string list) (acc : com list) (cloAcc : const list): ((const list * string list), parse_err) result = 
    match cmds with
    | [] -> err(NoEndStatementOnFun)
    | h::t -> 
      let x = List.hd(String.split_on_char ' ' h)
      in
      match x with
      | "Fun" ->
        let funcHeader = List.nth (String.split_on_char ' ' h) 1
        in
        let funcArg = List.nth (String.split_on_char ' ' h) 2 
        in
        let newClo = (Clo(funcHeader,funcArg,[])::cloAcc)
        in
        find_fun t acc newClo
      | "Return" ->
        find_fun t (Return::acc) cloAcc
      | "End" -> 
        if List.length acc = 0 || ((List.hd acc) <> Return) then
          err(MissingReturnStatement)
        else
          let Clo(prevCloHeader,prevCloArg,_) = List.hd cloAcc 
          in
          let newRealClo = Clo(prevCloHeader,prevCloArg, (List.rev acc))
          in
          let newCloAcc = newRealClo::(List.tl cloAcc)
          in
          ok( (newCloAcc  ,t) )
      | "Mut" -> 
        if List.length acc = 0 || ((List.hd acc) <> Return) then
          err(MissingReturnStatementMut)
        else
          let Clo(prevCloHeader,prevCloArg,_) = List.hd cloAcc 
          in
          let newRealClo = Clo(prevCloHeader,prevCloArg,(List.rev acc))
          in
          let newCloAcc = newRealClo::(List.tl cloAcc)
          in
          let funcHeader = List.nth (String.split_on_char ' ' h) 1
          in
          let funcArg = List.nth (String.split_on_char ' ' h) 2 
          in
          find_fun t [] (Clo(funcHeader,funcArg,[])::newCloAcc)
      | _ ->
        stringToCom cmds |> and_then @@ fun (com,rest) ->
        find_fun rest (com::acc) cloAcc
  and find_lr (cmds : string list) (left : com list) (right : com list) : ((ifthen * string list), parse_err) result = 
    match cmds with
    | [] -> err(NoEndStatementOnLR)
    | h::t -> 
      let x = List.hd(String.split_on_char ' ' h)
      in
      match x with 
      | "End" -> 
        (* swapped because else swaps the two arguments*)
        let branch : ifthen = ( (List.rev right) , (List.rev left ) )
        in
        ok( ( branch, t) )
      | "Right" -> 
        (* put populated if branch to the side and populate the els branch*)
        find_ifthen_end t right left
      | _ ->
        stringToCom cmds |> and_then @@ fun (com,rest) ->
        (* first argument always gets populated *)
        find_lr rest (com::left) right
let parse (src : string) = 
  let cmds = String.split_on_char '\n' src
  in
  let rec parse_all (cmds : string list) (acc : com list): (com list, parse_err) result = 
    match cmds with
    | [] -> ok(acc)
    | _::_ -> 
      stringToCom cmds |> and_then @@ fun(com, cmds) -> 
        parse_all (cmds) (com::acc)
  in
  match parse_all cmds [] with
  | Ok(p) -> List.rev p
  | Err(e) -> []
let findVar (x: string) (e : env) (i : int) = 
  let currEnv = (List.nth e i)
  in
  List.assoc_opt x currEnv
let push (x : const) (p : program) : (program, parse_err) result = 
  let (st, e) = p
  in
  let newStack = (x::st)
  in
  let newProgram = (newStack, e)
  in
  match x with
  | String s -> 
      ok(newProgram)
  | Int i -> 
      ok(newProgram)
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
      | None -> err(VariableNotFound)
      | Some x -> ok((x::st),e)
      )
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
let global (v : const) (p : program) : (program, parse_err) result = 
  let (st, e) = p
  in
  let Var vari = v
  in
  match st with
  | [] -> err(EmptyStackInGlobal)
  | topStack::restStack -> 
    let newEnv = updateEnv vari topStack e 0
    in 
    let newProgram = (restStack, newEnv)
    in
    ok(newProgram)

let local (v : const) (p : program) : (program, parse_err) result = 
  let (st, e) = p
  in
  let Var vari = v
  in
  match st with
  | [] -> err(EmptyStackInLocal)
  | topStack::restStack ->
    let newEnv = updateEnv vari topStack e ((List.length e) - 1)
    in 
    let newProgram = (restStack, newEnv)
    in
    ok(newProgram)

let removeLocalEnv (cl : env) : env =
  List.rev (List.tl (List.rev cl))
let rec eval_all (src : com list) (prog : program) : (program, parse_err) result = 
  let (st,e) = prog
  in
  let h = List.hd src
  in
  match h with
  | Quit -> ok(prog)
  | Begin (comlist) ->
    let newE = List.rev ([]::(List.rev e))
    in
    let newP = ([],newE)
    in
    eval_all comlist newP |> and_then @@ fun(newS,retE) ->
      if List.length newS < 1 then
        err(EmptyStackInBegin)
      else
        let top = List.hd newS
        in
        let newE = removeLocalEnv retE
        in
        (* Need to think about how to deal with the given new environment - remove top of the stack *)
        let newP = ((top::st), newE)
        in
        ok(newP)
  | IfThen(ift,els)-> 
      if List.length st >= 1 && topOneBoolean st
        then
          let Int b = List.hd st
          in
          let stTail = List.tl st 
          in
          if b = 1 then
            eval_all ift (stTail,e) |> and_then @@ fun newP -> ok(newP)
          else
            eval_all els (stTail,e) |> and_then @@ fun newP -> ok(newP)
      else
        err(NotBooleanOrEmptyStack)
  | Push(x) -> push x prog
  | Global(v) -> global v prog
  | Local(v) -> local v prog





let rec eval (src : com list) (prog : program): (program, parse_err) result = 
  match src with
  | [] -> err(NoQuitStatement)
  | h::t -> (
    if h = Quit then
      ok(prog)
    else
      eval_all src prog |> and_then @@ fun newProg ->
        eval t newProg
  )

(* helper execution commands *)
(*
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

let notF (tl : com list) (p : program) : (program, parse_err) result = 
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
let lteF (tl : com list) (p : program) : (program, parse_err) result = 
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

let equalF (tl : com list) (p : program) : (program, parse_err) result = 
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

let push (x : const) (tl : com list) (p : program) : (program, parse_err) result = 
  let (st, e) = p
  in
  match x with
  | String s -> 
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

(* execution*)

let rec execCom (cl : com list) (p : program) : (program, parse_err) result = 

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
  | IfThen(ift,els)-> 
      let (st,e) = p
      in
      if List.length st >= 1 && topOneBoolean st
        then
          let Int b = List.hd st
          in
          let stTail = List.tl st 
          in
          if b = 1 then
            execCom ift p |> and_then @@ fun newP -> ok(newP)
          else
            execCom els p |> and_then @@ fun newP -> ok(newP)
      else
        err(NotBooleanOrEmptyStack)
  | Begin(cmds)->
    let (st,e) = p
    in
    let newE = List.rev ([]::(List.rev e))
    in
    let newP = ([],newE)
    in
    execCom cmds newP |> and_then @@ fun(newS,_) ->
      if List.length newS < 1 then
        err(EmptyStackInBegin)
      else
        let top = List.hd newS
        in
        let newP = ((top::st), e)
        in
        ok(newP)

        let eval (commList : com list) = 
  let rec eval_all (cl : com list) (p : program) = 
    let nextCom = List.hd cl
    in
    match nextCom with
    | Quit -> 
      let (st,e) = p
      in
      ok(p)
    | _ -> (execCom cl p) |> and_then @@ (fun newP ->
      eval_all newCl newP) 
  in
  eval_all commList ([], ([]::[]::[]))
*)

let q = "Push 5
Global z
Begin
Push 3
Global x
Push 1
IfThen
Push 3
Else
Push 5
End
End
Begin
Push 68
End
Quit";;
eval (parse q) ([],([]::[]::[]))