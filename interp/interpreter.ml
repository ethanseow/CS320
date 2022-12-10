#load "str.cma";;

(*
  Init Types   
*)
  type const = 
  | FatalError
  | Int of int
  | String of string
  | Var of string
  | Clo of (string * string * com list)
  (* mutclo contains the other mutually rec closures and is applied to funf*)
  | MutClo of (string * string * com list * (unit -> (string * const) list))
  | Left of const 
  | Right of const
  | TupleConst of (const list)
  | QuitConst
  | ReturnConst
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
  | EmptyStackInReturn
  | NoEndStatementOnFun
  | EndNotSkipped
  | ElseNotSkipped
  | NotEnoughForTuple
  | EmptyStackInCall
  | Unmatched
  | MissingReturnStatement
  | MissingReturnStatementMut
  | EmptyStackOrNotTuple
  | OutsideTuple
  | NotCallableClosure
  | NotInClosure
  | NotBooleanOrEmptyStack
  | EmptyStackInBegin
  | EmptyStackInCase
  | NotLeftRightCase
  | EmptyStackInLocal
  | EmptyStackInGlobal
  | EmptyStackInInjl
  | EmptyStackInInjr
  | PI
  | NoQuitStatement
  | VariableNotFound of (const * env)
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
let regexp3 = Str.regexp "[a-zA-Z]+\\([0-9]\\|\\_\\)?$"
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
    | "Return" -> ok((Return,t))
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
          let Clo(prevCloHeader,prevCloArg,_) = List.hd cloAcc 
          in
          let newRealClo = Clo(prevCloHeader,prevCloArg, (List.rev acc))
          in
          let newCloAcc = newRealClo::(List.tl cloAcc)
          in
          ok( (newCloAcc  ,t) )
      | "Mut" -> 
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

(* helper execution commands *)
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
let pop (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let swap (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let neg (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)


let concat (p : program) : (program, parse_err) result = 
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
      ok((newProgram))


let div (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let mul (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let sub (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let add (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let andF (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let orF (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let notF (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)
let lteF (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)

let equalF (p : program) : (program, parse_err) result = 
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
      ok((newProgram))
  else
    err(PI)
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
      | None -> err(VariableNotFound(x,e))
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

let addLocalEnv (cl : env) : env =
  List.rev ([]::(List.rev cl))

let rec popN' i n stk =
  if i == n then
    stk
  else
    popN' (i+1) n (List.tl stk)

let popN n stk = popN' 0 n stk

let rec funF (cloList : const list) (prog : program) : (program, parse_err) result = 
  let (st,e) = prog
  in
  let restOfMut = (fun () -> (
    match funF cloList ([],[]::[]) with
    | Err(_) -> []
    | Ok((_,newE)) -> (List.hd (List.rev newE))
  ))
  in
  (* put all functions into local env *)
  let helper (acc : env) (clo : const) : env = 
    match clo with
    | Clo(funcName, funcArg, commands) -> 
      let vari = Var(funcName)
      in
      let newClo = MutClo(funcName,funcArg, commands, restOfMut)
      in
      let updatedE = (local vari ((newClo::[]),acc))
      in
      match updatedE with
      (* impossible to have error *)
      | Err(_) -> []
      | Ok((_,newE)) -> newE 
    | _ -> []
  in
  let addedFunToEnv = List.fold_left helper e cloList  
  in
  ok((st,addedFunToEnv))
    

let injl (prog : program) : (program, parse_err) result = 
  let (st,e) = prog
  in
  if (stackHasElem st) then
    let left = Left(List.hd st)
    in
    let newSt = left::(List.tl st)
    in
    ok(((newSt), e ))
  else
    err(EmptyStackInInjl)
let injr (prog : program) : (program, parse_err) result = 
  let (st,e) = prog
  in
  if (stackHasElem st) then
    let right = Right(List.hd st)
    in
    let newSt = right::(List.tl st)
    in
    ok(((newSt), e ))
  else
    err(EmptyStackInInjr)

let case (left : com list) (right : com list) (evalInner) (prog : program) = 
  let (st,e) = prog
  in
  if (stackHasElem st) then
    match List.hd st with
    | Left(c)  -> evalInner left ((c::(List.tl st)),e)
    | Right(c)  -> evalInner right ((c::(List.tl st)),e)
    | _ -> err(NotLeftRightCase)
  else
    err(EmptyStackInCase)


let tup (n : int) (prog : program) =
  let (st,e) = prog
  in
  if List.length st >= n then
    let helper acc h = 
      if List.length acc < n then
        h::acc
      else
        acc
    in
    let tuple = TupleConst(List.fold_left helper [] st)
    in
    let newStack = tuple::(popN n st)
    in
    ok((newStack,e))
  else
    err(NotEnoughForTuple)

let getTup (n : int) (prog : program) = 
  let (st,e) = prog
  in
  if (stackHasElem st) then
    match List.hd st with
    | TupleConst(cl) -> 
      if (List.length cl) - 1 >= n then
        ok(((List.nth cl n)::st, e))
      else
        err(OutsideTuple)
    | _ -> err(EmptyStackOrNotTuple)
  else
    err(EmptyStackOrNotTuple)

let callF (prog : program) (evalInner) = 
  let (st,topE) = prog
  in
  let helper funcArg comlist st e = 
        (
        let funcVar = Var(funcArg)
        in
        let funcVarValue = List.nth st 1
        in
        (* new env of just global and an empty local for the function with mut bindings *)
        let funcEnv = local funcVar ([funcVarValue],e)
        in
        match funcEnv with
        | Ok((_,e')) -> 
          evalInner comlist ([],e') |> and_then @@ (fun (newS,newE) -> 
              (* st contains the closure and argument *)
              let st' = popN 2 st
              in
              let newProg = ( (List.nth newS 1)::st', ((List.hd newE)::(List.tl topE)) )
              in
              ok(newProg)
            )
        | _ -> err(PI)
        )
  (* helper does not need to know about t or clo, we can move it outside*)
  in
  if List.length st >= 2 then
    match st with
    | clo::t ->
      match clo with
      | MutClo(_,funcArg,comlist, otherClosures) -> 
        (* inside of a func only head *)
        let newE : env = ((List.hd topE)::(otherClosures())::[])
        in
        helper funcArg comlist st newE
      | _ -> err(NotCallableClosure)
  else
    err(EmptyStackInCall)

let returnF (prog : program) =
  let (st,e) = prog
  in
  match st with
  | [] -> err(EmptyStackInReturn)
  | h::_ -> (
    (* used to bubble up return if inside begin/ifth *)
    ok((ReturnConst::h::[],e))
  )

let rec evalInner (src : com list) (prog : program): (program, parse_err) result = 
  match src with
  | [] -> ok(prog)
  | h::t -> (
    let (st,e) = prog
    in
    match h with
    | Quit ->
      (* used to quit if quit is inside begin/end*)
      let newSt = QuitConst::st
      in
      ok((newSt,e))
    | Return -> 
      (* used to bubble up return if return is inside begin/ift *)
      if List.length st > 0 then
        let newSt = ReturnConst::(List.hd st)::[]
        in
        (* ok in evalInner/eval exits out of current com list *)
        ok ((newSt,e))
      else
        err(EmptyStackInReturn)
    | _ -> eval_all src prog |> and_then @@ fun newProg ->
        let (st,e) = newProg
        in
        match st with
        | h::_ ->
          (
            match h with
          | QuitConst -> ok((st,e))
          | ReturnConst -> ok((st,e))
          | _ -> evalInner t newProg
          )
        | _ -> evalInner t newProg
  )
  and eval_all (src : com list) (prog : program) : (program, parse_err) result = 
  let (st,e) = prog
  in
  let h = List.hd src
  in
  match h with
  | Begin (comlist) ->
    let newE = List.rev ([]::(List.rev e))
    in
    let newP = ([],newE)
    in
    evalInner comlist newP |> and_then @@ fun(newS,retE) ->
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
            evalInner ift (stTail,e) |> and_then @@ fun newP -> ok(newP)
          else
            evalInner els (stTail,e) |> and_then @@ fun newP -> ok(newP)
      else
        err(NotBooleanOrEmptyStack)
  | Push(x) -> push x prog
  | Global(v) -> global v prog
  | Local(v) -> local v prog
  | Pop -> pop prog
  | Add -> add prog
  | Sub -> sub prog
  | Mul -> mul prog
  | Div -> div prog
  | Swap -> swap prog
  | Neg -> neg prog
  | Concat -> concat prog
  | And -> andF prog
  | Or -> orF prog
  | Not -> notF prog
  | Lte -> lteF prog
  | Equal -> equalF prog
  | Fun(cloList) -> funF cloList prog
  | InjL -> injl prog
  | InjR -> injr prog
  | Case(left,right) -> case left right evalInner prog
  | Tuple(n) -> tup n prog 
  | Get(n) -> getTup n prog
  | Call -> callF prog evalInner
let rec eval (src : com list) (prog : program): (program, parse_err) result = 
  match src with
  | [] -> err(NoQuitStatement)
  | h::t -> (
    match h with 
    | Quit -> ok(prog)
    | Return -> err(NotInClosure)
    | _ ->
      (* quit const bubbles up *)
      eval_all src prog |> and_then @@ (fun newProg ->
        let (st,e) = newProg
        in
        match st with
        | h::_ ->
          (
            match h with
          | QuitConst -> ok(( (List.tl st) , e))
          | ReturnConst -> err(NotInClosure)
          | _ -> eval t newProg
          )
        | _ -> eval t newProg)
  )

let rec stackToFile (st : const list) (delim : string): string list = 
  let helper acc h : string list = 
    let out = (match h with 
    | Int i -> string_of_int i
    | String s -> s
    | MutClo(funcName,funcArg,_,_) -> 
      "Clo (" ^ funcName ^ ", " ^ funcArg ^ ")"
    | Clo(funcName,funcArg,_) -> 
      "Clo (" ^ funcName ^ ", " ^ funcArg ^ ")"
    | Left(c) -> "Left " ^ (List.hd (stackToFile [c] delim))
    | Right(c) -> "Right " ^ (List.hd (stackToFile [c] delim))
    | TupleConst(c) -> (
      let rec helper acc h = acc ^ h ^ ", "
      in
      let tuplized = List.fold_left helper "(" (stackToFile c "")
      in
      String.sub tuplized 0 ((String.length tuplized) - 2) ^ ")"
      ))
    
    in
    (out ^ delim)::acc
  in
  List.rev (List.fold_left helper [] st)
let printToFile (inp : string list) (file_path : string) : unit = 
  let fp = open_out file_path in
  let lekunga = (String.concat "\n" inp)
  in
  let () = Printf.fprintf fp "%s" lekunga in
    close_out fp

let interpreter (src: string) (output_file_path : string) = 
  match eval (parse src) ([],([]::[]::[])) with
  | Ok(st,_) -> (printToFile (stackToFile st "") output_file_path)
  | Err(e) ->
    match e with
    | NoQuitStatement -> printToFile (""::[]) (output_file_path)
    | _ -> printToFile ("\"Error\""::[]) (output_file_path);;

let b = "Push 55
Local x
Push x
Begin
Push 3
Push 5
Global x
Push 7
Push x
End
Push x
Quit";;


(* testing *)
(* page 18 example 1 *)
let a = "Push 1
Push 2
Begin
Push 3
Push 7
Push 4
End
Push 5
Push 6
Quit";;

(* page 18 example 2 - expected error*)
let b = "Push 3
Begin
Pop
Push 7
End
Quit";;

(* expected is "Error" *)
let c = "Push 10
Push \"abc\"
Push 1
Push 0
And
Or
Quit";;


(* expected is 1*)
let d = "Push 1
Push 0
And
Push 1
Or
Not
Push 100
Push 100
Equal
Or
Quit";;

(* expected xyz 10 Correct *)
let e = "Push 10
Global x
Push \"abc\"
Global s
Push 20
Global z
Begin
Push \"burger\"
Local z
Push x
Push 20
Equal
IfThen
Push \"def\"
Global s
Else
Push \"xyz\"
Global s
End
Push 50
Local x
Begin
Push x
Push 40
Lte
IfThen
Push \"Correct\"
Else
Push \"Incorrect\"
End
End
Push \"spaghetti\"
Global z
End
Push x
Push s
Quit";;


let f = "Fun isOdd x
Push 3
Return
Mut isEven x
Push 5
Return
End
Push isOdd
Push isEven
Quit";;

(* should give Right and the closure *)
let g = "Fun foo x
Return
End
Push foo
InjR
Quit";;

(* should give error *)
let h = "InjR
Quit";;

(* should just give 5*)
let i = "Push 5
InjL
CaseLeft
Right
Add
End
Quit";;

(* should be error *)
let j = "Push 5
InjR
CaseLeft
Right
Add
End
Quit";;

(* should be Bobhello*)
let k = "Push \"hello\"
InjR
CaseLeft
Push 1
Add
Right
Push \"Bob\"
Concat
End
Quit"

(* should be tulpe of 1 two 3*)
let l = "Push 1
Push \"two\"
Push 3
Tuple 3
Quit";;

(* should be tuple(clo,5) 20*)
let m = "Fun bar x
Return
End
Push 20
Push bar
Push 5
Tuple 2
Quit";;

let n = "Push \"there\"
Push \"hi\"
Tuple 2
Get 0
Swap
Get 1
Swap
Pop
Concat
Quit";;

(* should just be 8*)
let o = "Fun f1 x
Push x
Return
Mut f2 x
Push x
Push 2
Mul
Local x
Push x
Push f1
Call
Return
Mut f3 x
Push x
Push 1
Add
Local x
Push x
Push f2
Call
Return
End
Push 3
Push f3
Call
Quit";;

(* error *)
let p = "Fun f1 x
Push y
Return
Mut f2 x
Push x
Push 2
Mul
Local x
Push x
Push f1
Call
Return
Mut f3 y
Push y
Push 1
Add
Local x
Push x
Push f2
Call
Return
End
Push 3
Push f3
Call
Quit";;

(* 11 22 tuple*)
let q = "Fun regular x
Push 11
Push x
Tuple 2
Return
End
Push 22
Push regular
Call
Quit";;

(* 46 *)
let r = "Fun odd x
Push x
Push 2
Mul
Local x
Push x
Push 46
Equal
IfThen
Push x
Return
Else
Push x
Push even
Call
Return
End
Mut even x
Push 1
Push x
Add
Local x
Push x
Push odd
Call
Return
End
Push 5
Push odd
Call
Quit";;


(* 6 *)
let s = "Fun numOfStepsToOne x
Push numOfSteps
Push 1
Add
Global numOfSteps
Push x
Push 1
Add
Local x
Push x
Push divideByTwo
Call
Return
Mut divideByTwo x
Push numOfSteps
Push 1
Add
Global numOfSteps
Push 2
Push x
Div
Local x
Push x
Push 1
Equal
IfThen
Push numOfSteps
Return
Else
Push x
Push numOfStepsToOne
Call
Return
End
End
Push 0
Global numOfSteps
Push 5
Push numOfStepsToOne
Call
Quit"


(* 100 *)
let t = "Fun snack laddoo
Push laddoo
Push 100
Mul
Local cal
Push cal
Push calories
Call
Return
Mut calories cal
Push 9
Push cal
Div
Local g
Push g
Push sugar
Call
Return
Mut sugar g
Push g
Return
End
Push 9
Push snack
Call
Quit";;
let test = "Fun f1 x
Push x
Push 2
Add
Local x
Push x
Push f2
Call
Return
Mut f2 x
Push x
Push 3
Add
Return
End
Push 3
Push f1
Call
Quit";;


let test2 = "Push 3
InjR
CaseLeft
Push 4
Add
Right
Push 5
Add
End";;

let test3 = "Push \"ManyFuns\"
Fun mystery1 x
Push x
Push mystery2
Call
Push 2
Mul
Return
End
Fun mystery2 x
Push x
Push 1
Add
Return
End
Push 4
Push mystery1
Call
Quit"

let test4 = "Push 1
Push 3
Tuple 0
Quit"

let test5 = "Fun loop n
Push 0
Push n
Equal
IfThen
Tuple 0
Return
Else
Push 1
Push n
Sub
Push loop
Call
Push n
Tuple 2
Return
End
End
Push 5
Push loop
Call
Quit";;

let test6 = "Fun add n
Push 0
Push n
Lte
IfThen
Push n
Return
Else
Push 1
Push n
Sub
Push add
Call
End
Push n
Tuple 2
Return
End
Push 3
Push add
Call
Quit";;

let test7 = "Push 5
Local x
Fun plus n
Push n
Push 1
Add
Return
End
Push x
Push plus
Call
Push x
Quit";;

let parse2 (src : string) = 
  let cmds = String.split_on_char '\n' src
  in
  let rec parse_all (cmds : string list) (acc : com list): (com list, parse_err) result = 
    match cmds with
    | [] -> ok(acc)
    | _::_ -> 
      stringToCom cmds |> and_then @@ fun(com, cmds) -> 
        parse_all (cmds) (com::acc)
  in parse_all cmds [];;
(*
eval (parse a) ([],([]::[]::[]));;
eval (parse b) ([],([]::[]::[]));;
eval (parse c) ([],([]::[]::[]));;
eval (parse d) ([],([]::[]::[]));;
eval (parse e) ([],([]::[]::[]));;
eval (parse g) ([],([]::[]::[]));;
eval (parse h) ([],([]::[]::[]));;
eval (parse i) ([],([]::[]::[]));;
eval (parse k) ([],([]::[]::[]));;
eval (parse l) ([],([]::[]::[]));;
eval (parse m) ([],([]::[]::[]));;
eval (parse n) ([],([]::[]::[]));;
eval (parse o) ([],([]::[]::[]));;
eval (parse p) ([],([]::[]::[]));; <- returns 3 - need to fix traversal of push
*) 

(*
let out = match eval (parse test) ([],([]::[]::[])) with
| Ok(st,_) -> st
| _ -> [];;

let c = List.nth out 0;;

let MutClo(_,_,_,f) = c;;
*)