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
  | Fun of (string * string * com list)
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
      if c = "Fun" || c = "Mut" then
        let funcHeader = List.nth x 1
        in
        let funcArg = List.nth x 2
        in
        find_fun t [] |> and_then @@ ( fun(coms, cmds) ->
          let closure = Fun(funcHeader, funcArg, coms)
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
  and find_fun (cmds : string list) (acc : com list) : ((com list * string list), parse_err) result = 
    match cmds with
    | [] -> err(NoEndStatementOnFun)
    | h::t -> 
      let x = List.hd(String.split_on_char ' ' h)
      in
      match x with
      | "Return" ->
        find_fun t (Return::acc) 
      | "End" -> 
        if List.length acc = 0 || ((List.hd acc) <> Return) then
          err(MissingReturnStatement)
        else
          ok( ( (List.rev acc), t) )

      | "Mut" -> 
        if List.hd acc <> Return then
          err(MissingReturnStatementMut)
        else
          ok( ( (List.rev acc), cmds) )
      | _ ->
        stringToCom cmds |> and_then @@ fun (com,rest) ->
        find_fun rest (com::acc) 
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
let parse (src : string) : (com list,parse_err) result = 
  let cmds = String.split_on_char '\n' src
  in
  let rec parse_all (cmds : string list) (acc : com list): (com list, parse_err) result = 
    match cmds with
    | [] -> ok(acc)
    | _::_ -> 
      stringToCom cmds |> and_then @@ fun(com, cmds) -> 
        parse_all (cmds) (com::acc)
  in
  parse_all cmds []

let a = "Push 5
InjL
CaseLeft
Push 3
CaseLeft
Push f3
Right
Push 5
End
Push 4
Right
Add
End
Tuple 3
Get 2
Quit
Call";;
parse a;;