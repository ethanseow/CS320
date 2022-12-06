type const = 
  | Int of int
  | String of string
  | Var of string
  | Clo of closure
  | Left of const 
  | Right of const
  | TupleConst of (const list)
  and com = 
  | Quit
  | Get of int
  | Case of (com list * com list)
  | Fun of (closure list)
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
  and closure = (string * string * com list)