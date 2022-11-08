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

let regexp = Str.regexp "[0-9]+$"
let stringToConst (str : string ) : const =
  if Str.string_match regexp str 0
    then
      let x = int_of_string str
      in
      Int(x)
  else
    String(str)

let stringToCom (inp : string list) : com =
  let comm = List.nth inp 0
  in
  match comm with
  | "Quit" -> Quit
  | "Push" -> 
    let v = stringToConst (List.nth inp 1)
    in
    Push(v)
  | "Pop" -> Pop
  | "Add" -> Add
  | "Concat" -> Concat
  | "Sub" -> Sub
  | "Mul" -> Mul
  | "Div" -> Div
  | "Swap" -> Swap
  | "Neg" -> Neg
  | "Concat" -> Concat

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

let printToFile (inp : string list) (file_path : string) : unit = 
  let fp = open_out file_path in
  let lekunga = (String.concat "\n" inp)
  in
  let () = Printf.fprintf fp "%s" lekunga in
    close_out fp
(*When it comes to parsing src, you should find it useful that fold_left can be
  defined and used with strings (like String.fold_left in new OCaml version).
  See String.get. These are suggestions though and you are welcome
  to use what you want :)  *)

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

let interpret (acc : (bool * (const list))) (comm : com) : (bool * (const list)) = 
  let (b, accum) = acc
  in
  if b == true
    then
      acc
  else
    match comm with
    | Quit -> (true,accum)
    | Push v -> (b,v::accum)
    | Pop -> pop b accum
    | Add -> higherOrderMathCom (lengthGreaterTwo::topTwoInteger::[]) (+) b accum
    | Sub -> higherOrderMathCom (lengthGreaterTwo::topTwoInteger::[]) (-) b accum
    | Mul -> higherOrderMathCom (lengthGreaterTwo::topTwoInteger::[]) ( * ) b accum
    | Div -> higherOrderMathCom (lengthGreaterTwo::topTwoInteger::divideByZero::[]) (/) b accum
    | _ -> acc

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