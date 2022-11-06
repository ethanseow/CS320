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
type const = 
  | Int of int
  | String of string
type com = 
  | Quit
  | Push of const
  | Pop
  | Add
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
      printToFile s "bungus"
  else
    ()