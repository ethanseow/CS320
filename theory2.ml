type cookie_details = float * float
type cookie_flavor =
| CaramelPumpkin of cookie_details
| LaddooLemon of cookie_details
| Nevadito of cookie_details

let reverse (l : cookie_flavor list) : cookie_flavor list =
  let rec helper l = 
    match l with
    | [] -> []
    | h::t -> h::(helper t)
  in
  helper(helper l)

let append (l1 : cookie_flavor list) (l2 : cookie_flavor list) : cookie_flavor list =
  let rec helper l1 l2 = 
    match l1,l2 with
    | ([],[]) -> [] 
    | ([],h::t) -> h::(helper [] t)
    | (h::t,[]) -> h::(helper t [])
    | (h::t,_::_) -> h::(helper t l2)
  in
  helper l1 l2

let concat (ll : cookie_flavor list list) : cookie_flavor list = 
  List.fold_left append [] ll

let rec filter (fil : cookie_flavor -> bool) (l : cookie_flavor list) : cookie_flavor list = 
  match l with
  | [] -> []
  | h::t ->
    if fil h
      then
        h::filter fil t
    else
        filter fil t
  
let rec fold_right (f : cookie_flavor -> 'b -> 'b) (l : cookie_flavor list) (acc : 'b) : 'b =
  let helper (f : cookie_flavor -> 'b -> 'b) (l : cookie_flavor list) (acc : 'b) : 'b = 
    match l with
    | [] -> acc
    | h::t -> fold_right f t (f h acc)
  in
  helper f (reverse l) acc

let rec fix_cookie_box (f : cookie_flavor list) (a : float) (b : float) : cookie_flavor list list = 
  match f with
  | [] -> []
  | h::t -> 
    match h with
    | LaddooLemon _ -> [LaddooLemon(a,b);LaddooLemon(a,b)]::fix_cookie_box t a b
    | CaramelPumpkin _ -> [CaramelPumpkin(a,b);CaramelPumpkin(a,b)]::fix_cookie_box t a b
    | Nevadito _ -> [Nevadito(a,b);Nevadito(a,b)]::fix_cookie_box t a b
