(*

First Name: Hayden 
Last Name: Rothman
Last Updated: 3/22/2022
Source: This program is the result of an assignment from CS320 at Boston University
*)

(* util functions *)
let is_lower_case c =
  'a' <= c && c <= 'z'
let is_upper_case c =
  'A' <= c && c <= 'Z'
let is_alpha c =
  is_lower_case c || is_upper_case c
let is_digit c =
  '0' <= c && c <= '9'
let is_alphanum c =
  is_lower_case c ||
  is_upper_case c ||
  is_digit c
let is_blank c =
  String.contains " \012\n\r\t" c
let explode s =
  List.of_seq (String.to_seq s)
let implode ls =
  String.of_seq (List.to_seq ls)
let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ (loop ())
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res
(* end of util functions *)

(* parser combinators *)
type 'a parser = char list -> ('a * char list) option
let parse (p : 'a parser) (s : string) : ('a * char list) option =
  p (explode s)
let pure (x : 'a) : 'a parser =
  fun ls -> Some (x, ls)
let fail : 'a parser = fun ls -> None
let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None
let (>>=) = bind
let (let*) = bind
let read : char parser =
  fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None
let satisfy (f : char -> bool) : char parser =
  fun ls ->
  match ls with
  | x :: ls ->
    if f x then Some (x, ls)
    else None
  | _ -> None
let char (c : char) : char parser =
  satisfy (fun x -> x = c)
let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None
let (>>) = seq
let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) ->
    (match p2 ls with
     | Some (_, ls) -> Some (x, ls)
     | None -> None)
  | None -> None
let (<<) = seq'
let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls)  -> Some (x, ls)
  | None -> p2 ls
let (<|>) = alt
let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None
let (>|=) = map
let (>|) = fun p c -> map p (fun _ -> c)
let rec many (p : 'a parser) : ('a list) parser =
  fun ls ->
  match p ls with
  | Some (x, ls) ->
    (match many p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> Some ([], ls)
let rec many1 (p : 'a parser) : ('a list) parser =
  fun ls ->
  match p ls with
  | Some (x, ls) ->
    (match many p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> None
let rec many' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) ->
    (match many' p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> Some ([], ls)
let rec many1' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) ->
    (match many' p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> None
let whitespace : unit parser =
  fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c
    then Some ((), ls)
    else None
  | _ -> None
let ws : unit parser =
  (many whitespace) >| ()
let ws1 : unit parser =
  (many1 whitespace) >| ()
let digit : char parser =
  satisfy is_digit
let natural : int parser =
  fun ls ->
  match many1 digit ls with
  | Some (xs, ls) ->
    Some (int_of_string (implode xs), ls)
  | _ -> None
let literal (s : string) : unit parser =
  fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match cs, ls with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c
      then loop cs xs
      else None
    | _ -> None
  in loop cs ls
let keyword (s : string) : unit parser =
  (literal s) >> ws >| ()
let integer = 
  fun ls -> 
  match ls with 
  | h::t -> 
    if h = '-' then 
      match natural t with 
      | Some (i,ls) -> Some (-1 * i, ls)
      | _ -> None
    else natural ls
  | [] -> None
(* end of parser combinators *)

(*Grammar*)
let digit = satisfy (fun c -> '0' <= c && c <= '9')
type nat = Nat of int
let letter = satisfy (fun c -> 'a' <= (Char.lowercase_ascii c) && (Char.lowercase_ascii c) <= 'z')
let initial = letter <|> satisfy (fun c -> c = '_')
type name = string
let nameC = initial <|> digit <|> satisfy (fun c -> c = '\'')
let isNameValid = 
  fun (ls:char list) -> 
  match (parse initial (implode ls)) with 
  | Some (h,[]) -> Some (implode [h], [])
  | Some (h,t) ->   
    let rec aux (ls : char list) acc = 
      match (parse nameC (implode ls)) with 
      | Some (h',[]) -> Some ((implode (List.rev (h'::acc))), ls)
      | Some (h,t) -> aux t (h::acc)
      | None -> Some (implode (List.rev acc), ls)
    in aux (t) [h]
  | _ -> None
let nameS = fun ls -> isNameValid ls
type const = Natc of nat | Namec of name | Unitc of unit 
type com = Push of const | Tracec | Addc | Subc | Mulc | Divc | IfElseEnd of (coms * coms) 
         | Let | Lookup | BeginEnd of coms | FunEnd of (name * name * coms) | Call
and coms = (com list)
type prog = Prog of coms
type env = (name * valuec) list
and valuec = Constv of const | Funv of (name * name * coms * env)

(*Stack definition*)
type 'a stack = 'a list
let push (s: 'a stack) (a: 'a) : 'a stack = (a::s)
let pop (s: 'a stack) : ('a * 'a stack) option = 
  match s with 
  | [] -> None
  | h::rest -> Some (h,rest)

(*parsers for each type*)
let pushP_i : com parser =
  many whitespace >>= fun _ -> 
  literal "Push" >>= fun _ ->
  many1 whitespace >>= fun _ -> 
  integer >>= fun i ->
  many whitespace >>= fun _ -> pure (Push (Natc (Nat (i))))
let pushP_n : com parser =
  many whitespace >>= fun _ -> 
  literal "Push" >>= fun _ ->
  many1 whitespace >>= fun _ -> 
  isNameValid >>= fun (n: string) ->
  many whitespace >>= fun _ -> pure (Push (Namec ((n))))
let pushP_u : com parser =
  many whitespace >>= fun _ -> 
  literal "Push" >>= fun _ ->
  many1 whitespace >>= fun _ -> 
  keyword "()" >>= fun _ ->
  many whitespace >>= fun _ -> pure (Push (Unitc ()))
let traceP =
  many whitespace >>= fun _ -> 
  literal "Trace" >>= fun _ ->
  many whitespace >>= fun _ -> pure Tracec
let addP =
  many whitespace >>= fun _ -> 
  literal "Add" >>= fun _ ->
  many whitespace >>= fun _ -> pure Addc
let subP =
  many whitespace >>= fun _ -> 
  literal "Sub" >>= fun _ ->
  many whitespace >>= fun _ -> pure Subc
let rec mulP =
  many whitespace >>= fun c -> 
  literal "Mul" >>= fun _ -> 
  many whitespace >>= fun _ -> pure Mulc
let divP =
  many whitespace >>= fun _ -> 
  literal "Div" >>= fun _ ->
  many whitespace >>= fun _ -> pure Divc
let letP =
  many whitespace >>= fun _ -> 
  literal "Let" >>= fun _ ->
  many whitespace >>= fun _ -> pure Let 
let lookupP =
  many whitespace >>= fun _ -> 
  literal "Lookup" >>= fun _ ->
  many whitespace >>= fun _ -> pure Lookup
let callP =
  many whitespace >>= fun _ -> 
  literal "Call" >>= fun _ ->
  many whitespace >>= fun _ -> pure Call
let rec beginEndP u =
  many whitespace >>= fun _ -> 
  literal "Begin" >>= fun _ ->
  many1 (commandP ()) >>= fun c -> 
  many whitespace >>= fun _ -> 
  literal "End" >>= fun _ ->
  many whitespace >>= fun _ -> pure (BeginEnd c) 
and funEndP u =
  many whitespace >>= fun _ -> 
  literal "Fun" >>= fun _ ->
  many1 whitespace >>= fun _ ->
  isNameValid >>= fun n1 -> 
  many1 whitespace >>= fun _ -> 
  isNameValid >>= fun n2 -> 
  many1 whitespace >>= fun _ -> 
  many1 (commandP ()) >>= fun c -> 
  literal "End" >>= fun _ ->
  many whitespace >>= fun _ -> pure (FunEnd (n1,n2,c))
and if_else_endP u = 
  many whitespace >>= fun _ -> 
  literal "If" >>= fun _ ->
  many whitespace >>= fun _ ->  
  many1 (commandP ())
  >>= fun c1 ->
  many whitespace >>= fun _ ->  
  literal "Else" >>= fun _ ->
  many whitespace >>= fun _ ->  
  many1 (commandP ())
  >>= fun c2 -> 
  many whitespace >>= fun _ -> 
  literal "End" >>= fun _ ->
  many whitespace >>= fun _ -> pure (IfElseEnd (c1,c2)) 
and commandP u =  
  (letP <|> lookupP <|> callP <|> (beginEndP ()) <|> (funEndP ()) <|> pushP_u <|> pushP_n
   <|> pushP_i <|> traceP <|> addP <|> subP <|> mulP <|> divP <|> (if_else_endP ()))
let commandsP = 
  many1 (commandP ())

(*Eval Utility/Helper Functions*)
let nameEq (n1: name) (n2: name) = 
  match (n1,n2) with 
  | (n1, n2) -> n1=n2
let getVal (env: (name * valuec) list) (v: valuec) = 
  let rec aux env' = 
    match env' with 
    | [] -> None
    | (n',v')::t -> 
      (match v with 
       | Constv (Namec n) -> 
         if (nameEq n n') then 
           match v' with 
           | Constv c -> Some (Constv c)
           | Funv (fname, arg, cms, env) -> Some (Funv (fname, arg, cms, env))
         else aux t
       | Constv (Natc (x)) -> Some (Constv (Natc x))
       | Constv (Unitc u) -> Some (Constv (Unitc u))
       | Funv f -> Some (Funv f))
  in aux env
let rec getFullVal (env: (name * valuec) list) (v: valuec) = 
  match v with 
  | Constv (Natc (Nat x)) -> Some (Constv (Natc (Nat x)))
  | _ -> 
    (match getVal env v with 
     | Some (Constv (Unitc u)) -> Some (Constv (Unitc u))
     | Some (Constv (Namec n)) -> getFullVal env (Constv (Namec n))
     | Some (Constv (Natc (Nat x))) -> Some (Constv (Natc (Nat x)))
     | Some (Funv (fname, arg, cms, env)) -> Some (Funv (fname, arg, cms, env))
     | _ -> None)

(*Evaluating*)
let string_of_const c = 
  match c with 
  | Natc (Nat x) -> string_of_int x
  | Namec (s) -> s
  | Unitc () -> "()"
let rec string_of_val (v: valuec) = 
  match v with 
  | Constv c -> string_of_const c
  | Funv (fname, n, c, env) -> "<fun>"
let popTwice (s: valuec stack) : (valuec * valuec * valuec stack) option = 
  match pop s with 
  | Some (h1, rest) -> 
    (match pop rest with 
     | Some (h2, rest) -> Some (h1,h2,rest) 
     | _ -> None)
  | _ ->  None
(*command eval functions*)
let pushEval (c: valuec) (cs: valuec stack) env = Some ((push cs c),[], env)
let traceEval (cs: valuec stack) (env: (name * valuec) list) = 
  match pop cs with 
  | Some (Funv _, rest) -> Some (push rest (Constv (Unitc ())), [Constv (Namec ("<fun>"))], env)
  | Some (h,rest) -> Some (push rest (Constv (Unitc ())), [h], env)
  | _ -> None
let addEval (s: valuec stack) env = 
  match (popTwice s) with 
  | Some (v1,v2, rest) -> 
    (match (getFullVal env v1, getFullVal env v2) with 
     | (Some (Constv (Natc (Nat x))), Some (Constv (Natc (Nat y)))) ->
       Some (((push rest (Constv (Natc (Nat (y + x)))))), [], env)
     | _ ->  None)
  | _ ->  None
let subEval (s: valuec stack) env = 
  match (popTwice s) with 
  | Some (v1,v2, rest) -> 
    (match (getFullVal env v1, getFullVal env v2) with 
     | (Some (Constv (Natc (Nat x))), Some (Constv (Natc (Nat y)))) -> 
       Some (((push rest (Constv (Natc (Nat (y - x)))))), [], env)
     | _ -> None)
  | _ -> None
let mulEval (s: valuec stack) env = 
  match (popTwice s) with 
  | Some (v1,v2, rest) -> 
    (match (getFullVal env v1, getFullVal env v2) with 
     | (Some (Constv (Natc (Nat x))), Some (Constv (Natc (Nat y)))) -> 
       Some (((push rest (Constv (Natc (Nat (y * x)))))), [], env)
     | _ -> None)
  | _ -> None
let divEval (s: valuec stack) env = 
  match (popTwice s) with 
  | Some (v1,v2, rest) -> 
    (match (getFullVal env v1, getFullVal env v2) with 
     | (Some (Constv (Natc (Nat x))), Some (Constv (Natc (Nat y)))) -> 
       Some (((push rest (Constv (Natc (Nat (y / x)))))), [], env)
     | _ -> None)
  | _ -> None
let letEval (s: valuec stack) (env: (name * valuec) list) = 
  match (popTwice s) with 
  | Some (c, Constv (Namec n), rest) -> Some (rest, [], (n, c)::env)
  | _ -> None
let lookupEval (s: valuec stack) (env: (name * valuec) list) = 
  match pop s with 
  | Some (n, rest) -> 
    (match getVal env n with 
     | Some (x) -> Some (push rest (x), [], env)
     | _ -> None)
  | _ -> None
let rec evalComs c s acc env =  
  match c with 
  | [] -> Some (s,acc, env)
  | h::t -> 
    match (evalCom h s env) with
    | Some (s', c', env') -> evalComs t s' (c' @ acc) env'
    | _ ->  None
and evalCom c s (env: (name * valuec) list) : (valuec stack * string list * (name * valuec) list) option =
  match c with 
  | Push x -> pushEval (Constv x) s env
  | Tracec -> 
    (match s with 
     | [] -> None
     | Funv f::t -> 
       (match (traceEval s env) with 
        |  Some (s',ls', env') -> Some (s',  [("<fun>")], env') 
        | _ -> None)
     | h::t -> 
       match (traceEval s env) with 
       |  Some (s',ls', env') -> Some (s',  [(string_of_val h)], env')
       | _ -> None)
  | Addc -> addEval s env
  | Subc -> subEval s env
  | Mulc -> mulEval s env
  | Divc -> divEval s env
  | IfElseEnd (c1,c2) -> ifelseendEval (c1,c2) s env
  | Let -> letEval s env
  | Lookup -> lookupEval s env
  | BeginEnd cms -> beginEndEval s cms env
  | FunEnd (n1, n2, cms) -> funEndEval s n1 n2 cms env
  | Call -> callEval s env
and ifelseendEval (ctpl: coms * coms) (s: valuec stack) env  = 
  match ctpl with 
  | (c1,c2) -> 
    (match pop s with 
     | Some (Constv (Natc (Nat h)), rest) -> 
       if h > 0 then evalComs c1 rest [] env
       else evalComs c2 rest [] env
     | Some (Constv (Namec (h)), rest) -> 
       (match getFullVal env (Constv (Namec h)) with 
        | Some (Constv (Natc (Nat x))) -> 
          if x > 0 then evalComs c1 rest [] env
          else evalComs c2 rest [] env
        | _ -> None)
     | _ -> None)
and beginEndEval (s: valuec stack) (cms: coms) (env: env) = 
  match evalComs cms [] [] env with 
  | Some (s',l, env') -> Some (s' @ s, l, env)
  | _ -> None
and funEndEval (s: valuec stack) (fname: name) (arg: name) (cms: coms) (env: env) = 
  Some (s, [], ([fname, Funv (fname, arg, cms, env)] @ env))
and callEval s env = 
  match popTwice s with 
  | Some (v, Funv (fname, arg, cms, fenv), rest) -> 
    let fenv' = ((arg, v)::(fname, Funv (fname, arg, cms, fenv))::fenv) in 
    (match evalComs cms [] [] fenv' with 
     | Some (s', ls, env') -> 
       (match s' with 
        | h::t -> Some (h::rest, ls, env)
        | [] -> None)
     | _ -> None)  
  |_ -> None


(*Interpreter Function*)
let interpreter (src: string) : string * string list =
  match (parse commandsP src) with 
  | Some (c,ls) -> 
    (match (evalComs c [] [] []) with 
     | Some ([], ls', env) -> ("",ls')
     | Some (h::rest, ls', env) -> ((string_of_val h), ls')
     | _ -> ("Error", []))
  | _ -> ("Error",[])







(*
  Part 6 
*)
(* part3 template *)
(*type name = string*)
type term =
  (* lambda calculus *)
  | Name  of name
  | Fun   of name * name * term
  | App   of term * term
  (* extensions *)
  | Ifgz  of term * term * term
  | LetIn of name * term * term
  | Unit
  | Int   of int
  | Add   of term * term
  | Sub   of term * term
  | Mul   of term * term
  | Div   of term * term
  | Trace of term

type value =
  | IntVal of int
  | FunVal of name * name * term * envt
  | UnitVal

and envt = (string * value) list

type error =
  | TypeError
  | DivByZeroError
  | UnboundError

type result =
  | Value of value
  | Error of error

let string_of_value v =
  match v with
  | IntVal n -> string_of_int n
  | FunVal _ -> "<fun>"
  | UnitVal  -> "()"

let string_of_error err =
  match err with
  | TypeError      -> "TypeError"
  | DivByZeroError -> "DivByZeroError"
  | UnboundError   -> "UnboundError"

let string_of_result res =
  match res with
  | Value v -> string_of_value v
  | Error err -> string_of_error err

let string_of_log log = 
  let log =
    (List.fold_left 
       (fun acc log -> 
          if acc = ""
          then log
          else log ^ "; " ^ acc )
       "" log)
  in
  "[" ^ log ^ "]"

let string_of_env env =
  (List.fold_left
     (fun acc (s, v) ->
        if acc = "" 
        then s ^ ":=" ^ (string_of_value v)
        else s ^ ":=" ^ (string_of_value v) ^ "; " ^ acc))
    "" env

let rec string_of_term t =
  match t with
  | Name x -> x
  | Fun (fn, arg, e) -> 
    "Fun (" ^ fn ^ ", " ^ arg ^ ", " ^ (string_of_term e) ^ ")"
  | App (e1, e2) -> 
    "App (" ^ (string_of_term e1) ^ ", " ^ (string_of_term e2) ^ ")"
  (* extensions *)
  | Ifgz (cond, e1, e2) ->
    let cond = string_of_term cond in
    let e1 = string_of_term e1 in
    let e2 = string_of_term e2 in
    "Ifgz (" ^ cond ^ ", " ^ e1 ^ ", " ^ e2 ^ ")"
  | LetIn (x, e1, e2) ->
    let e1 = string_of_term e1 in
    let e2 = string_of_term e2 in
    "LetIn (" ^ x ^ ", " ^ e1 ^ ", " ^ e2 ^ ")"
  | Unit -> "Unit"
  | Int n -> "Int (" ^ (string_of_int n) ^ ")"
  | Add (e1, e2) ->
    let e1 = string_of_term e1 in
    let e2 = string_of_term e2 in
    "Add (" ^ e1 ^ ", " ^ e2 ^ ")"
  | Sub (e1, e2) ->
    let e1 = string_of_term e1 in
    let e2 = string_of_term e2 in
    "Sub (" ^ e1 ^ ", " ^ e2 ^ ")"
  | Mul (e1, e2) ->
    let e1 = string_of_term e1 in
    let e2 = string_of_term e2 in
    "Mul (" ^ e1 ^ ", " ^ e2 ^ ")"
  | Div (e1, e2) ->
    let e1 = string_of_term e1 in
    let e2 = string_of_term e2 in
    "Div (" ^ e1 ^ ", " ^ e2 ^ ")"
  | Trace e ->
    "Trace (" ^ (string_of_term e) ^ ")"


let rec interp env t log = 
  match t with
  | Name n -> (
      match List.assoc_opt n env with
      | Some v -> (Value v, log)
      | None -> 
        let _ = print_endline n in
        (Error UnboundError, log))
  | Fun (fn, arg, bod) -> (Value (FunVal (fn, arg, bod, env)), log)
  | App (f, a) -> (
      match interp env f log with
      | (Value (FunVal (fn, arg, e, env')), log) -> (
          match interp env a log with
          | (Value v, log) -> 
            let env' = (fn, FunVal (fn, arg, e, env')) :: env' in
            let env' = (arg, v) :: env' in
            interp env' e log
          | (error, log) -> (error, log))
      | (Value _, log) -> (Error TypeError, log)
      | (error, log) -> (error, log))
  | Ifgz (cond, e1, e2) -> (
      match interp env cond log with
      | (Value (IntVal n), log) -> 
        if n > 0
        then interp env e1 log 
        else interp env e2 log
      | (Value _, log) -> (Error TypeError, log)
      | (error, log) -> (error, log))
  | LetIn (name, e1, e2) -> (
      match interp env e1 log with
      | (Value v, log) -> interp ((name, v) :: env) e2 log
      | (error, log) -> (error, log))
  | Unit -> (Value UnitVal, log)
  | Int n -> (Value (IntVal n), log)
  | Add (e1, e2) -> (
      match interp env e1 log with
      | (Value (IntVal v1), log) -> (
          match interp env e2 log with
          | (Value (IntVal v2), log) -> (Value (IntVal (v1 + v2)), log)
          | (Value _, log) -> (Error TypeError, log)
          | (error, log) -> (error, log))
      | (Value _, log) -> (Error TypeError, log)
      | (error, log) -> (error, log))
  | Sub (e1, e2) -> (
      match interp env e1 log with
      | (Value (IntVal v1), log) -> (
          match interp env e2 log with
          | (Value (IntVal v2), log) -> (Value (IntVal (v1 - v2)), log)
          | (Value _, log) -> (Error TypeError, log)
          | (error, log) -> (error, log))
      | (Value _, log) -> (Error TypeError, log)
      | (error, log) -> (error, log))
  | Mul (e1, e2) -> (
      match interp env e1 log with
      | (Value (IntVal v1), log) -> (
          match interp env e2 log with
          | (Value (IntVal v2), log) -> (Value (IntVal (v1 * v2)), log)
          | (Value _, log) -> (Error TypeError, log)
          | (error, log) -> (error, log))
      | (Value _, log) -> (Error TypeError, log)
      | (error, log) -> (error, log))
  | Div (e1, e2) -> (
      match interp env e1 log with
      | (Value (IntVal v1), log) -> (
          match interp env e2 log with
          | (Value (IntVal 0), log) -> (Error DivByZeroError, log)
          | (Value (IntVal v2), log) -> (Value (IntVal (v1 / v2)), log)
          | (Value _, log) -> (Error TypeError, log)
          | (error, log) -> (error, log))
      | (Value _, log) -> (Error TypeError, log)
      | (error, log) -> (error, log))
  | Trace e -> (
      match interp env e log with
      | (Value v, log) -> (Value UnitVal, string_of_value v :: log)
      | (error, log) -> (error, log))

let run e = 
  let res, log = interp [] e [] in
  match res with
  | Value v -> (string_of_value v, log)
  | Error _ -> ("Error", [])

(* parser for term language *)

let reserved = [
  "fun";
  "if";
  "then";
  "else";
  "let";
  "rec";
  "in";
  "trace";
  "main";
]

let name : string parser =
  let* xs1 = many1 (satisfy (fun c -> is_alpha c || c = '_')) in
  let* xs2 = 
    many (satisfy (fun c ->
        is_alphanum c ||
        (c = '_') ||
        (c = '\'')))
  in
  let s = (implode xs1) ^ (implode xs2) in
  if List.exists (fun x -> x = s) reserved
  then fail
  else pure s << ws

let name_parser () =
  let* n = name in
  pure (Name n)

let unit_parser () =
  let* _ = keyword "()" in
  pure (Unit)

let int_parser () =
  let* n = natural in
  pure (Int n) << ws

let rec term_parser0 () =
  let* _ = pure () in
  (name_parser ()) <|>
  (unit_parser ()) <|>
  (int_parser ()) <|>
  (keyword "(" >> term_parser () << keyword ")")

and term_parser1 () =
  let* es = many1 (term_parser0 ()) in
  match es with
  | e :: es ->
    pure (List.fold_left (fun acc e -> App (acc, e)) e es)
  | _ -> fail

and term_parser2 () =
  let* e = term_parser1 () in
  let opr () = 
    (let* _ = keyword "*" in
     let* e = term_parser1 () in
     pure ((fun e1 e2 -> Mul (e1, e2)), e))
    <|>
    (let* _ = keyword "/" in
     let* e = term_parser1 () in
     pure ((fun e1 e2 -> Div (e1, e2)), e))
  in
  let* es = many (opr ()) in
  pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

and term_parser3 () =
  let* e = term_parser2 () in
  let opr () = 
    (let* _ = keyword "+" in
     let* e = term_parser2 () in
     pure ((fun e1 e2 -> Add (e1, e2)), e))
    <|>
    (let* _ = keyword "-" in
     let* e = term_parser2 () in
     pure ((fun e1 e2 -> Sub (e1, e2)), e))
  in
  let* es = many (opr ()) in
  pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

and term_parser () = 
  let* _ = pure () in
  (keyword "trace" >> term_parser3 () >|= (fun e -> Trace e)) <|>
  (fun_parser ()) <|>
  (iflz_parser ()) <|>
  (letrec_parser ()) <|>
  (letin_parser ()) <|>
  (term_parser3 ())

and fun_parser () =
  let* _ = keyword "fun" in
  let* a = name in
  let* _ = keyword "->" in
  let* e = term_parser () in
  pure (Fun ("_", a, e))

and iflz_parser () =
  let* _ = keyword "if" in
  let* cond = term_parser () in
  let* _ = keyword "then" in
  let* e1 = term_parser () in
  let* _ = keyword "else" in
  let* e2 = term_parser () in
  pure (Ifgz (cond, e1, e2))

and letin_parser () =
  let* _ = keyword "let" in
  let* n = name in
  let* _ = keyword "=" in
  let* e1 = term_parser () in
  let* _ = keyword "in" in
  let* e2 = term_parser () in
  pure (LetIn (n, e1, e2))

and letrec_parser () =
  let* _ = keyword "let" in
  let* _ = keyword "rec" in
  let* n = name in
  let* args = many1 name in
  let* _ = keyword "=" in
  let* e1 = term_parser () in
  let (e1, _) =
    List.fold_right
      (fun arg (acc, len) ->
         let fn = if len = 1 then n else "_" in
         (Fun (fn, arg, acc), len - 1))
      args (e1, List.length args)
  in
  let* _ = keyword "in" in
  let* e2 = term_parser () in
  pure (LetIn (n, e1, e2))

let nameEval (n: name) (env: envt) = Some ([Push ((Namec (n))); Lookup], [], env)
let rec funEval (n1: name) (n2: name) t env = 
  match termEval t env with 
  | Some (cms',log,env') -> Some ([FunEnd (n1, n2, cms'); Push (Namec n1); Lookup], [], env)
  | _ -> None
and appEval t1 t2 env = 
  match ( termEval t1 env ),( termEval t2 env ) with 
  | Some (cms,log1,env1), Some (cms',log2,env2)  -> 
    Some (cms @ cms' @ [Call], log1 @ log2, env1 @ env2)
  | _ -> None
and ifEval t1 t2 t3 env =
  match ( termEval t1 env ),( termEval t2 env ),( termEval t3 env )  with 
  | Some (Push n::[],log1,env1), Some (cms2,log2,env2), Some (cms3,log3,env3) ->
    Some ([Push n;Lookup;IfElseEnd (cms2, cms3)], log1 @ log2 @ log3, env1 @ env2 @ env3)
  | Some (cms,log1,env1), Some (cms2,log2,env2), Some (cms3,log3,env3) ->
    Some (cms @ [IfElseEnd (cms2, cms3)], log1 @ log2 @ log3, env1 @ env2 @ env3)
  | _ -> None
and letInEval (n1: name) t1 t2 env = 
  match termEval t1 env with 
  | Some (cms, log, env') ->
    (match termEval t2 env' with 
     | Some (cms', log', env'') -> Some ([BeginEnd ([Push (Namec n1)] @ cms @ [Let] @ cms')], log @ log', env'')
     | _ -> None)
  | _ -> None
and unitEval env = Some ([Push (Unitc ())],[], env)
and intEval x env = Some ([Push (Natc (Nat x))],[], env)
and addEval t1 t2 env = 
  match (termEval t1 env, termEval t2 env) with
  | (Some (cms, log1, env), Some (cms2, log2, env2)) ->
    Some (cms @ cms2 @ [Addc], log1 @ log2, env @ env2)
  | _ -> None
and subEval t1 t2 env = 
  match (termEval t1 env, termEval t2 env) with
  | (Some (cms, log1, env), Some (cms2, log2, env2)) ->
    Some (cms @ cms2 @ [Subc], log1 @ log2, env @ env2)
  | _ -> None
and mulEval t1 t2 env = 
  match (termEval t1 env, termEval t2 env) with
  | (Some (cms, log1, env), Some (cms2, log2, env2)) ->
    Some (cms @ cms2 @ [Mulc], log1 @ log2, env @ env2)
  | _ -> None
and divEval t1 t2 env = 
  match (termEval t1 env, termEval t2 env) with
  | (Some (cms, log1, env), Some (cms2, log2, env2)) ->
    Some (cms @ cms2 @ [Divc], log1 @ log2, env @ env2)
  | _ -> None
and tracetEval t env = 
  match termEval t env with 
  | Some (cms, log, env') -> Some (cms @ [Tracec], [], env)
  | _ -> None
and termEval (t: term) env = 
  let v = 
    match t with 
    | Name n -> nameEval n env
    | Fun (n1,n2,t) -> funEval n1 n2 t env
    | App (t1,t2) -> appEval t1 t2 env
    | Ifgz (t1,t2,t3) -> ifEval t1 t2 t3 env
    | LetIn (n,t1,t2) -> letInEval n t1 t2 env
    | Unit -> unitEval env
    | Int x -> intEval x env
    | Add (t1,t2) -> addEval t1 t2 env
    | Sub (t1,t2) -> subEval t1 t2 env
    | Mul (t1,t2) -> mulEval t1 t2 env
    | Div (t1,t2) -> divEval t1 t2 env
    | Trace t -> tracetEval t env
  in 
  match v with 
  | Some (cms',log,env') -> Some (cms',log, env')
  | _ -> None

(* Parse programs written in the term language. *)
let parse_prog (s : string) : (term * char list) option = 
  parse (ws >> term_parser ()) s


let string_to_coms (src : string) : coms =
  match parse_prog src with
  | Some (t, ls) -> 
    (match termEval t [] with 
     | Some (cms, log, env) -> cms
     | _ -> [])
  | _ -> []

let rec string_of_com (c) = 
  match c with 
  | Push x -> "Push " ^ string_of_const x
  | Tracec -> "Trace"
  | Subc -> "Sub"
  | Addc -> "Add"
  | Divc -> "Div"
  | Mulc -> "Mul"
  | IfElseEnd (c1,c2) -> "If " ^ string_of_coms c1 ^ " Else " ^ string_of_coms c2 ^ " End"
  | Let -> "Let"
  | Lookup -> "Lookup"
  | BeginEnd cms -> "Begin " ^ string_of_coms cms ^ " End"
  | FunEnd (n1, n2, cms) -> "Fun " ^ n1 ^ " " ^ n2 ^ " " ^ string_of_coms cms ^ " End"
  | Call -> "Call"
and string_of_coms (cms: coms)= 
  let rec aux cms acc = 
    match cms with 
    | h::t -> aux t (acc ^ " " ^ string_of_com h)
    | [] -> acc
  in aux cms ""

(* Compiles a program written in the Part3 Term Language to Part2 Stack Language.
 * Required by the autograder, do not change its type. *)
let compiler src = 
  (string_of_coms (string_to_coms src)) 
