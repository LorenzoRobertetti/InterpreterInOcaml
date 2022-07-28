type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
           Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
           Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
           Letrec of ide * exp * exp |
           (*tipo costruttore per il dizionario e successive funzionalità*)
           EmptyDict | Insert of string * exp * exp | Delete of string * exp | Has_key of string * exp | Iterate of exp * exp | Fold of exp * exp | Filter of exp * exp |
           (*tipo costruttore per la lista per implementare l'operazione di filter*)
           EmptyKeyList | AddKey of string * exp;;


(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | Dict of dict | KeyList of keylist
(*in and perchè si chiamano a vicenda*)
and evFun = ide * exp * evT env
(*tipo esprimibile per il dizionario*)
and dict = Nil | Cons of (string * evT * dict)
(*tipo esprimibile per la lista*)
and keylist = KeyNil | KeyCons of (string * keylist)


(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
    "int" -> (match v with
        Int(_) -> true |
        _ -> false) |
    "bool" -> (match v with
        Bool(_) -> true |
        _ -> false) |
    "dict" -> (match v with
        Dict(_) -> true |
        _ -> false) |
    "keylist" -> (match v with
        KeyList(_) -> true |
        _ -> false) |
    _ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n*u))
  else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n+u))
  else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n-u))
  else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Bool(n=u))
  else failwith("Type error");;

let minus x = if (typecheck "int" x)
  then (match x with
        Int(n) -> Int(-n))
  else failwith("Type error");;

let iszero x = if (typecheck "int" x)
  then (match x with
        Int(n) -> Bool(n=0))
  else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> (Bool(b||e)))
  else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> Bool(b&&e))
  else failwith("Type error");;

let non x = if (typecheck "bool" x)
  then (match x with
        Bool(true) -> Bool(false) |
        Bool(false) -> Bool(true))
  else failwith("Type error");;
(*funzione per aggiungere elem ad una lista*)
let addkey k kl = if (typecheck "keylist" kl)
  then(match kl with
        KeyList kla -> KeyList (KeyCons(k, kla)))
  else failwith("Type error");;
(*funzioni primitive richieste dalla specifica*)
(*la funzione ricorsiva è incapsulata da quella semplice*)
(*insert*)
let rec insrec k v a = match a with
    Nil -> Cons (k, v, Nil) |
    Cons (kk, vv, aa) -> if (kk = k)
      then Cons(k, v, aa)
      else Cons(kk, vv, insrec k v aa);;

let insert k v d = if (typecheck "dict" d)
  then(match d with
        Dict a -> Dict (insrec k v a))
  else failwith("Type error");;
(*delete*)
let rec delrec k a = match a with
    Nil -> Nil |
    Cons (kk, vv, aa) -> if (kk = k)
      then aa
      else Cons(kk, vv, delrec k aa);;

let delete k d = if (typecheck "dict" d)
  then(match d with
        Dict a -> Dict (delrec k a))
  else failwith("Type error");;
(*has_key*)
let rec has_keyrec k a = match a with
    Nil -> false |
    Cons (kk, vv, aa) -> if (kk = k)
      then true
      else has_keyrec k aa;;

let has_key k d = if (typecheck "dict" d)
  then(match d with
        Dict a -> Bool(has_keyrec k a))
  else failwith("Type error");;
(*funzione di utilità per cercare una chiave in una lista *)
let rec list_has_key kla k = match kla with
    KeyNil -> false |
    KeyCons (kk, kkla) -> if (kk = k)
      then true
      else list_has_key kkla k;;
(*filter*)
let rec filterrec kla a = match a with
    Nil -> Nil |
    Cons (kk, vv, aa) -> if (list_has_key kla kk)
      then Cons(kk, vv, filterrec kla aa)
      else filterrec kla aa;;

let filter kl d = if (typecheck "keylist" kl) && (typecheck "dict" d)
  then(match d with
        Dict a -> match kl with
              KeyList kla -> Dict(filterrec kla a))
  else failwith("Type error");;


(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
    Eint n -> Int n |
    Ebool b -> Bool b |
    IsZero a -> iszero (eval a r) |
    Den i -> applyenv r i |
    Eq(a, b) -> eq (eval a r) (eval b r) |
    Prod(a, b) -> prod (eval a r) (eval b r) |
    Sum(a, b) -> sum (eval a r) (eval b r) |
    Diff(a, b) -> diff (eval a r) (eval b r) |
    Minus a -> minus (eval a r) |
    And(a, b) -> et (eval a r) (eval b r) |
    Or(a, b) -> vel (eval a r) (eval b r) |
    Not a -> non (eval a r) |
    EmptyKeyList -> KeyList KeyNil |
    EmptyDict -> Dict Nil |
    AddKey(key, klist) -> addkey key (eval klist r) |
    Insert(key, value, dictonary) -> insert key (eval value r) (eval dictonary r) |
    Delete(key, dictonary) -> delete key (eval dictonary r) |
    Has_key(key, dictonary) -> has_key key (eval dictonary r) |
    Iterate(f, dictonary) -> iterate (eval f r) (eval dictonary r) |
    Fold(f, dictonary) -> fold (eval f r) (eval dictonary r) |
    Filter(kl, dictonary) -> filter (eval kl r) (eval dictonary r) |
    Ifthenelse(a, b, c) ->
      let g = (eval a r) in
      if (typecheck "bool" g)
      then (if g = Bool(true) then (eval b r) else (eval c r))
      else failwith ("nonboolean guard") |
    Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
    Fun(i, a) -> FunVal(i, a, r) |
    FunCall(f, eArg) -> funcall (eval f r) (eval eArg r) |
    Letrec(f, funDef, letBody) ->
      (match funDef with
         Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
           eval letBody r1 |
         _ -> failwith("non functional def"))
(*funzioni che ho dovuto aggiungere, la funcall l'ho riadatta*)
(* in and perchè chiamano la eval tramite la funcall*)
and funcall fClosure aVal =
  (match fClosure with
     FunVal(arg, fBody, fDecEnv) ->
       eval fBody (bind fDecEnv arg aVal) |
     RecFunVal(g, (arg, fBody, fDecEnv)) ->
       let rEnv = (bind fDecEnv g fClosure) in
       let aEnv = (bind rEnv arg aVal) in
       eval fBody aEnv |
     _ -> failwith("non functional value"))

and iteraterec f a = match a with
    Nil -> Nil |
    Cons (kk, vv, aa) -> Cons(kk, funcall f vv, iteraterec f aa)

and iterate f d = if (typecheck "dict" d)
  then(match d with
        Dict a -> Dict (iteraterec f a))
  else failwith("Type error")

and foldrec f a = match a with
    Nil -> Int 0 |
    Cons (kk, vv, aa) -> sum (funcall f vv) (foldrec f aa)

and fold f d = if (typecheck "dict" d)
  then(match d with
        Dict a -> foldrec f a)
  else failwith("Type error");;

(* =============================  TESTS  ================= *)

let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;

let e3 = Insert("mele", Eint 430, Insert("banane", Eint 312, Insert("arance", Eint 525, Insert("pere", Eint 217, EmptyDict))));;

eval e3 env0;;

let e6 = Insert("kiwi", Eint 300, e3);;

eval e6 env0;;

let e7 = Delete("pere", e3);;

eval e7 env0;;

let e8 = Has_key("banane", e3);;

eval e8 env0;;

let e9 = Iterate(Fun("y", Sum(Den "y", Eint 1)), e3);;

eval e9 env0;;

let e10 = Fold(Fun("y", Sum(Den "y", Eint 1)), e3);;

eval e10 env0;;

let e4 = AddKey("mele", AddKey("pere", EmptyKeyList));;

eval e4 env0;;

let e5 = Filter(e4, e3);;

eval e5 env0;;
