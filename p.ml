  type ide = string;;

  type exp =
  CstInt of int
  | CstTrue
  | CstFalse
  | Times of exp * exp
  | Sum of exp * exp
  | Sub of exp * exp
  | Eq of exp * exp
  | Iszero of exp
  | Or of exp * exp
  | And of exp * exp
  | Not of exp
  | Den of ide
  | Ifthenelse of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide * exp
  | Apply of exp * exp
  | Letrec of ide * exp * exp
  | Dict of dictarg
  | Insert of ide * exp * exp
  | Delete of exp * ide
  | Has_key of ide * exp
  | Iterate of exp * exp
  | Fold of exp * exp
  | Filter of ide list * exp

  and dictarg = Empty | Val of ide * exp * dictarg;;

  type 't env = ide -> 't;;
  let emptyenv (v : 't) = fun x -> v;;
  let applyenv (r : 't env) (i : ide) = r i;;
  let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

  type evT = Int of int | Bool of bool | Unbound | Clousure of ide * exp * evT env | RecClosure of ide * evFun | Dictvalues of (ide * exp) list
             and evFun = ide * exp * evT env;;

  let typecheck (x, y) =
                          match x with
                          | "int" -> (match y with
                                      | Int(u) -> true
                                      | _ -> false)
                          | "bool" ->
                                     (match y with
                                      | Bool(u) -> true
                                      | _ -> false)
                                      | _ -> failwith ("not a valid type");;

  let is_zero x = match (typecheck("int",x), x) with
                  | (true, Int(y)) -> Bool(y==0)
                  | (_, _) -> failwith("run-time error");;

  let int_eq(x,y) = match (typecheck("int",x), typecheck("int",y), x, y) with
                    | (true, true, Int(v), Int(w)) -> Bool(v = w)
                    | (_,_,_,_) -> failwith("run-time error ");;

  let int_plus(x, y) = match(typecheck("int",x), typecheck("int",y), x, y) with
                       | (true, true, Int(v), Int(w)) -> Int(v + w)
                       | (_,_,_,_) -> failwith("run-time error ");;

  let int_times(x,y) = match(typecheck("int",x), typecheck("int",y), x, y) with
                       | (true, true, Int(v),Int(w)) -> Int(v*w)
                       | (_,_,_,_) -> failwith("run-time error ");;

  let int_sub(x,y) = match(typecheck("int",x), typecheck("int",y), x, y) with
                     | (true, true, Int(v),Int(w)) -> Int(v-w)
                     | (_,_,_,_) -> failwith("run-time error ");;

  let bool_and(x,y) = match(typecheck("bool",x), typecheck("bool",y), x, y) with
                     | (true, true, Bool(v),Bool(w)) -> Bool(v && w)
                     | (_,_,_,_) -> failwith("run-time error ");;

  let bool_or(x,y) = match(typecheck("bool",x), typecheck("bool",y), x, y) with
                      | (true, true, Bool(v),Bool(w)) -> Bool(v || w)
                      | (_,_,_,_) -> failwith("run-time error ");;

  let bool_not(x) = match(typecheck("bool",x), x) with
                      | (true,Bool(true)) -> Bool(false)
                      | (true,Bool(false)) -> Bool(true)
                      | (_,_) -> failwith("run-time error ");;

  let rec lookup env x =
                         match env with
                         | [] -> failwith("not found")
                         | (y,v)::r -> if x==y then v
                                       else lookup r x;;

  let rec eval e r =  match e with
                      | CstInt(n) -> Int(n)
                      | CstTrue -> Bool(true)
                      | CstFalse -> Bool(false)
                      | Iszero(e1) -> is_zero(eval e1 r)
                      | Eq(e1,e2) -> int_eq((eval e1 r),(eval e2 r))
                      | Times(e1,e2) -> int_times((eval e1 r), (eval e2 r))
                      | Sum(e1,e2) -> int_plus((eval e1 r), (eval e2 r))
                      | Sub(e1,e2) -> int_sub((eval e1 r), (eval e2 r))
                      | And(e1,e2) -> bool_and((eval e1 r), (eval e2 r))
                      | Or(e1,e2) -> bool_or ((eval e1 r), (eval e2 r))
                      | Not(e1) -> bool_not(eval e1 r)
                      | Ifthenelse(e1,e2,e3) -> let g = eval e1 r in
                                                match typecheck("bool",g) with
                                                | true -> match g with
                                                          | Bool(true) -> eval e2 r
                                                          | Bool(false) -> eval e3 r
                                                | _ -> failwith("Error ifthenelse")
                      | Let(i, e, ebody) -> eval ebody (bind r i (eval e r))
                      | Fun(i, a) -> Clousure(i, a, r)
                      | Apply(f, eArg) -> let fclosure = eval f r in
                                               (match fclosure with
                                                | Clousure(arg, fbody, fDecEnv) -> let aVal = eval eArg r in
                                                                                   let aenv = bind fDecEnv arg aVal in
                                                                                  eval fbody aenv
                                                | RecClosure(f, (recArg,fBody,fDecEnv)) -> let aVal = (eval actParam r) in
                                                                                           let rEnv = bind fDecEnv f fClosure in
                                                                                           let aEnv = bind rEnv recArg aVal in
                                                                                           eval fBody aEnv
                                                | _ -> failwith("not a function"))
                      | Letrec(fIde, funDef, letBody) -> match funDef with
                                                        |Fun(i, fBody) -> let r1 = (bind r fIde (RecClosure(fIde, (i, fBody, r))))
                                                                          in  eval letBody r1
                                                        | _ -> failwith("non functional def")
                      | Dict(l) -> Dictvalues(evalList l r)
                      | Insert(id,e1,d) -> match eval d r with
                                           | Dictvalues(l1) -> let evalue = eval e1 r
                                                              in Dictvalues(insert l1 id evalue)
                                           | _ -> failwith ("Insert not used on a dict")

                      | Delete (d,id) -> match eval d r with
                                           | Dictvalues(l1) -> Dictvalues(delete l1 id false)
                                           | _ -> failwith ("Delete not used on a dict")

                      | Has_key(id,d) -> match eval d r with
                                           | Dictvalues(l1) -> Dictvalues(haskey l1 id)
                                           | _ -> failwith ("HasKey not used on a dict")

                      | Iterate(funz,d) ->  let dvalue=eval d r in
                                           match dvalue with
                                           | Dictvalues(l1) -> Dictvalues(apl funz l1)
                                           | _ -> failwith ("Iterate not used on dict ")

                      | Fold(funz,d) ->     match eval d r with
                                           | Dictvalues(l1) -> apply funz l1 0
                                           | _ -> failwith ("Fold not used on a dict")
  and evalList l amb =
                       match l with
                       | Empty -> []
                       | Val(id,e,ls) -> let evalue = eval e amb
                                         in (id,evalue)::evallist ls amb
                       | _ -> failwith("Not a dict")


  and insert l id1 value=
                       match l with
                       | [] -> (id1,value)::[]
                       | x::xs -> insert xs id1 value

  and delete l id1 a =
                       match (l,a) with
                       | ([],_) -> []
                       | (id,x)::xs -> if id == id1 && a == false then delete xs id1 true
                                       else (id,x)::delete xs id1

  and haskey l id1 =
                       match l with
                       | [] -> false
                       | (id,x)::xs -> if id1==id then true
                                       else haskey xs id1

  and apply funz l1 a =
                       match l1 with
                       | [] -> a
                       | (id,x)::xs -> apply xs ((funz x)+a)

  and apl funct l1 =
                       match l1 with
                       | [] -> []
                       | (id,x)::xs -> (id,funct x) :: applyfun funct xs;;
