type ide = string;;

type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
  Letrec of ide * exp * exp
  | Dict of dictarg
  | Insert of ide * exp * exp 
  | Delete of exp * ide 
  | Has_key of ide * exp
  | Iterate of exp * exp
  | Fold of exp * exp
  | Filter of ide list * exp
  and dictarg = Empty | Val of ide * exp * dictarg;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | Dictvalues of (ide * evT) list
and evFun = ide * exp * evT env

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
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

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
      Eint n -> Int n 
    | Ebool b -> Bool b
    | IsZero a -> iszero (eval a r) 
    | Den i -> applyenv r i 
    | Eq(a, b) -> eq (eval a r) (eval b r) 
    | Prod(a, b) -> prod (eval a r) (eval b r) 
    | Sum(a, b) -> sum (eval a r) (eval b r) 
    | Diff(a, b) -> diff (eval a r) (eval b r) 
    | Minus a -> minus (eval a r)
    | And(a, b) -> et (eval a r) (eval b r)
    | Or(a, b) -> vel (eval a r) (eval b r) 
    | Not a -> non (eval a r) 
    | Ifthenelse(a, b, c) -> let g = (eval a r) in
			                        if (typecheck "bool" g) then (if g = Bool(true) then (eval b r) else (eval c r))
                              else failwith ("nonboolean guard")
    | Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
    | Fun(i, a) -> FunVal(i, a, r) 
    | FunCall(f, eArg) -> let fClosure = (eval f r) in
			                        (match fClosure with
                                   FunVal(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg (eval eArg r))
                                 | RecFunVal(g, (arg, fBody, fDecEnv)) -> let aVal = (eval eArg r) in
                                                                    	let rEnv = (bind fDecEnv g fClosure) in
				                                                          			let aEnv = (bind rEnv arg aVal) in
                                                                          eval fBody aEnv
                               | _ -> failwith("non functional value")) 
    | Letrec(f, funDef, letBody) ->  (match funDef with
            	                        	Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                                               eval letBody r1 
                                        |_ -> failwith("non functional def"))
    | Dict(l) -> Dictvalues(evalList l r)
    | Insert(id,e1,d) -> (match eval d r with
                         Dictvalues(l1) -> let evalue = eval e1 r in Dictvalues(insert l1 id evalue)
                        | _ -> failwith("Insert non used on a dict"))
    | Delete(d,id) -> (match eval d r with
                      Dictvalues(l1) -> Dictvalues(delete l1 id false)
                      | _ -> failwith("delete not used on a dict")) 
    | Has_key(id,d) -> (match eval d r with
                       Dictvalues(l1) -> haskey l1 id
                       | _ -> failwith("HasKey not used on a dict")) 
    | Iterate(funz,d) -> (match d with
                         Dict(l1) -> Dictvalues(apl funz l1 r)
                         | _ -> failwith("Iterate not used on a dict")) 
    | Fold(funz,d) -> (match d with
                      Dict(l1) -> apply funz l1 (Int(0)) r
                      | _ -> failwith("Fold not used on a dict")) 

    
     and evalList (l:dictarg) (amb: evT env) : (ide*evT) list = (match l with
                          Empty -> []
                          | Val(id,e,ls) -> let evalue = eval e amb
                                            in (id,evalue)::(evalList ls amb)
                          | _ -> failwith("Not a dict"))
                             
     and insert (l:(ide*evT) list) (id1:string) (value:evT) : (ide*evT) list= l @ [(id1,value)]
                          
  
     and delete (l:(ide*evT) list) (id1:string) (a:bool) : (ide*evT) list =
                          ( match (l,a) with
                           ([],_) -> []
                         | (((id,x)::xs),bl) -> if ((id=id1) && bl == false) then delete xs id1 true
                                         else (id,x)::delete xs id1 bl)
                 
     and haskey (l:(ide*evT) list) (id1:string) : evT  = (match l with
                         [] -> Bool false
                       | (id,x)::xs -> if id1=id then Bool true
                                       else haskey xs id1) 
     
     and apl (funct:exp) (l1:dictarg) (amb:evT env) : (ide*evT) list = (match l1 with
                         Empty -> []
                         | Val(id,e,ls) -> let value = eval (FunCall(funct,e)) amb
                                          in (id,value) :: apl funct ls amb 
                         |_ -> failwith("Not a dict"))
                     
     and apply (funct:exp) (l1:dictarg) (a:evT) (amb:evT env)  : evT  = (match l1 with
                                 Empty -> a
                                 | Val(id,e,ls) -> let value = eval (FunCall(funct,e)) amb
                                                   in ( match (a,value) with
                                                   ((Int(u),Int(v))) -> apply funct ls (Int(u+v)) amb
                                                   |_->failwith("Error apply"))
                                 |_ -> failwith("Not a dict"));;
                            
    


(*)                TEST            *)

eval (Dict(Val("p1",Eint(10),Val("p2",Eint(20),Empty)))) (emptyenv Unbound);;

eval (Insert("p3",Eint(30),(Dict(Val("p1",Eint(10),Val("p2",Eint(20),Empty)))))) (emptyenv Unbound);;

eval (Delete((Dict(Val("p1",Eint(10),Val("p2",Eint(20),Val("p2",Eint(30),Empty))))),"p2")) (emptyenv Unbound);;

eval (Has_key("p1",(Dict(Val("p1",Eint(10),Val("p2",Eint(20),Empty)))))) (emptyenv Unbound);;

eval (Iterate(Fun("y", Sum(Den "y", Eint 100)),(Dict(Val("p1",Eint(10),Val("p2",Eint(20),Empty)))))) (emptyenv Unbound);;

eval (Fold(Fun("y", Sum(Den "y", Eint 100)),(Dict(Val("p1",Eint(10),Val("p2",Eint(20),Empty)))))) (emptyenv Unbound);;