
open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))

(* TODO environnement pour les types structure *)



(* TODO environnement pour les fonctions *)

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | _ -> error dummy_loc ("unknown struct ") (* TODO type structure *)

let rec eq_type ty1 ty2 = match ty1, ty2 with                  (*sert à vérifier que deux types sont bien égaux*)
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring | Twild, _ | _, Twild-> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | Tmany [], Tmany [] -> true
  | Tmany (t1::q1), Tmany (t2::q2) -> (t1 == t2) && eq_type (Tmany q1) (Tmany q2) 
  | _ -> false

    (* TODO autres types *)

let fmt_used = ref false
let fmt_imported = ref false

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in    (*sert à numéroter les variables d'un bloc*)
  fun x loc ?(used=false) ty -> (*à l'initialisation de la variable, elle n'a pas encore été utilisée => used = false*)
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = 0; v_depth = 0 }

module Env = struct
  module M = Map.Make(String)
  type t = var M.t
  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env

  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && (* TODO used *) v.v_used = false then error v.v_loc "unused variable" in
    List.iter check !all_vars


  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

  (* TODO type () et vecteur de types *)
end

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }  (*correspond à {expression x de TAST; type de x}*)
let stmt d = make d tvoid (*correspond à {expression x de TAST; tvoid = absence de type pour l'instant}*)

let rec print_type = function
  | Tint -> "int"
  | Tbool -> "bool" 
  | Tstring -> "string"
  | Tstruct s -> "struct" 
  | Tptr a -> "ptr"^(print_type a)
  | Twild -> "wild"
  | Tmany l -> "typ list"

let compo f g = function x -> f (g x)

let rec left_value expr = (*permet de tester si une expression est une l-value ou non*)
  match expr.expr_desc with
  | TEident _ -> true
  | TEdot (el, _) -> left_value el
  | TEunop (Ustar, el) -> el.expr_desc <> TEnil
  | _ -> false

let rec expr env e =
  let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt
  
and expr_desc env loc = function
  | PEskip ->
      TEskip, tvoid, false

  | PEconstant c ->
      TEconstant c, 
      (match c with 
      |Cbool x -> Tbool 
      |Cint x -> Tint
      |Cstring x -> Tstring), 
      false

  | PEbinop (op, e1, e2) -> (match op with
      | Beq | Bne -> (let a1,rt = expr env e1 and a2,rt2 = expr env e2 in 
            (match (eq_type a1.expr_typ a2.expr_typ) && (e1.pexpr_desc <> PEnil || e2.pexpr_desc <> PEnil) with
            | false -> error e1.pexpr_loc ("this expression has type "^(print_type a1.expr_typ)^ " but is expected to have type "^(print_type a2.expr_typ))
            | true -> TEbinop(op,a1,a2), Tbool, false))
  
      | Badd | Bsub | Bmul | Bdiv | Bmod -> (let a1,rt = expr env e1 and a2,rt2 = expr env e2 in
            (match (eq_type a1.expr_typ Tint) && (eq_type a2.expr_typ Tint) with
              | false -> if not (eq_type a1.expr_typ Tint) then (error e1.pexpr_loc ("this expression has type "^(print_type a1.expr_typ)^ " but is expected to have type "^(print_type Tint)))
                  else (error e2.pexpr_loc ("this expression has type "^(print_type a2.expr_typ)^ " but is expected to have type "^(print_type Tint)))
              | true -> TEbinop(op,a1,a2), Tint, false))
                              
      | Blt | Ble | Bgt | Bge -> (let a1,rt = expr env e1 and a2,rt2 = expr env e2 in
            (match (eq_type a1.expr_typ Tint) && (eq_type a2.expr_typ Tint) with
            | false -> if not (eq_type a1.expr_typ Tint) then (error e1.pexpr_loc ("this expression has type "^(print_type a1.expr_typ)^ " but is expected to have type "^(print_type Tint)))
                else (error e2.pexpr_loc ("this expression has type "^(print_type a2.expr_typ)^ " but is expected to have type "^(print_type Tint)))
            | true -> TEbinop(op,a1,a2), Tbool, false))
                              
      | Band | Bor -> (let a1,rt = expr env e1 and a2,rt2 = expr env e2 in
            (match (eq_type a1.expr_typ Tbool) && (eq_type a2.expr_typ Tbool) with
              | false -> if not (eq_type a1.expr_typ Tbool) then (error e1.pexpr_loc ("this expression has type "^(print_type a1.expr_typ)^ " but is expected to have type "^(print_type Tbool)))
                  else (error e2.pexpr_loc ("this expression has type "^(print_type a2.expr_typ)^ " but is expected to have type "^(print_type Tbool)))
              | true -> TEbinop(op,a1,a2), Tbool, false)))


  | PEunop (Uamp, e1) -> (let a1,rt = expr env e1 in
      if (left_value a1) then (TEunop(Uamp, a1),Tptr a1.expr_typ,false)
      else (error e1.pexpr_loc ("this expression is expected to be a l-value")))

  | PEunop (Uneg | Unot | Ustar as op, e1) -> (let a1,rt = expr env e1 in
        (match op with 
          |Uneg -> if (eq_type a1.expr_typ Tint) then (TEunop(Uneg, a1), Tint, false) else (error e1.pexpr_loc ("this expression has type "^(print_type a1.expr_typ)^ " but is expected to have type "^(print_type Tint)))
          |Unot ->if (eq_type a1.expr_typ Tbool) then (TEunop(Unot, a1), Tbool, false) else (error e1.pexpr_loc ("this expression has type "^(print_type a1.expr_typ)^ " but is expected to have type "^(print_type Tbool)))
          |Ustar -> if (eq_type a1.expr_typ (Tptr Twild)) && (e1.pexpr_desc <> PEnil) then (TEunop(Ustar, a1), Tptr (a1.expr_typ), false) else (error e1.pexpr_loc ("this expression has type "^(print_type a1.expr_typ)^ " but is expected to have type pointer"))
        ))

  | PEcall ({id = "fmt.Print"}, el) ->
      let rec aux = function | [] -> []
                            | t::q -> (t.expr_typ) :: (aux q) 
      in
      let l = List.map (compo fst (expr env)) el in
      (fmt_used := true; TEprint l, Tmany (aux l), false)
  
  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) ->  (*on a une liste avec une seule expression PEident {id}*)
      let ty = match id with
        | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
        | _ -> (* TODO *) error loc ("no such type " ^ id) in
      TEnew ty, Tptr ty, false

  | PEcall ({id="new"}, _) ->
      error loc "new expects a type"
  | PEcall (id, el) ->
      (* TODO *) assert false
  | PEfor (e, b) ->
      (* TODO *) assert false
  | PEif (e1, e2, e3) ->
      (* TODO *) assert false
  | PEnil ->
      TEnil, Tptr Twild, false (*nil est de type pointeur vers n'importe quel autre type*)
  | PEident {id=id} ->
      (* TODO *) (try let v = Env.find id env in TEident v, v.v_typ, false
                  with Not_found -> error loc ("unbound variable " ^ id))
  | PEdot (e, id) ->
      (* TODO *) assert false
  | PEassign (lvl, el) ->
      (* TODO *) TEassign ([], []), tvoid, false 
  | PEreturn el ->
      (* TODO *) TEreturn [], tvoid, true
  | PEblock el ->
      (* TODO *) TEblock [], tvoid, false
  | PEincdec (e, op) ->
      (* TODO *) assert false
  | PEvars _ ->
      (* TODO *) assert false 


let found_main = ref false

(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id = id; loc = loc }} -> (* TODO *) ()
  | PDfunction _ -> ()

let sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | _ -> (* TODO *) assert false 

(* 2. declare functions and type fields *)
let phase2 = function
  | PDfunction { pf_name={id; loc}; pf_params=pl; pf_typ=tyl; } ->
     (* TODO *) (if id = "main" then found_main := true) 
  | PDstruct { ps_name = {id}; ps_fields = fl } ->
     (* TODO *) () 

(* 3. type check function bodies *)
let decl = function
  | PDfunction { pf_name={id; loc}; pf_body = e; pf_typ=tyl } ->
    (* TODO check name and type *) 
    let f = { fn_name = id; fn_params = []; fn_typ = []} in
    let e, rt = expr Env.empty e in
    TDfunction (f, e)
  | PDstruct {ps_name={id}} ->
    (* TODO *) let s = { s_name = id; s_fields = Hashtbl.create 5; s_size = 0 } in
     TDstruct s

let file ~debug:b (imp, dl) =
  debug := b;
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env.check_unused (); (* TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
