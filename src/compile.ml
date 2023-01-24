(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile 

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...

*)

open Format
open Ast
open Tast
open X86_64

exception Anomaly of string

let debug = ref false

let strings = Hashtbl.create 32
let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz" (* c'est une version améliorée de malloc
   qui met tout les bits que tu alloues à 0 et renvoie l'adresse qui pointe vers l'espace alloué (comme malloc) *)
let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  exit_label: string;
  ofs_this: int;  (*rang de la pile dans la mémoire*)
  nb_locals: int ref; (* maximum = nombre de variables locales ? Taille de la pile ?*)
  next_local: int; (* 0, 1, ... *)
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0 }

let mk_bool d = { expr_desc = d; expr_typ = Tbool }

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true ++
  movq (imm 0) (reg rdi) ++ jmp l_end ++
  label l_true ++ movq (imm 1) (reg rdi) ++ label l_end

let typ_affichage = ref Twild
let rec expr env e = 
  let typer = e.expr_typ in
  match e.expr_desc with
  | TEskip ->
    nop
  | TEconstant (Cbool true) ->
    movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)
  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)
  | TEnil ->
    xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) ->
    movq (ilab (alloc_string s)) (reg rdi)
  | TEbinop (Band, e1, e2) ->
    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    popq rax ++
    andq (reg rax) (reg rdi)

  | TEbinop (Bor, e1, e2) ->
    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    popq rax ++
    orq (reg rax) (reg rdi)

  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) ->
    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    popq rax ++
    cmpq (reg rax) (reg rdi) ++
    movq (imm 0) (reg rdi) ++
    (match op with 
        | Blt -> setl (reg dl) ++ movsbq (reg dl) rdi  (*met 1 dans rdi si e1 < e2*)
        | Ble -> setle (reg dl) ++ movsbq (reg dl) rdi  
        | Bgt -> setg (reg dl) ++ movsbq (reg dl) rdi  
        | Bge -> setge (reg dl) ++ movsbq (reg dl) rdi  
        | _ -> nop
    )

  | TEbinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1, e2) ->
      expr env e1 ++
      pushq (reg rdi) ++
      expr env e2 ++
      popq rax ++
      (match op with
        | Badd -> addq (reg rax) (reg rdi)
        | Bsub -> subq (reg rax) (reg rdi)
        | Bmul -> imulq (reg rax) (reg rdi)
        | op2 -> (cqto ++ idivq (reg rdi) ++  (*si rdi a 0 pour valeur, il y aura une erreur retournée*)
                (match op2 with
                  | Bdiv -> movq (reg rax) (reg rdi)
                  | Bmod -> movq (reg rdx) (reg rdi)
                  | _ -> nop)))

  | TEbinop (Beq | Bne as op, e1, e2) ->
    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    popq rax ++
    cmpq (reg rax) (reg rdi) ++
    movq (imm 0) (reg rdi) ++
    (match op with
    | Beq ->  sete (reg dl) ++ movsbq (reg dl) rdi
    | Bne ->  setne (reg dl) ++  movsbq (reg dl) rdi
    | _ -> nop
    )
  
  | TEunop (Uneg, e1) ->
    expr env e1 ++
    negq (reg rdi)

  | TEunop (Unot, e1) ->
    expr env e1 ++
    notq (reg rdi)

  | TEunop (Uamp, e1) ->
    
    (* TODO code pour & *) assert false
  | TEunop (Ustar, e1) ->
    (* TODO code pour * *) assert false
  | TEprint el -> 
    (match el with 
      | [] -> nop
      | t::q -> expr env t ++ ( let a = !typ_affichage in 
                                match t.expr_typ with
                                | Tint ->( typ_affichage := Tint;
                                          (if (a <> Tint) 
                                            then (call "print_int")
                                          else (movq (reg rdi) (reg rbp)
                                          ++ movq (ilab (alloc_string " ")) (reg rdi) ++ call "printf"
                                          ++ movq (reg rbp) (reg rdi) ++ call "print_int");
                                          nop ))
                                            (*on rajoute un espace entre deux entiers*)

                                | Tstring -> (typ_affichage := Twild; 
                                             label "Twild" ++ call "printf")

                                | Tbool -> if t.expr_desc = TEconstant(Cbool false) then (expr env {expr_desc = TEprint [{expr_desc = TEconstant (Cstring "false"); expr_typ = Tstring}]; expr_typ = Twild})
                                          else (expr env {expr_desc = TEprint [{expr_desc = TEconstant (Cstring "true"); expr_typ = Tstring}]; expr_typ = Twild})
                                | _ -> nop
      ) ++ expr env {expr_desc = (TEprint q); expr_typ = typer})
    
  | TEident x ->
    (* TODO code pour x *) assert false
  | TEassign ([{expr_desc=TEident x}], [e1]) ->
    (* TODO code pour x := e *) assert false
  | TEassign ([lv], [e1]) ->
    (* TODO code pour x1,... := e1,... *) assert false
  | TEassign (_, _) ->
     assert false
  | TEblock el -> (match el with 
      | [] -> nop
      | t::q -> expr env t ++ expr env {expr_desc = (TEblock q); expr_typ = typer})
     
  | TEif (e1, e2, e3) ->
     (* TODO code pour if *) assert false
  | TEfor (e1, e2) ->
     (* TODO code pour for *) assert false
  | TEnew ty ->
     (* TODO code pour new S *) assert false
  | TEcall (f, el) ->
     (* TODO code pour appel fonction *) assert false
  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false
  | TEvars _ ->
     assert false (* fait dans block *)
  | TEreturn [] ->
    (* TODO code pour return e *) assert false
  | TEreturn [e1] ->
    (* TODO code pour return e1,... *) assert false
  | TEreturn _ ->
     assert false
  | TEincdec (e1, op) ->
    (* TODO code pour return e++, e-- *) assert false

let typ_affichage = ref Twild

let function_ f e env =
  if !debug then eprintf "function %s:@." f.fn_name;
  (* TODO code pour fonction *) label ("F_" ^ f.fn_name) ++
  expr env e
  ++ ret

let decl env code = function
  | TDfunction (f, e) -> code ++ function_ f e env
  | TDstruct _ -> code

let file ?debug:(b=false) dl =
  debug := b;
  let env = empty_env in
  (* TODO calcul offset champs *)
  (* TODO code fonctions *) let funs = List.fold_left (decl env) nop dl in
  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      funs ++
      inline "
print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret
"; (* TODO print pour d'autres valeurs *)
   (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld" ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
