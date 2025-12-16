open Proof
open Vernacexpr
open Evd
open Environ
open Ppconstr
open Pputils
open Ppvernac
open Vernacstate
open Names
open CAst
open Printer
open Decls

(* replace_fun_name_in_definition *)

let name_to_id (n:Name.t) = match n with Anonymous -> failwith "name_to_id"| Name i -> i

let qualid_of_lname (ln : Names.lname)= with_val (fun x -> Libnames.make_qualid DirPath.empty (name_to_id x)) ln

(*let constr_to_constr_expr (env : Environ.env) (sigma : Evd.evar_map) (c : constr) : Constr.expr =
  let pp = Printer.pr_constr_env env sigma c in
  let s = Pp.string_of_ppcmds pp in
  let lexbuf = Lexing.from_string s in
  Parser.parse_constr lexbuf
 *)

let lean_string_of_ppcmds t = Pp.string_of_ppcmds t

let replace_notation_in_constrexpr (old_notation : string)
    (new_notation : string) (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr = term

let replace_fun_name_in_constrexpr (old_fun_name : string)
    (new_fun_name : string) (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr = term

let def_kind (d:definition_object_kind) : string =
  match d with
   Definition -> "Definition "
  | Coercion -> "Coercion"
  | SubClass -> "SubClass"
  | CanonicalStructure -> "CanonicalStructure"
  | Example -> "Example"
  | Fixpoint -> "Fixpoint"
  | CoFixpoint -> "CoFixpoint"
  | Scheme -> "Scheme"
  | StructureComponent -> "StructureComponent"
  | IdentityCoercion -> "IdentityCoercion"
  | Instance -> "instance"
  | Method -> "Method"
  | Let -> "Let"
  | LetContext -> "Definition"
  
let replace_type_in_definition (doc:Rocq_document.t) (x : Syntax_node.t) : transformation_step option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacDefinition
              ( (discharge, definition_object_kind),
                (name_decl : Constrexpr.name_decl),
                expr ) -> (
            let s_kind = def_kind definition_object_kind in 
            let qid = qualid_of_lname (fst name_decl) in
            match expr with
            | ProveBody _ -> Logs.debug
                               (fun m -> m "error None"); None
            | DefineBody (binders, raw_red_expr_opt, expr1, opt_expr) ->
               let s_binders =  Pp.string_of_ppcmds (pr_binders empty_env  empty binders) in
               let s_expr = Pp.string_of_ppcmds (pr_top  expr1) in
               let s_opt_expr = (*match opt_expr with
                   Some s -> Pp.string_of_ppcmds (pr_top s)
                 | None ->*)
                    let token = Coq.Limits.Token.create () in
                    let st = Runner.get_init_state doc x token |> Result.get_ok in
                    let new_state = Runner.run_node token st x in
                    match new_state with
                      Error t ->  Logs.debug (fun m -> m "Error - runner failed %s " (Error.to_string_hum t)); "rien"
                    | Ok x ->
                       let _ = unfreeze_full_state (Coq.State.to_coq x) in
                       let my_env = Global.env () in
                       let qid = qualid_of_lname (fst name_decl) in
                       let globref = Nametab.locate qid  in
                       match globref with
                         ConstRef c ->
                          let type_c = (Environ.lookup_constant c my_env).Declarations.const_type in
                          let _ = Logs.debug
                            (fun m -> m "right way %s : %s"
                                               (Pp.string_of_ppcmds (pr_global (ConstRef c)))
                                               (Pp.string_of_ppcmds (pr_constr_env my_env Evd.empty type_c))
                                   ) in (Pp.string_of_ppcmds (pr_constr_env my_env Evd.empty type_c))
                      | VarRef _ -> Logs.debug (fun m -> m "wrong way: variable"); "rien"
                      | IndRef _ -> Logs.debug (fun m -> m "wrong way: inductive"); "rien"
                      | ConstructRef _ -> Logs.debug (fun m -> m "wrong way: constructor of an inductive datatype") ; "rien"

                    
                    in 
                 
            (*let _ = 
            match expr with
              | ProveBody _ -> Logs.debug
                           (fun m -> m "error None"); None
              | DefineBody (binders, raw_red_expr_opt, expr1, opt_expr) ->
                 let _ = Logs.debug
                           (fun m -> m "1/expr1 is %s"
                                       (Pp.string_of_ppcmds (pr_constr_expr (Global.env()) Evd.empty expr1))) in
                 let _ = match opt_expr with
                     None -> Logs.debug (fun m -> m "2/no type")
                   | Some c ->
                      Logs.debug (fun m -> m "2/opt_expr is %s"
                                             (Pp.string_of_ppcmds (pr_constr_expr (Global.env()) Evd.empty expr1))) in

                 let token = Coq.Limits.Token.create () in
                 let st = Runner.get_init_state doc x token |> Result.get_ok in
                 let new_state = Runner.run_node token st x in

                 
                   match new_state with
                     Error t ->  Logs.debug (fun m -> m "Error - runner failed %s " (Error.to_string_hum t))
                   | Ok x ->
                      let _ = unfreeze_full_state (Coq.State.to_coq x) in
                      let my_env = Global.env () in
                      let qid = qualid_of_lname (fst name_decl) in
                      let globref = Nametab.locate qid  in
                      match globref with
                        ConstRef c ->
                         let type_c = (Environ.lookup_constant c my_env).Declarations.const_type in
                          Logs.debug
                                   (fun m -> m "globref inspection %s : %s"
                                               (Pp.string_of_ppcmds (pr_global (ConstRef c)))
                                               (Pp.string_of_ppcmds (pr_constr_env my_env Evd.empty type_c))
                                   ) 
                      | VarRef _ -> Logs.debug (fun m -> m "wrong way: variable")
                      | IndRef _ -> Logs.debug (fun m -> m "wrong way: inductive")
                      | ConstructRef _ -> Logs.debug (fun m -> m "wrong way: constructor of an inductive datatype") 

                 in*)
                 
                 (* pr_constr_env : to print a constr *)
                 (*                 let ( let* ) = Result.bind in*)
                    let new_string =
                      if (s_binders="")
                      then
                        s_kind ^ Pp.string_of_ppcmds (pr_qualid qid) ^ " : " ^ s_opt_expr^ " := " ^ s_expr ^ "."
                      else
                        s_kind ^ Pp.string_of_ppcmds (pr_qualid qid) ^ " : " ^ s_opt_expr^ " := fun " ^  s_binders ^ " => " ^ s_expr ^ "."  in
                 let _ = Logs.debug (fun m -> m "string:%s:" new_string) in
                 let new_node =
                   Syntax_node.syntax_node_of_string new_string x.range.start |> Result.get_ok
                 in
                 Some (Replace (x.id, new_node)))
          | _ -> None))
  | None -> None

let replace_notation_in_definition (old_notation : string)
    (new_notation : string) (x : Syntax_node.t) : transformation_step option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacDefinition
              ( (discharge, definition_object_kind),
                (name_decl : Constrexpr.name_decl),
                expr ) -> (
              match expr with
              | ProveBody _ -> None
              | DefineBody (binders, raw_red_expr_opt, expr1, opt_expr) ->
                  let replace_map =
                    replace_notation_in_constrexpr old_notation new_notation
                  in

                  let new_expr, did_replace =
                    Expr_substitution.constr_expr_map replace_map expr1
                  in

                  if did_replace then
                    let new_define_body =
                      DefineBody (binders, raw_red_expr_opt, new_expr, opt_expr)
                    in
                    let new_vernacexpr =
                      VernacSynPure
                        (VernacDefinition
                           ( (discharge, definition_object_kind),
                             name_decl,
                             new_define_body ))
                    in
                    let new_vernac_control =
                      Syntax_node.mk_vernac_control new_vernacexpr
                    in
                    let new_node =
                      Syntax_node.syntax_node_of_coq_ast
                        (Coq.Ast.of_coq new_vernac_control)
                        x.range.start
                    in
                    Some (Replace (x.id, new_node))
                  else None)
          | _ -> None))
  | None -> None

let rec strip_None l = match l with [] -> []
                                  | None::xs -> strip_None xs
                                  | (Some x) :: xs -> x :: strip_None xs

let rocq_to_typed_rocq (doc : Rocq_document.t) :
      (transformation_step list, Error.t) result =

  (* lemmas *)

  let lemma_nodes =
    List.filter Syntax_node.is_syntax_node_proof_start doc.elements in
  let replace_lemma_command_nodes =
    List.map
      (fun (x : Syntax_node.t) ->
        match x.ast with
         | Some ast -> (
           match (Coq.Ast.to_coq ast.v).v.expr with
           | VernacSynterp _ -> []
           | VernacSynPure expr -> (
             match expr with
               Vernacexpr.VernacStartTheoremProof (tk,pel) ->
               (* type proof_expr = ident_decl * (local_binder_expr list * constr_expr) *)
                let s_theorem = match tk with
                  | Theorem -> "theorem"
                  | Lemma -> "theorem"
                  | Fact -> "lemma"
                  | Remark -> "lemma"
                  | Property -> "lemma"
                  | Proposition -> "lemma"
                  | Corollary ->  "lemma" in
                let s_pel =
                  String.concat ""
                    (List.map
                       (fun x -> match x with ((li,udeo), (lbel,ce)) ->
                                   (lean_string_of_ppcmds (pr_lident li)) ^
                                     (lean_string_of_ppcmds (pr_binders empty_env  empty lbel)) ^ " : " ^ 
                                       (lean_string_of_ppcmds (pr_top ce)))
                       pel) in
                let lean_phrase = s_theorem ^ " " ^ s_pel  in
                let node = Syntax_node.comment_syntax_node_of_string
                             lean_phrase x.range.start
                             |> Result.get_ok
                in
                [Replace (x.id, node)]
             | _ -> []))
         | None -> [])
      lemma_nodes
    |> List.concat
  in

  (* Fixpoint *)
  let fixpoint_nodes =
    List.filter Syntax_node.is_syntax_node_fixpoint doc.elements in
  let replace_fixpoint_nodes =
    List.map
      (fun (x : Syntax_node.t) ->
         match x.ast with
         | Some ast -> (
           match (Coq.Ast.to_coq ast.v).v.expr with
           | VernacSynterp _ -> []
           | VernacSynPure expr -> (
             match expr with
               Vernacexpr.VernacFixpoint (discharge,(fixpoint_order_expr_option_list, recursive_expr_gen_list)) ->
              let s_f = String.concat "" (List.map (fun x -> "") fixpoint_order_expr_option_list) in
              let s_r = String.concat "" (List.map (fun x -> lean_string_of_ppcmds (pr_rec_definition (None, x))) recursive_expr_gen_list) in
              let lean_phrase = "def " ^ String.sub s_r 0 ((String.length s_r)-3) ^s_f in 
                let node = Syntax_node.comment_syntax_node_of_string
                             lean_phrase x.range.start
                             |> Result.get_ok
                in
                [Replace (x.id, node)]
             | _ -> []))
         | None -> [])
      fixpoint_nodes
    |> List.concat

  in

(* definitions *)
  let definition_nodes =
    List.filter Syntax_node.is_syntax_node_definition_command doc.elements in
  
  let replace_definition_nodes =
    strip_None (List.map (fun (x:Syntax_node.t) -> replace_type_in_definition doc x) definition_nodes)
    (*
    List.map
      (fun (x : Syntax_node.t) ->
         match x.ast with
         | Some ast -> (
           match (Coq.Ast.to_coq ast.v).v.expr with
           | VernacSynterp _ -> []
           | VernacSynPure expr -> (
             match expr with
               Vernacexpr.VernacDefinition ((d,dok), (ln,univ),de) ->
                let s_d = match dok with
                    Definition -> "def"
                  | Coercion ->  "coercion?"
                  | SubClass -> "subclass?"
                  | CanonicalStructure -> "canonicalstructure?"
                  | Example -> "def" (* using "example" fails on the lean side *)
                  | Fixpoint -> "fixpoint?"
                  | CoFixpoint -> "cofixpoint?"
                  | Scheme -> "scheme?"
                  | StructureComponent -> "structurecomponent?"
                  | IdentityCoercion -> "identitycoercion?"
                  | Instance -> "instance?"
                  | Method -> "method?"
                  | Let -> "let?"
                  | LetContext -> "letcontext?" in 

                let body = match de with
                    ProveBody (lbel,ce) ->
                     let s_lbel = lean_string_of_ppcmds (pr_binders empty_env  empty lbel) in
                     let s_ce = lean_string_of_ppcmds (pr_top ce) in s_lbel ^ ": " ^ s_ce
                  | DefineBody (lbel, rreo, ce, ceo) ->
                     let s_lbel = lean_string_of_ppcmds (pr_binders empty_env  empty lbel) in
                     let s_ce = lean_string_of_ppcmds (pr_top ce) in
                let s_ceo = match ceo with Some s -> " : " ^ lean_string_of_ppcmds (pr_top s) | None -> "" in
                s_lbel ^ s_ceo ^ " := "^s_ce
                in

                let lean_phrase = s_d ^ " " ^ lean_string_of_ppcmds (pr_lname ln) ^ " " ^ body
                in
                let node = Syntax_node.comment_syntax_node_of_string
                             lean_phrase x.range.start
                             |> Result.get_ok
                in
                [Replace (x.id, node)]
             | _ -> []))
         | None -> [])
      definition_nodes
    |> List.concat
     *)
  in 
  Ok (replace_lemma_command_nodes @ replace_fixpoint_nodes @ replace_definition_nodes)
