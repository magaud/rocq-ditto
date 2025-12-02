open Proof
open Vernacexpr
open Evd
open Environ
open Ppconstr
open Libnames
open Pputils
open Constrexpr

let charlist_of_string s =
  let rec trav l i =
    if i = l then [] else s.[i]::trav l (i+1)
  in
  trav (String.length s) 0;;

let rec replace_patterns_aux str =
  match str with
    [] -> ""
  | x :: [] -> String.make 1 x
  | '~' :: str2 -> "\u{00AC}" ^ replace_patterns_aux str2
  | '<' :: '>' :: str2 -> "\u{2260}" ^ replace_patterns_aux str2
  (* | 'n' :: 'a' :: 't' :: str2 -> "Nat" ^ replace_patterns_aux str2*)
  | x2 :: str2 -> String.make 1 x2 ^ replace_patterns_aux str2;;

let replace_patterns str = replace_patterns_aux (charlist_of_string str);;

let lean_string_of_ppcmds t = replace_patterns (Pp.string_of_ppcmds t)

let is_prefix (prefix : string) (s : string) =
  let plen = String.length prefix in
   String.length s >= plen && String.sub s 0 plen = prefix

let split_prefix (prefix : string) (s : string) =
  let plen = String.length prefix in
  if String.length s >= plen && String.sub s 0 plen = prefix then
    Some (prefix, String.sub s plen (String.length s - plen))
  else None
         (*
           type local_decl_expr =
  | AssumExpr of lname * local_binder_expr list * constr_expr
  | DefExpr of lname * local_binder_expr list * constr_expr * constr_expr option
          *)
let x_to_string (t : (local_decl_expr * record_field_attr_unparsed) list) =
  "\n" ^ String.concat "\n" (List.map (fun (lde, rfau) ->
                        match lde with
                          AssumExpr (ln, lbel, ce) ->
                           lean_string_of_ppcmds (pr_lname ln) ^ " " ^
                             lean_string_of_ppcmds (pr_binders empty_env  empty lbel) ^ " : " ^
                             lean_string_of_ppcmds (pr_top ce)
                        | DefExpr (ln, lbel, ce, ceo) ->
                           lean_string_of_ppcmds (pr_lname ln) ^ " " ^ 
                             lean_string_of_ppcmds (pr_binders empty_env  empty lbel) ^
                               " := " ^ lean_string_of_ppcmds (pr_top ce))
                      t) ^ "\n"

let ind_expr_to_string (i : inductive_expr) : string =
  match i with ((cf , (li, cido)), ipe,_ (*ce*), clrde) ->
                (*type inductive_params_expr = local_binder_expr list * local_binder_expr list option*)

    let s_li = lean_string_of_ppcmds (pr_qualid (qualid_of_lident li)) in

    let s_lbel =  match ipe with (lbel1, lbel2) ->
        let s_lbel1 =
          String.concat "" (List.map (function x -> match x with
                                               CLocalAssum (ll,rie,bk,ce) -> " extends " ^ (lean_string_of_ppcmds (pr_top ce))
                                             | CLocalDef    (_,_,_,_) -> "CLocalDef?"
                                             | CLocalPattern _ -> "CLocalPattern?") lbel1) in 



        (* (lean_string_of_ppcmds (pr_binders empty_env  empty lbel1)) in *)

                                  let s_lbel2 =   match lbel2 with Some l ->
                                                                       (lean_string_of_ppcmds (pr_binders empty_env  empty l))
                                                                    | None -> "" in 
                                  s_lbel1 ^ s_lbel2 in

    (*let status_lbel1 = match ipe with (lbel1, lbel2) ->
      String.concat "" (List.map (function x -> match x with
                                               CLocalAssum (ll,rie,bk,ce) -> "CLocalAssum extends " ^ (lean_string_of_ppcmds (pr_top ce))
                                             | CLocalDef    (_,_,_,_) -> "CLocalDef"
                                             | CLocalPattern _ -> "CLocalPattern") lbel1) in *)
    (*let status_lbel2 = match ipe with (lbel1, lbel2) ->
        String.concat "" (match lbel2 with Some x -> (List.map (function x -> match x with
                                               CLocalAssum (_,_,_,_) -> "CLocalAssum2"
                                             | CLocalDef    (_,_,_,_) -> "CLocalDef2"
                                             | CLocalPattern _ -> "CLocalPattern2") x)  | None -> [""]) in*)
    let s_clrde = match clrde with
       Constructors lc ->
       String.concat " | " (List.map
                              (fun (_, (lin, co_exp)) -> lean_string_of_ppcmds (pr_qualid (qualid_of_lident lin))
^ " : " ^lean_string_of_ppcmds  (pr_top co_exp) ^ "\n"
                              ) lc)
                      | RecordDecl (lid1_o, l,  lid2_o) ->
                         let s_l1 =
                           match lid1_o with
                             Some l1 -> lean_string_of_ppcmds (pr_qualid (qualid_of_lident l1))
                           | None -> ""
                         in
                         let s_l = x_to_string l
                         in
                         let s_l2 =
                           match lid2_o with
                             Some l2 -> lean_string_of_ppcmds (pr_qualid (qualid_of_lident l2))
                           | None -> ""
                         in s_l1 ^ s_l ^ s_l2
    in
    s_li ^  s_lbel ^ " where " ^ s_clrde

(*                                 Some e -> "v" | None -> "nothing" *)


let indto_string (i : inductive_kind * (inductive_expr * notation_declaration list) list) : string =
  match i with
    (ik, l) -> let keyword =  (match ik with
                    Inductive_kw -> "inductive "
                  | CoInductive -> "coinductive? "
                  | Variant -> "variant? "
                  | Record -> "record? "
                  | Structure -> "structure? "
                  | Class b -> "class ") in
keyword ^ String.concat "" (List.map (fun (ind_expr, ndl) -> ind_expr_to_string ind_expr) l)
(* VernacInductive of inductive_kind * (inductive_expr * notation_declaration list) list *)
(* type inductive_expr =
   cumul_ident_decl with_coercion
   * inductive_params_expr * constr_expr option
   * constructor_list_or_record_decl_expr
   *)



let rocq_to_lean (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  (* let proofs = Rocq_document.get_proofs doc in *)

  (* Lemma, Theorem, *)
  let lemma_nodes =
    List.filter Syntax_node.is_syntax_node_proof_start doc.elements
  in
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
                  | Lemma -> "lemma"
                  | Fact -> "lemma"
                  | Remark -> "lemma"
                  | Property -> "lemma"
                  | Proposition -> "lemma"
                  | Corollary ->  "lemma" in
                let s_pel =String.concat ""
                              (List.map (fun x -> match x with ((li,udeo), (lbel,ce)) -> lean_string_of_ppcmds (pr_lident li)) pel)
                in

                let lean_phrase = s_theorem ^ " " ^ s_pel in
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

  (* Proof command *)
  let proof_command_nodes =
    List.filter Syntax_node.is_syntax_node_proof_command doc.elements
  in
  let replace_proof_command_nodes = List.map (fun (x : Syntax_node.t) -> Remove x.id) proof_command_nodes
  in

  (* proof nodes *)
(*
  let tactic_nodes =
    List.filter Syntax_node.is_syntax_node_tactic doc.elements
  in
  let replace_tactic_nodes = List.map (fun (x : Syntax_node.t) -> Remove x.id) tactic_nodes
  in
 *) 
  (* end of proof : Qed or Admitted *)

 let end_proof_nodes =
    List.filter Syntax_node.is_syntax_node_proof_end doc.elements
  in
  let replace_end_proof_nodes = List.map (fun (x : Syntax_node.t) ->
                                 let node = Syntax_node.comment_syntax_node_of_string
                            ":= by admit\n" x.range.start
                          |> Result.get_ok in
                                 Replace (x.id, node)) end_proof_nodes
  in

  (* require commands *)
  let require_nodes =
    List.filter Syntax_node.is_syntax_node_require doc.elements
  in
  let replace_requires =
    List.map
      (fun (x : Syntax_node.t) ->
        match x.ast with
        | Some ast -> (
            match (Coq.Ast.to_coq ast.v).v.expr with
            | VernacSynterp synterp_expr -> (
                match synterp_expr with
                | VernacRequire (libname_qualid, export_with_cats, l) ->
                    let _ =
                      Option.map
                        (fun x -> Libnames.string_of_qualid x)
                        libname_qualid
                      |> Option.default "no name!"
                    in
                    List.map
                      (fun (qualid, _) ->
                        let libname_qualid_str =
                          match libname_qualid
                          with
                            Some libname_qualid_s -> Libnames.string_of_qualid libname_qualid_s
                          | None -> "no libname !"
                        in
                        Logs.debug (fun m -> m "libname_qualid_str: %s" libname_qualid_str);
                        let qualid_str = Libnames.string_of_qualid qualid
                        in
                        Logs.debug (fun m -> m "qualid_str: %s" qualid_str);

                        let lean_require_str =
                          if (libname_qualid_str = "GeoCoq")
                          then
                            "import GeoLean.theories." ^ qualid_str
                          else
                            if (is_prefix "GeoCoq" qualid_str)
                            then
                              let _, postfix =
                                split_prefix "GeoCoq." qualid_str |> Option.get
                              in
                              "import GeoLean.theories." ^ postfix
                            else "/- import " ^ libname_qualid_str ^ "." ^  qualid_str ^" -/"
                        in
                        let node =
                          Syntax_node.comment_syntax_node_of_string
                            lean_require_str x.range.start
                          |> Result.get_ok
                        in
                        Replace (x.id, node))
                      l
                | _ -> [])
            | VernacSynPure _ -> [])
        | None -> [])
      require_nodes
    |> List.concat
  in

  (* inductive and classes *)
  let inductives_and_classes_nodes =
    List.filter Syntax_node.is_syntax_node_inductive doc.elements
  in

  let (replace_classes : transformation_step list) =
        List.map
      (fun (x : Syntax_node.t) ->
         match x.ast with
         | Some ast -> (
           match (Coq.Ast.to_coq ast.v).v.expr with
           | VernacSynterp _ -> []
           | VernacSynPure expr -> (
             match expr with
               Vernacexpr.VernacInductive (ik,l) ->

                (*  List.map (fun  -> ) l*)

               let lean_phrase = indto_string (ik,l)
               in
               let node = Syntax_node.comment_syntax_node_of_string
                            lean_phrase x.range.start
                             |> Result.get_ok
               in
               [Replace (x.id, node)]
             | _ -> []))
         | None -> [])
      inductives_and_classes_nodes
        |> List.concat

  in

  (* beginning of section *)
let beginning_section_nodes =
    List.filter Syntax_node.is_syntax_node_section_command doc.elements
  in
  let replace_beginning_section_nodes =
    List.map
      (fun (x : Syntax_node.t) ->
        match x.ast with
        | Some ast -> (
          match (Coq.Ast.to_coq ast.v).v.expr with
          | VernacSynterp expr -> (
            match expr with
              Vernacexpr.VernacBeginSection li ->
               let lean_phrase = "section " ^ (lean_string_of_ppcmds (pr_lident li))
               in
               let node = Syntax_node.comment_syntax_node_of_string
                            lean_phrase x.range.start
                          |> Result.get_ok
               in
               [Replace (x.id, node)]
            | _ -> [])
           | VernacSynPure expr -> []
                                     )
         | None -> [])
      beginning_section_nodes
        |> List.concat

  in

  (* end of section *)
  let end_section_nodes =
    List.filter Syntax_node.is_syntax_node_end_section_command doc.elements
  in
  let replace_end_section_nodes =
    List.map
      (fun (x : Syntax_node.t) ->
        match x.ast with
        | Some ast -> (
          match (Coq.Ast.to_coq ast.v).v.expr with
          | VernacSynterp expr -> (
            match expr with
              Vernacexpr.VernacEndSegment li ->
               let lean_phrase = "end " ^ (lean_string_of_ppcmds (pr_lident li))
               in
               let node = Syntax_node.comment_syntax_node_of_string
                            lean_phrase x.range.start
                          |> Result.get_ok
               in
               [Replace (x.id, node)]
            | _ -> [])
           | VernacSynPure expr -> []
                                     )
         | None -> [])
      end_section_nodes
        |> List.concat

  in

  (* definitions *)
  let definition_nodes =
    List.filter Syntax_node.is_syntax_node_definition_command doc.elements in
  (* VernacDefinition of (discharge * Decls.definition_object_kind) * name_decl * definition_expr *)
  let replace_definition_nodes =
    List.map
      (fun (x : Syntax_node.t) ->
         match x.ast with
         | Some ast -> (
           match (Coq.Ast.to_coq ast.v).v.expr with
           | VernacSynterp _ -> []
           | VernacSynPure expr -> (
             match expr with
               Vernacexpr.VernacDefinition ((d,dok), (ln,univ),de) ->
                let body = match de with
                    ProveBody (lbel,ce) ->
                     let s_lbel = lean_string_of_ppcmds (pr_binders empty_env  empty lbel) in
                     let s_ce = lean_string_of_ppcmds (pr_top ce) in s_lbel ^ s_ce
                  | DefineBody (lbel, rreo, ce, ceo) ->
                     let s_lbel = lean_string_of_ppcmds (pr_binders empty_env  empty lbel) in
                     let s_ce = lean_string_of_ppcmds (pr_top ce) in
                let s_ceo = match ceo with Some s -> lean_string_of_ppcmds (pr_top s) | None -> "" in
                s_lbel ^ " := "^s_ce ^ s_ceo
                in

                let lean_phrase = "def " ^ lean_string_of_ppcmds (pr_lname ln) ^ " " ^ body
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

  in
  
 

  (* comments *)
  let comment_nodes =
    List.filter (fun (x : Syntax_node.t) -> Option.is_empty x.ast) doc.elements
  in
  let (replace_comments : transformation_step list) =
    List.map
      (fun (x : Syntax_node.t) ->
        let lean_comment_node =
          let new_s =
            let s = (Syntax_node.repr x)
            in String.sub s 2 (String.length s-4)
          in Syntax_node.comment_syntax_node_of_string ("/-" ^ new_s ^ "-/") x.range.start
          |> Result.get_ok
        in
        Replace (x.id, lean_comment_node))
      comment_nodes
  in
  Ok (replace_lemma_command_nodes @
        replace_proof_command_nodes @
          replace_end_proof_nodes @
          (*replace_tactic_nodes @*)
              replace_requires @
                replace_classes @
                  replace_beginning_section_nodes @
                    replace_end_section_nodes @
                      replace_definition_nodes @
                        replace_comments)
