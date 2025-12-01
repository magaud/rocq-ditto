open Fleche
open Syntax_node
open Vernacexpr
open Nary_tree

type proof_status = Admitted | Proved | Aborted
[@@deriving show { with_path = false }]

type attach_position = LineAfter | LineBefore | SameLine
[@@deriving show { with_path = false }]

type transformation_step =
  | Remove of Uuidm.t
  | Replace of Uuidm.t * Syntax_node.t
  | Add of Syntax_node.t
  | Attach of Syntax_node.t * attach_position * Uuidm.t

let pp_transformation_step (fmt : Format.formatter) (step : transformation_step)
    : unit =
  match step with
  | Remove id -> Format.fprintf fmt "Remove(%s)." (Uuidm.to_string id)
  | Replace (id, new_node) ->
      if new_node.range.start.line != new_node.range.end_.line then
        Format.fprintf fmt "Replace(%s, %s) at %s" (Uuidm.to_string id)
          (repr new_node)
          (Code_range.to_string new_node.range)
  | Add new_node ->
      Format.fprintf fmt "Add(%s) at %s" (repr new_node)
        (Code_range.to_string new_node.range)
  | Attach (attached_node, attach_position, anchor_id) ->
      Format.fprintf fmt "Attach(%s, %s, %s)" (repr attached_node)
        (Uuidm.to_string anchor_id)
        (show_attach_position attach_position)

let transformation_step_to_string (step : transformation_step) : string =
  Format.asprintf "%a" pp_transformation_step step

(* TODO add precisions *)

type t = {
  proposition : Syntax_node.t;
  proof_steps : Syntax_node.t list;
  status : proof_status;
}
(* proposition can also be a type, better name ? *)

(* A node can have multiple names (ie mutual recursive defs) *)
let get_names (node : Syntax_node.t) : string list =
  match node.ast with
  | Some ast -> (
      match ast.ast_info with
      | Some infos ->
          List.concat_map
            (fun (info : Lang.Ast.Info.t) ->
              match info.name.v with None -> [] | Some s -> [ s ])
            infos
      | None -> [])
  | None -> []

let get_theorem_kind (x : t) : Decls.theorem_kind option =
  let coq_ast =
    Option.map
      (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v)
      x.proposition.ast
  in
  match coq_ast with
  | Some ast -> (
      match ast.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | VernacStartTheoremProof (kind, _) -> Some kind
          | _ -> None))
  | None -> None

let get_constr_expr (x : t) : Constrexpr.constr_expr option =
  let coq_ast =
    Option.map
      (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v)
      x.proposition.ast
  in
  match coq_ast with
  | Some ast -> (
      match ast.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | Vernacexpr.VernacStartTheoremProof (_, [ ((_, _), (_, expr)) ]) ->
              Some expr
          | _ -> None))
  | None -> None

type theorem_components = {
  kind : Decls.theorem_kind;
  name : Names.lident;
  universe : Constrexpr.universe_decl_expr option;
  binders : Constrexpr.local_binder_expr list;
  expr : Constrexpr.constr_expr;
}

let get_theorem_components (x : t) : theorem_components option =
  let coq_ast =
    Option.map
      (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v)
      x.proposition.ast
  in
  match coq_ast with
  | Some ast -> (
      match ast.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | Vernacexpr.VernacStartTheoremProof
              (kind, [ ((name, universe), (binders, expr)) ]) ->
              Some { kind; name; universe; binders; expr }
          | _ -> None))
  | None -> None

let syntax_node_of_theorem_components (c : theorem_components)
    (start_point : Code_point.t) : Syntax_node.t =
  let expr_syn =
    Vernacexpr.VernacStartTheoremProof
      (c.kind, [ ((c.name, c.universe), (c.binders, c.expr)) ])
  in
  let synpure_expr = VernacSynPure expr_syn in
  let control = Syntax_node.mk_vernac_control synpure_expr in
  let coq_ast = Coq.Ast.of_coq control in
  Syntax_node.syntax_node_of_coq_ast coq_ast start_point

let proof_status_from_last_node (node : Syntax_node.t) :
    (proof_status, Error.t) result =
  match node.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> Error.string_to_or_error "not a valid closing node"
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacEndProof proof_end -> (
              match proof_end with
              | Admitted -> Ok Admitted
              | Proved _ -> Ok Proved)
          | Vernacexpr.VernacAbort -> Ok Aborted
          | Vernacexpr.VernacAbortAll -> Ok Aborted
          | _ -> Error.string_to_or_error "not a valid closing node"))
  | None -> Error.string_to_or_error "not a valid closing node (no ast)"

let get_proof_name (p : t) : string option =
  List.nth_opt (get_names p.proposition) 0

let get_proof_status (p : t) : proof_status option =
  match p.proof_steps with
  | [] -> None
  | steps ->
      let rec last = function
        | [ x ] -> x
        | _ :: xs -> last xs
        | [] -> assert false
      in
      proof_status_from_last_node (last steps) |> Result.to_option

let rec print_tree (tree : Syntax_node.t nary_tree) (indent : string) : unit =
  match tree with
  | Node (value, children) ->
      Printf.printf "%sNode(%s)\n" indent (repr value);
      List.iter (fun child -> print_tree child (indent ^ "  ")) children

let proof_nodes (p : t) : Syntax_node.t list = p.proposition :: p.proof_steps

let proof_from_nodes (nodes : Syntax_node.t list) : (t, Error.t) result =
  if List.length nodes < 2 then
    Error.string_to_or_error
      ("Not enough elements to create a proof from the nodes.\nnodes: "
      ^ String.concat ""
          (List.map
             (fun node ->
               repr node ^ " range:" ^ Code_range.to_string node.range)
             nodes))
  else
    let last_node_status =
      List.hd (List.rev nodes) |> proof_status_from_last_node
    in
    match last_node_status with
    | Ok status ->
        Ok { proposition = List.hd nodes; proof_steps = List.tl nodes; status }
    | Error err -> Error err
