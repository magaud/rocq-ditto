open Fleche
open Vernacexpr
module Lsp = Fleche_lsp

[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_major_version < 9]

module Procq = Pcoq

[%%endif]

type t = {
  ast : Doc.Node.Ast.t option;
  range : Code_range.t;
  repr : string Lazy.t;
  id : Uuidm.t;
  proof_id : int option;
      (* the id of the proof associated with the node if there is one *)
  diagnostics : Lang.Diagnostic.t list;
}

let repr (x : t) : string = Lazy.force x.repr

let generate_ast (code : string) :
    (Vernacexpr.vernac_control list, Error.t) result =
  let mode = Ltac_plugin.G_ltac.classic_proof_mode in
  let entry = Pvernac.main_entry (Some mode) in
  let code_stream = Gramlib.Stream.of_string code in
  let init_parser = Procq.Parsable.make code_stream in
  let rec f parser =
    try
      match Procq.Entry.parse entry parser with
      | None -> Ok []
      | Some ast -> (
          let res = f parser in
          match res with Ok elem -> Ok (ast :: elem) | Error err -> Error err)
    with Gramlib.Grammar.Error exn -> Error (Error.of_string exn)
  in
  f init_parser

let mk_vernac_control ?(loc : Loc.t option)
    (ve : synterp_vernac_expr vernac_expr_gen) : vernac_control =
  let control = [] in
  let attrs = [] in
  let expr = ve in
  let payload = { control; attrs; expr } in
  match loc with
  | Some loc -> CAst.make ~loc payload
  | None -> CAst.make payload

let are_colliding (a : t) (b : t) : bool =
  let a_line_range = (a.range.start.line, a.range.end_.line) in
  let b_line_range = (b.range.start.line, b.range.end_.line) in
  match Range_utils.common_range a_line_range b_line_range with
  | Some range ->
      let len_range = snd range - fst range + 1 in
      if len_range > 1 then true
      else
        let common_line = fst range in
        let a_line_start_char =
          if fst a_line_range < common_line then 0 else a.range.start.character
        in
        let b_line_start_char =
          if fst b_line_range < common_line then 0 else b.range.start.character
        in
        let a_line_end_char =
          if snd a_line_range > common_line then max_int
          else a.range.end_.character
        in
        let b_line_end_char =
          if snd b_line_range > common_line then max_int
          else b.range.end_.character
        in
        let a_char_range = (a_line_start_char, a_line_end_char) in
        let b_char_range = (b_line_start_char, b_line_end_char) in
        Option.has_some (Range_utils.common_range a_char_range b_char_range)
  | None -> false

let colliding_nodes (target : t) (nodes_list : t list) : t list =
  List.filter (are_colliding target) nodes_list

let compare_nodes (a : t) (b : t) : int =
  match
    Range_utils.common_range
      (a.range.start.line, a.range.end_.line)
      (b.range.start.line, b.range.end_.line)
  with
  | Some common_line_range ->
      let smallest_common = fst common_line_range in
      if a.range.start.line < smallest_common then -1
      else if b.range.start.line < smallest_common then 1
      else compare a.range.start.character b.range.start.character
  | None -> compare a.range.start.line b.range.start.line

let validate_syntax_node (x : t) : (t, Error.t) result =
  if x.range.end_.line < x.range.start.line then
    Error.string_to_or_error
      "Incorrect range: range end line is smaller than the range start line"
  else if
    x.range.start.line = x.range.end_.line
    && String.length (repr x) > x.range.end_.character - x.range.start.character
  then
    Error.string_to_or_error
      "Incorrect range: the height of the node is one and the range end \
       character minus range start character is smaller than the node \
       character size"
  else Ok x

(* TODO, is this even necessary ? *)
let comment_syntax_node_of_string (content : string)
    (start_point : Code_point.t) : (t, Error.t) result =
  let range =
    Range_utils.range_from_starting_point_and_repr start_point content
  in

  if
    range.start.line = range.end_.line
    && String.length content > range.end_.character - range.start.character
  then
    Error
      (Error.of_string
         "Incorrect range: range end character minus range start character \
          smaller than node character size")
  else
    Ok
      {
        ast = None;
        repr = lazy content;
        range;
        id = Unique_id.uuid ();
        proof_id = None;
        diagnostics = [];
      }

let syntax_node_of_string (code : string) (start_point : Code_point.t) :
    (t, Error.t) result =
  let range = Range_utils.range_from_starting_point_and_repr start_point code in
  (*offset doesn't count the newline in*)
  if
    range.start.line = range.end_.line
    && String.length code > range.end_.character - range.start.character
  then
    Error
      (Error.of_string
         "Incorrect range: range end character minus range start character \
          smaller than node character size")
  else
    match generate_ast code with
    | Ok [] -> Error (Error.of_string ("no node found in string " ^ code))
    | Ok [ x ] ->
        let node_ast : Doc.Node.Ast.t =
          { v = Coq.Ast.of_coq x; ast_info = None }
        in

        Ok
          {
            ast = Some node_ast;
            range;
            id = Unique_id.uuid ();
            (*id is set during insertion in a document*)
            repr = lazy code;
            proof_id = None;
            diagnostics = [];
          }
    | Ok (_ :: _ :: _) ->
        Error (Error.of_string ("more than one node found in string " ^ code))
    | Error err -> Error err

let remove_outer_parentheses s =
  let len = String.length s in
  if len >= 2 && s.[0] = '(' && s.[len - 2] = ')' && s.[len - 1] = '.' then
    String.sub s 1 (len - 3) ^ "."
  else s

let syntax_node_of_coq_ast (ast : Coq.Ast.t) (start_point : Code_point.t) : t =
  let coq_ast = Coq.Ast.to_coq ast in
  let repr =
    Ppvernac.pr_vernac coq_ast |> Pp.string_of_ppcmds
    |> remove_outer_parentheses
  in
  let range = Range_utils.range_from_starting_point_and_repr start_point repr in
  let node_ast : Doc.Node.Ast.t = { v = ast; ast_info = None } in
  {
    ast = Some node_ast;
    range;
    id = Unique_id.uuid ();
    (* id is set during document insertion *)
    repr = lazy repr;
    proof_id = None;
    diagnostics = [];
  }

let reformat_node (x : t) : (t, Error.t) result =
  match x.ast with
  | Some ast ->
      let start_point = x.range.start in
      Ok { (syntax_node_of_coq_ast ast.v start_point) with id = x.id }
      (* we return the same id, doesn't matter in the order of operation we do *)
  | None ->
      Error.string_to_or_error "The node need to have an AST to be reformatted"

let string_of_syntax_node (node : t) : string =
  match node.ast with
  | Some ast -> Ppvernac.pr_vernac (Coq.Ast.to_coq ast.v) |> Pp.string_of_ppcmds
  | None -> repr node

let shift_point (n_line : int) (n_char : int) (x : Code_point.t) : Code_point.t
    =
  { line = x.line + n_line; character = x.character + n_char }

let shift_range (n_line : int) (n_char : int) (x : Code_range.t) : Code_range.t
    =
  {
    start = shift_point n_line n_char x.start;
    end_ = shift_point n_line n_char x.end_;
  }

let shift_node (n_line : int) (n_char : int) (x : t) : t =
  { x with range = shift_range n_line n_char x.range }

let is_syntax_node_inductive (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacInductive _ -> true | _ -> false))
  | None -> false

let is_syntax_node_command_allowed_in_proof (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          (* Proof structuring *)
          | VernacProof _ | VernacEndProof _ | VernacAbort | VernacAbortAll
          | VernacRestart | VernacUndo _ | VernacUndoTo _ | VernacBack _
          | VernacFocus _ | VernacUnfocus | VernacUnfocused | VernacBullet _
          | VernacSubproof _ | VernacEndSubproof
          (* Queries / utilities *)
          | VernacShow _ | VernacCheckMayEval _ | VernacGlobalCheck _
          | VernacPrint _ | VernacSearch _ | VernacLocate _
          (* internal or rare ? *)
          | VernacExactProof _ | VernacValidateProof | VernacCheckGuard ->
              true
          | _ -> false))
  | None -> false

let is_syntax_node_tactic (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp synterp_expr -> (
          match synterp_expr with
          | VernacExtend (ext, _) ->
              if ext.ext_plugin = Rocq_version.ltac_ext_plugin_name then true
              else false
          | _ -> false)
      | VernacSynPure _ -> false)
  | None -> false

let is_syntax_node_proof_command (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacProof _ -> true | _ -> false))
  | None -> false

let is_syntax_node_proof_with (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacProof (Some _, _) -> true
          | _ -> false))
  | None -> false

[%%if rocq_version <= (9, 0, 1)]

let get_syntax_node_proof_with_tactic (x : t) : string option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacProof (Some raw_arg, _) ->
              let empty_env = Environ.empty_env in
              let empty_evd = Evd.empty in

              Some
                (Pp.string_of_ppcmds
                   (Pputils.pr_raw_generic empty_env empty_evd raw_arg))
          | _ -> None))
  | None -> None

[%%else]

let get_syntax_node_proof_with_tactic (x : t) : string option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacProof (Some raw_arg, _) ->
              let empty_env = Environ.empty_env in
              let empty_evd = Evd.empty in

              Some
                (Pp.string_of_ppcmds
                   (Pputils.pr_raw_generic empty_env empty_evd
                      (Gentactic.to_raw_genarg raw_arg)))
          | _ -> None))
  | None -> None

[%%endif]

let is_syntax_node_ending_with_elipsis (x : t) : bool =
  String.ends_with ~suffix:"..." (repr x)

let is_syntax_node_context (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacContext _ -> true | _ -> false))
  | None -> false

let is_syntax_node_require (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp synterp_expr -> (
          match synterp_expr with VernacRequire _ -> true | _ -> false)
      | VernacSynPure _ -> false)
  | None -> false

let is_syntax_node_function_start (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp synterp_expr -> (
          match synterp_expr with
          | VernacExtend (ext, _) ->
              ext.ext_plugin = Rocq_version.ltac_funid_plugin_name
              && ext.ext_entry = "Function"
          | _ -> false)
      | VernacSynPure _ -> false)
  | None -> false

let is_syntax_node_instance_start (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacInstance _ -> true | _ -> false))
  | None -> false

let is_syntax_node_program_instance_start (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacInstance _ ->
              let flags = (Coq.Ast.to_coq ast.v).v.attrs in

              List.exists
                (fun (flag : Attributes.vernac_flag) ->
                  let str, flag_value = flag.v in
                  str = "program")
                flags
          | _ -> false))
  | None -> false

let is_syntax_node_definition_with_proof (x : t) : bool =
  (* TODO: check if this include anonymous goals *)
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacDefinition ((_, _), _, definition_expr) -> (
              match definition_expr with ProveBody _ -> true | _ -> false)
          | _ -> false))
  | None -> false

let is_syntax_node_bullet (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacBullet _ -> true | _ -> false))
  | None -> false

let is_syntax_node_opening_bracket (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacSubproof _ -> true | _ -> false))
  | None -> false

let is_syntax_node_closing_bracket (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacEndSubproof -> true | _ -> false))
  | None -> false

let is_syntax_node_focus_command (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacFocus _ -> true | _ -> false))
  | None -> false

let is_syntax_node_focusing_goal (x : t) : bool =
  is_syntax_node_bullet x
  || is_syntax_node_focus_command x
  || is_syntax_node_opening_bracket x

let is_syntax_node_proof_start (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacStartTheoremProof _ -> true
          | _ -> false))
  | None -> false

let is_syntax_node_proof_end (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacEndProof _ -> true | _ -> false))
  | None -> false

let is_syntax_node_proof_abort (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacAbort -> true
          | Vernacexpr.VernacAbortAll ->
              true
              (*not sure what is the fundamental difference between abort and abort all *)
          | _ -> false))
  | None -> false

let get_syntax_node_extend_name (x : t) : extend_name option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp synterp_expr -> (
          match synterp_expr with
          | VernacExtend (ext, _) -> Some ext
          | _ -> None)
      | VernacSynPure _ -> None)
  | None -> None

let get_tactic_raw_generic_arguments (x : t) :
    Genarg.raw_generic_argument list option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp synterp_expr -> (
          match synterp_expr with
          | VernacExtend (ext, args) ->
              if ext.ext_plugin = Rocq_version.ltac_ext_plugin_name then
                Some args
              else None
          | _ -> None)
      | VernacSynPure _ -> None)
  | None -> None

open Raw_gen_args_converter

let get_node_ltac_elements (x : t) : ltac_elements option =
  get_tactic_raw_generic_arguments x
  |> Option.map raw_arguments_to_ltac_elements
  |> Option.flatten

let get_node_goal_selector_opt (x : t) : Goal_select_view.t option =
  get_tactic_raw_generic_arguments x
  |> Option.map raw_arguments_to_goal_selector
  |> Option.flatten

let get_node_raw_tactic_expr (x : t) :
    Ltac_plugin.Tacexpr.raw_tactic_expr option =
  get_tactic_raw_generic_arguments x
  |> Option.map raw_arguments_to_raw_tactic_expr
  |> Option.flatten

let get_node_raw_atomic_tactic_expr (x : t) :
    Ltac_plugin.Tacexpr.raw_atomic_tactic_expr option =
  let raw_expr = get_node_raw_tactic_expr x in
  Option.map Ltac.get_raw_atomic_tactic_expr raw_expr |> Option.flatten

let tactic_raw_generic_arguments_to_syntax_node (ext : extend_name)
    (args : Genarg.raw_generic_argument list) (starting_point : Code_point.t) :
    t option =
  match args with
  | [ _; _; _; _ ] ->
      let expr_syn = Vernacexpr.VernacExtend (ext, args) in
      let synterp_expr = Vernacexpr.VernacSynterp expr_syn in
      let control = mk_vernac_control synterp_expr in
      let ast_node = Coq.Ast.of_coq control in
      Some (syntax_node_of_coq_ast ast_node starting_point)
  | _ -> None

let raw_tactic_expr_to_syntax_node
    (raw_expr : Ltac_plugin.Tacexpr.raw_tactic_expr)
    ?(selector : Goal_select_view.t option) ?(use_default = false)
    (starting_point : Code_point.t) : (t, Error.t) result =
  let selector_raw_arg =
    Raw_gen_args_converter.raw_generic_argument_of_ltac_selector selector
  in
  let use_default_raw_arg =
    Raw_gen_args_converter.raw_generic_argument_of_ltac_use_default use_default
  in
  let ltac_info_arg =
    Raw_gen_args_converter.raw_generic_argument_of_empty_ltac_info ()
  in

  let raw_expr_raw_arg =
    Raw_gen_args_converter.raw_generic_argument_of_raw_tactic_expr raw_expr
  in

  let args =
    [ selector_raw_arg; ltac_info_arg; raw_expr_raw_arg; use_default_raw_arg ]
  in

  let ext = Ltac.default_extend_name in

  match tactic_raw_generic_arguments_to_syntax_node ext args starting_point with
  | Some tac -> Ok tac
  | None ->
      let empty_env = Environ.empty_env in
      let empty_evd = Evd.empty in
      let pp_str =
        Ltac_plugin.Pptactic.pr_raw_tactic empty_env empty_evd raw_expr
        |> Pp.string_of_ppcmds
      in
      Error.format_to_or_error "Error creating a syntax node from %s" pp_str

let drop_goal_selector (x : t) : t =
  let args = get_tactic_raw_generic_arguments x in
  match args with
  | Some args ->
      let args = raw_generic_argument_of_ltac_selector None :: List.tl args in
      Option.default x
        (tactic_raw_generic_arguments_to_syntax_node Ltac.default_extend_name
           args x.range.start)
  | None -> x

let add_goal_selector (x : t) (selector : Goal_select_view.t) :
    (t, Error.t) result =
  match get_node_goal_selector_opt x with
  | Some selector ->
      Error.format_to_or_error "%s already contains a goal selector: %s"
        (repr x)
        (Goal_select_view.to_string selector)
  | None -> (
      match get_node_raw_tactic_expr x with
      | Some expr ->
          raw_tactic_expr_to_syntax_node expr ?selector:(Some selector)
            x.range.start
      | None ->
          Error.format_to_or_error
            "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
            (repr x))

let is_syntax_node_intros (x : t) : bool =
  let raw_tactic_expr = get_node_raw_tactic_expr x in
  let raw_atomic_expr =
    Option.map Ltac.get_raw_atomic_tactic_expr raw_tactic_expr
  in
  match Option.flatten raw_atomic_expr with
  | Some (Ltac_plugin.Tacexpr.TacIntroPattern _) -> true
  | _ -> false

(* single-pass validation + conversion *)
let l_to_raw_tactics (l : t list) =
  let rec aux (acc : Ltac_plugin.Tacexpr.raw_tactic_expr list) (i : int) =
    function
    | [] -> Ok (List.rev acc)
    | x :: xs -> (
        match get_node_raw_tactic_expr x with
        | Some raw -> aux (raw :: acc) (i + 1) xs
        | None ->
            Error.format_to_or_error
              "%s at index %d in l isn't convertible to a raw_tactic_expr (It \
               probably isn't Ltac)"
              (repr x) i)
  in
  aux [] 0 l

let apply_tac_thens (a : t) (l : t list)
    ?(start_point : Code_point.t = a.range.start) () : (t, Error.t) result =
  let ( let* ) = Result.bind in
  let* raw_a =
    match get_node_raw_tactic_expr a with
    | Some r -> Ok r
    | None ->
        Error.format_to_or_error
          "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
          (repr a)
  in

  let* raw_tactics_l = l_to_raw_tactics l in

  let args = get_tactic_raw_generic_arguments a |> Option.get in
  let extend = Ltac.default_extend_name in

  let a_thens_l : Ltac_plugin.Tacexpr.raw_tactic_expr =
    CAst.make (Ltac_plugin.Tacexpr.TacThens (raw_a, raw_tactics_l))
  in

  let raw_arg =
    Raw_gen_args_converter.raw_generic_argument_of_raw_tactic_expr a_thens_l
  in
  let new_args =
    [ List.nth args 0; List.nth args 1; raw_arg; List.nth args 3 ]
  in

  tactic_raw_generic_arguments_to_syntax_node extend new_args start_point
  |> Option.cata Result.ok
       (Error.format_to_or_error "failed to create a thens between %s and [%s]"
          (repr a)
          (l |> List.map repr |> String.concat "; "))

let apply_tac_then (a : t) (b : t) ?(start_point : Code_point.t = a.range.start)
    () : (t, Error.t) result =
  let ( let* ) = Result.bind in

  let* raw_a =
    match get_node_raw_tactic_expr a with
    | Some r -> Ok r
    | None ->
        Error.format_to_or_error
          "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
          (repr a)
  in
  let* raw_b =
    match get_node_raw_tactic_expr b with
    | Some r -> Ok r
    | None ->
        Error.format_to_or_error
          "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
          (repr b)
  in

  let args = get_tactic_raw_generic_arguments a |> Option.get in
  let extend = Ltac.default_extend_name in

  let a_then_b = CAst.make (Ltac_plugin.Tacexpr.TacThen (raw_a, raw_b)) in
  let raw_arg =
    Raw_gen_args_converter.raw_generic_argument_of_raw_tactic_expr a_then_b
  in
  let new_args =
    [ List.nth args 0; List.nth args 1; raw_arg; List.nth args 3 ]
  in
  tactic_raw_generic_arguments_to_syntax_node extend new_args start_point
  |> Option.cata Result.ok
       (Error.format_to_or_error "failed to create a then betwen %s and %s"
          (repr a) (repr b))

let node_can_open_proof (x : t) : bool =
  let res =
    is_syntax_node_proof_start x
    || is_syntax_node_definition_with_proof x
    || is_syntax_node_instance_start x
       && not (is_syntax_node_program_instance_start x)
       (* TODO actually treat Program and Obligation *)
    || is_syntax_node_function_start x
  in
  res

let node_can_close_proof (x : t) : bool =
  is_syntax_node_proof_abort x || is_syntax_node_proof_end x

let is_syntax_node_proof_intro_or_end (x : t) : bool =
  is_syntax_node_proof_start x
  || is_syntax_node_proof_command x
  || is_syntax_node_proof_end x
