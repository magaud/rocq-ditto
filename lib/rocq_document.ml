open Proof
open Fleche
open Syntax_node

type proofState = NoProof | ProofOpened

type t = {
  filename : string;
  elements : Syntax_node.t list;
  document_repr : string;
  initial_state : Coq.State.t;
}

type removeMethod = LeaveBlank | ShiftNode
type shiftMethod = ShiftVertically | ShiftHorizontally

let pp_coq_document (fmt : Format.formatter) (doc : t) : unit =
  Format.fprintf fmt "filename: %s@ " doc.filename;
  Format.fprintf fmt "elements:@ ";

  List.iter
    (fun node ->
      Format.fprintf fmt "%a %s@ " Code_range.pp node.range (repr node))
      (* see to add id maybe ? *)
    doc.elements;

  Format.fprintf fmt "document repr: %s" doc.document_repr

let get_proofs (doc : t) : (Proof.t list, Error.t) result =
  let rec aux (nodes : Syntax_node.t list) (cur_proof_acc : Syntax_node.t list)
      (proofs_acc : (Proof.t, Error.t) result list) (cur_state : proofState) :
      (Proof.t, Error.t) result list =
    match nodes with
    | [] -> proofs_acc
    | x :: tail -> (
        if Syntax_node.node_can_open_proof x then
          aux tail [ x ] proofs_acc ProofOpened
        else if Syntax_node.node_can_close_proof x then
          if List.is_empty cur_proof_acc then
            aux tail [] proofs_acc
              NoProof (* TODO: proper handling of Program and Obligation *)
          else
            let proof = proof_from_nodes (List.rev (x :: cur_proof_acc)) in
            aux tail [] (proof :: proofs_acc) NoProof
        else
          match cur_state with
          | NoProof -> aux tail [] proofs_acc NoProof
          | ProofOpened -> aux tail (x :: cur_proof_acc) proofs_acc ProofOpened)
  in

  let res = aux doc.elements [] [] NoProof in
  let err_opt =
    List.find_opt (fun proof_res -> Result.is_error proof_res) res
  in
  match err_opt with
  | Some error -> Error (Result.get_error error)
  | None -> Ok (List.rev (List.map Result.get_ok res))

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let get_line_col_positions text pos : Code_point.t =
  let rec aux line col index =
    if index = pos then (line, col, index)
    else if index >= String.length text then (line, col, index)
    else if text.[index] = '\n' then aux (line + 1) 0 (index + 1)
    else aux line (col + 1) (index + 1)
  in

  let line, character, _ = aux 0 0 0 in
  (* Start from line 0, column 0, character 0 *)
  { line; character }

let offset_of_code_point (doc : t) (p : Code_point.t) =
  let lines = String.split_on_char '\n' doc.document_repr in
  let rec sum_lengths acc idx =
    if idx = 0 then acc
    else
      sum_lengths (acc + String.length (List.nth lines (idx - 1)) + 1) (idx - 1)
  in
  let before_lines_len = sum_lengths 0 p.line in
  before_lines_len + p.character

let mark_string_regions (s : string) : bool array =
  let n = String.length s in
  let rec loop i in_string escape acc =
    if i = n then Array.of_list (List.rev acc)
    else
      let c = s.[i] in

      if in_string then
        let acc' = true :: acc in
        if escape then loop (i + 1) true false acc'
        else begin
          match c with
          | '\\' -> loop (i + 1) true true acc'
          | '"' -> loop (i + 1) false false acc'
          | _ -> loop (i + 1) true false acc'
        end
      else
        (* Outside a string *)
        let acc' = false :: acc in
        match c with
        | '"' -> loop (i + 1) true false acc'
        | _ -> loop (i + 1) false false acc'
  in
  loop 0 false false []

let get_comments (content : string) :
    ((string * Code_range.t) list, string) result =
  let explode s =
    List.init (String.length s) (fun idx -> (idx, String.get s idx))
  in
  let repr = explode content in

  let ( let* ) = Result.bind in

  let pairwise lst =
    let rec aux acc = function
      | (a1, p1) :: (a2, p2) :: rest ->
          aux (((a1, p1), (a2, p2)) :: acc) ((a2, p2) :: rest)
      | _ -> List.rev acc
    in
    aux [] lst
  in

  let string_mask = mark_string_regions content in

  let pairs =
    pairwise repr |> List.filter (fun ((i, _), _) -> not string_mask.(i))
  in
  let* _, res =
    List.fold_left
      (fun acc pair ->
        match acc with
        | Ok (stack, res) as acc -> (
            match pair with
            | ((_, '('), (_, '*')) as x -> Ok (x :: stack, res)
            | (idx1, '*'), (idx2, ')') -> (
                match stack with
                | ((idx3, '('), (idx4, '*')) :: t ->
                    Ok (t, ((idx3, idx4), (idx1, idx2)) :: res)
                | [] ->
                    acc
                    (* we might have encountered: try (rewrite IHn in *\) for example *)
                | _ -> Error "unmatched ending comment")
            | _ -> acc)
        | Error err -> Error err)
      (Ok ([], []))
      pairs
  in

  Ok
    (List.map
       (fun ((a, _), (_, d)) ->
         let len = d - a + 1 in
         let str = String.sub content a len in

         let range : Code_range.t =
           {
             start = get_line_col_positions content a;
             end_ = get_line_col_positions content d;
           }
         in
         (str, range))
       res)

let compare_code_point (p1 : Code_point.t) (p2 : Code_point.t) : int =
  match Int.compare p1.line p2.line with
  | 0 -> Int.compare p1.character p2.character
  | c -> c

let second_node_included_in (a : Syntax_node.t) (b : Syntax_node.t) : bool =
  compare_code_point a.range.start b.range.start <= 0
  && compare_code_point b.range.end_ a.range.end_ <= 0

let merge_nodes (nodes : Syntax_node.t list) : Syntax_node.t list =
  let rec merge_aux (acc : Syntax_node.t list) (nodes : Syntax_node.t list) =
    match nodes with
    | [] -> List.rev acc
    | curr_node :: rest -> (
        match acc with
        | acc_node :: _ when second_node_included_in acc_node curr_node ->
            merge_aux acc rest
        | _ -> merge_aux (curr_node :: acc) rest)
  in
  merge_aux [] nodes

let parse_document (doc : Doc.t) : t =
  let nodes = doc.nodes in
  let document_repr = doc.contents.raw in
  let filename = Lang.LUri.File.to_string_uri doc.uri in

  let nodes_with_ast =
    List.filter (fun elem -> Option.has_some (Doc.Node.ast elem)) nodes
  in

  let ast_nodes =
    List.map
      (fun (node : Doc.Node.t) ->
        {
          ast = node.ast;
          range = Code_range.code_range_from_lang_range node.range;
          repr = lazy (node_representation node document_repr);
          id = Unique_id.uuid ();
          proof_id = None;
          diagnostics = node.diags;
        })
      nodes_with_ast
  in

  let comments = get_comments document_repr |> Result.get_ok in

  let comments_nodes =
    List.map
      (fun comment ->
        {
          ast = None;
          range = snd comment;
          repr = lazy (fst comment);
          id = Unique_id.uuid ();
          proof_id = None;
          diagnostics = [];
        })
      comments
  in

  let all_nodes =
    merge_nodes
      (List.sort Syntax_node.compare_nodes (ast_nodes @ comments_nodes))
  in
  let all_nodes_with_growing_ids =
    List.map (fun node -> { node with id = Unique_id.uuid () }) all_nodes
  in

  {
    elements = all_nodes_with_growing_ids;
    document_repr;
    filename;
    initial_state = doc.root;
  }

let dump_elements_to_string (elements : Syntax_node.t list) :
    (string, Error.t) result =
  let rec aux (repr_nodes : Syntax_node.t list) (doc_repr : string)
      (previous_node : Syntax_node.t) : (string, Error.t) result =
    match repr_nodes with
    | [] -> Ok doc_repr
    | node :: tail -> (
        let line_diff = node.range.start.line - previous_node.range.end_.line in
        let result =
          if previous_node.range = node.range then
            (* first node: potentially empty lines before *)
            Ok
              (doc_repr
              ^ String.make node.range.start.line '\n'
              ^ String.make node.range.start.character ' '
              ^ repr node)
          else if node.range.start.line = previous_node.range.end_.line then
            let char_diff =
              node.range.start.character - previous_node.range.end_.character
            in
            if char_diff < 0 then
              Error
                (Error.of_string
                   ("Error: node start - previous end char negative"
                  ^ "\nprevious node range: "
                   ^ Code_range.to_string previous_node.range
                   ^ "\ncurrent node range: "
                   ^ Code_range.to_string node.range))
            else Ok (doc_repr ^ String.make char_diff ' ' ^ repr node)
          else if line_diff <= 0 then
            Error
              (Error.of_string
                 ("line diff negative" ^ "\nprevious node range: "
                 ^ Code_range.to_string previous_node.range
                 ^ "\ncurrent node range: "
                 ^ Code_range.to_string node.range))
          else
            Ok
              (doc_repr ^ String.make line_diff '\n'
              ^ String.make node.range.start.character ' '
              ^ repr node)
        in
        match result with
        | Error _ as e -> e
        | Ok updated_doc -> aux tail updated_doc node)
  in
  match elements with
  | [] -> Ok "" (* or maybe Error "Empty document"? *)
  | first :: tail ->
      let sorted_elements = List.sort compare_nodes (first :: tail) in
      aux sorted_elements "" first

let dump_to_string (doc : t) : (string, Error.t) result =
  dump_elements_to_string doc.elements

let element_with_id_opt (element_id : Uuidm.t) (doc : t) : Syntax_node.t option
    =
  List.find_opt (fun elem -> elem.id = element_id) doc.elements

let proof_with_id_opt (proof_id : Uuidm.t) (doc : t) : Proof.t option =
  let proofs_res = get_proofs doc in
  match proofs_res with
  | Ok proofs ->
      List.find_opt (fun elem -> elem.proposition.id = proof_id) proofs
  | Error _ -> None

let proof_with_name_opt (proof_name : string) (doc : t) : Proof.t option =
  let proof_res = get_proofs doc in
  match proof_res with
  | Ok proofs ->
      List.find_opt
        (fun proof ->
          match get_proof_name proof with
          | Some name -> name = proof_name
          | None -> false)
        proofs
  | Error _ -> None

let split_at_id (target_id : Uuidm.t) (doc : t) :
    Syntax_node.t list * Syntax_node.t list =
  let rec aux (elements : Syntax_node.t list) (acc : Syntax_node.t list) =
    match elements with
    | [] -> (acc, [])
    | x :: tail ->
        if x.id = target_id then (List.rev acc, tail) else aux tail (x :: acc)
  in
  aux doc.elements []

let elements_starting_at_line (line_number : int) (nodes : Syntax_node.t list) :
    Syntax_node.t list =
  List.filter (fun elem -> elem.range.start.line = line_number) nodes

let shift_node_first_line (n_char : int) (x : Syntax_node.t) : Syntax_node.t =
  if x.range.start.line = x.range.end_.line then shift_node 0 n_char x
  else
    {
      x with
      range =
        {
          start = shift_point 0 n_char x.range.start;
          end_ = shift_point 0 0 x.range.end_;
        };
    }

let num_chars_last_line (x : Syntax_node.t) : int =
  if x.range.start.line = x.range.end_.line then
    x.range.end_.character - x.range.start.character
  else x.range.end_.character

let remove_node_with_id (target_id : Uuidm.t) ?(remove_method = ShiftNode)
    (doc : t) : (t, Error.t) result =
  let ( let* ) = Result.bind in
  match element_with_id_opt target_id doc with
  | None ->
      Error.format_to_or_error
        "The element with id: %s wasn't found in the document"
        (Uuidm.to_string target_id)
  | Some removed_node -> (
      let before, after = split_at_id target_id doc in
      let block_height =
        removed_node.range.end_.line - removed_node.range.start.line + 1
      in

      let node_before_on_start_line =
        List.exists
          (fun x -> x.range.end_.line = removed_node.range.start.line)
          before
      in

      let nodes_after_on_end_line =
        List.exists
          (fun x -> x.range.start.line = removed_node.range.end_.line)
          after
      in

      (* each block is at least a line high *)
      match remove_method with
      | LeaveBlank ->
          let elements = before @ after in
          let* doc_repr = dump_elements_to_string elements in
          Ok { doc with elements; document_repr = doc_repr }
      | ShiftNode ->
          let line_shift =
            if node_before_on_start_line then -(block_height - 1)
            else -block_height
          in
          if nodes_after_on_end_line then
            let elements =
              before
              @ List.map
                  (fun x ->
                    if x.range.start.line = removed_node.range.end_.line then
                      shift_node_first_line
                        (-num_chars_last_line removed_node)
                        x
                    else x)
                  after
            in
            let* document_repr = dump_elements_to_string elements in
            Ok { doc with elements; document_repr }
          else
            let elements = before @ List.map (shift_node line_shift 0) after in
            let* document_repr = dump_elements_to_string elements in
            Ok { doc with elements; document_repr })

let insert_node (new_node : Syntax_node.t) ?(shift_method = ShiftVertically)
    (doc : t) : (t, Error.t) result =
  let ( let* ) = Result.bind in

  let element_before_new_node_start, element_after_new_node_start =
    List.partition (fun node -> compare_nodes node new_node < 0) doc.elements
  in

  let element_after_range_opt =
    Option.map (fun x -> x.range) (List.nth_opt element_after_new_node_start 0)
  in

  let node_offset_size = String.length (repr new_node) in

  let offset_space =
    match element_after_range_opt with
    | Some element_after_range ->
        offset_of_code_point doc element_after_range.start
        - offset_of_code_point doc new_node.range.start
        - 1
    | None -> 0
  in

  let total_shift = node_offset_size - offset_space in

  match shift_method with
  | ShiftHorizontally ->
      if new_node.range.start.line != new_node.range.end_.line then
        Error.format_to_or_error
          "Error when trying to shift %s at: %s.@.Shifting horizontally is \
           only possible with 1 line height node"
          (repr new_node)
          (Code_range.to_string new_node.range)
      else
        let multi_lines_nodes_after_same_line =
          elements_starting_at_line new_node.range.start.line
            element_after_new_node_start
          |> List.find_opt (fun node ->
              node.range.start.character > new_node.range.start.character
              && node.range.end_.line - node.range.start.line >= 1)
          |> Option.has_some
        in
        if multi_lines_nodes_after_same_line then
          Error.format_to_or_error
            "Can't shift multi-lines nodes on the same line (%d) as the node \
             inserted"
            new_node.range.start.line
        else
          let elements =
            element_before_new_node_start
            @ new_node
              :: List.map
                   (fun node ->
                     if node.range.start.line = new_node.range.start.line then
                       shift_node 0 total_shift node
                     else node)
                   element_after_new_node_start
          in
          let* document_repr = dump_elements_to_string elements in
          Ok { doc with elements; document_repr }
  | ShiftVertically ->
      let line_shift =
        if List.length (colliding_nodes new_node doc.elements) = 0 then 0
        else new_node.range.end_.line - new_node.range.start.line + 1
      in
      let elements =
        element_before_new_node_start
        @ new_node
          :: List.map
               (fun node -> shift_node line_shift 0 node)
               element_after_new_node_start
      in
      let* document_repr = dump_elements_to_string elements in
      Ok { doc with elements; document_repr }

let replace_node (target_id : Uuidm.t) (replacement : Syntax_node.t) (doc : t) :
    (t, Error.t) result =
  let ( let* ) = Result.bind in
  let* replacement = validate_syntax_node replacement in
  match element_with_id_opt target_id doc with
  | Some target ->
      let _, after_replaced = (split_at_id target.id) doc in
      let node_after_opt = List.nth_opt after_replaced 0 in

      let replacement_shifted =
        {
          replacement with
          range =
            Code_range.range_from_starting_point_and_repr target.range.start
              (repr replacement);
        }
      in

      let replacement_height =
        replacement_shifted.range.end_.line
        - replacement_shifted.range.start.line + 1
      in

      let removed_node_doc =
        remove_node_with_id ~remove_method:LeaveBlank target.id doc
        |> Result.get_ok
        (* we already checked for the node existence *)
      in

      let has_same_lines_elements =
        List.exists
          (fun node ->
            node.id != target.id
            && node.range.start.line = target.range.end_.line)
          removed_node_doc.elements
      in

      if has_same_lines_elements && replacement_height = 1 then
        insert_node replacement_shifted ~shift_method:ShiftHorizontally
          removed_node_doc
      else
        let* new_doc =
          insert_node replacement_shifted ~shift_method:ShiftVertically
            removed_node_doc
        in

        let before_replacement, after_replacement =
          (split_at_id replacement_shifted.id) new_doc
        in
        let new_node_after_opt = List.nth_opt after_replacement 0 in
        if
          not
            (Option.equal
               (fun x y -> x.id = y.id)
               node_after_opt new_node_after_opt)
        then
          Error.string_to_or_error
            "This should not happen, please report this bug if you see it"
        else
          let dist =
            match (node_after_opt, new_node_after_opt) with
            | Some before, Some after ->
                let dist_before =
                  before.range.start.line - target.range.end_.line
                in
                let dist_after =
                  after.range.start.line - replacement_shifted.range.end_.line
                in
                dist_before - dist_after
            | _ -> 0
          in
          Ok
            {
              new_doc with
              elements =
                before_replacement
                @ replacement_shifted
                  :: List.map (shift_node dist 0) after_replacement;
            }
  | None ->
      Error.string_to_or_error
        ("The target node with id : " ^ Uuidm.to_string target_id
       ^ " doesn't exists")

let replace_proof (target_id : Uuidm.t) (new_proof : Proof.t) (doc : t) :
    transformation_step list option =
  match proof_with_id_opt target_id doc with
  | Some target ->
      let replacement_node =
        Replace (target.proposition.id, new_proof.proposition)
      in
      let remove_nodes =
        List.map (fun node -> Remove node.id) target.proof_steps
      in

      let attached_nodes =
        List.mapi
          (fun i node ->
            if i = 0 then Attach (node, LineAfter, new_proof.proposition.id)
            else
              let prev_node = List.nth new_proof.proof_steps (i - 1) in
              Attach (node, LineAfter, prev_node.id))
          new_proof.proof_steps
      in
      Some (remove_nodes @ (replacement_node :: attached_nodes))
  | None -> None

let apply_transformation_step (step : transformation_step) (doc : t) :
    (t, Error.t) result =
  match step with
  | Remove id -> remove_node_with_id id doc
  | Replace (id, new_node) -> replace_node id new_node doc
  | Add new_node -> insert_node new_node doc
  | Attach (attached_node, attach_position, anchor_id) -> (
      match element_with_id_opt anchor_id doc with
      | None ->
          Error.format_to_or_error
            "Can't find the node with id: %s to attach to"
            (Uuidm.to_string anchor_id)
      | Some target -> (
          let attached_node_start_point =
            match attach_position with
            | LineBefore -> target.range.start
            (* we don't shift back as by default, equal elements are pushed after *)
            | LineAfter -> shift_point 1 0 target.range.end_
            | SameLine -> shift_point 0 1 target.range.end_
          in

          let new_node_range =
            Code_range.range_from_starting_point_and_repr
              attached_node_start_point (repr attached_node)
          in
          let new_node_range : Code_range.t =
            match attach_position with
            | SameLine -> new_node_range
            | LineAfter | LineBefore ->
                {
                  start =
                    shift_point 0
                      (-new_node_range.start.character)
                      new_node_range.start;
                  end_ = shift_point 0 0 new_node_range.end_;
                }
          in

          let new_node =
            match attached_node.ast with
            | Some _ ->
                let node =
                  Syntax_node.syntax_node_of_string (repr attached_node)
                    new_node_range.start
                  |> Result.get_ok
                in
                { node with id = attached_node.id }
            | None ->
                let node =
                  Syntax_node.comment_syntax_node_of_string (repr attached_node)
                    new_node_range.start
                  |> Result.get_ok
                in
                { node with id = attached_node.id }
          in

          match attach_position with
          | SameLine -> insert_node ~shift_method:ShiftHorizontally new_node doc
          | LineAfter | LineBefore ->
              insert_node ~shift_method:ShiftVertically new_node doc))

let apply_transformations_steps (steps : transformation_step list) (doc : t) :
    (t, Error.t) result =
  List.fold_left
    (fun doc_acc_err step ->
      match doc_acc_err with
      | Ok doc -> apply_transformation_step step doc
      | Error err -> Error err)
    (Ok doc) steps
