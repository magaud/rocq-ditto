open Fleche
open Ditto
open Ditto.Nary_tree
open Ditto.Proof
open Ditto.Syntax_node

let normalize_strings (strings : string list) : string list =
  List.map (fun str -> String.trim str) strings

let sexp_of_syntax_node (x : Syntax_node.t) : Sexplib.Sexp.t =
  let open Sexplib in
  Sexp.(Atom (repr x))

let sexp_of_proof_tree (x : Syntax_node.t nary_tree) =
  Nary_tree.sexp_of_nary_tree sexp_of_syntax_node x

let rec simplify sexp =
  let open Sexplib.Sexp in
  match sexp with
  | List [ x ] -> simplify x
  | List xs -> List (List.map simplify xs)
  | Atom _ as a -> a

let print_tree ?(prefix = "") sexp =
  let open Sexplib.Sexp in
  let rec aux prefix sexp =
    match sexp with
    | Atom s -> Printf.printf "%s%s\n" prefix s
    | List lst ->
        let len = List.length lst in
        List.iteri
          (fun i x ->
            let is_last = i = len - 1 in
            let branch = if is_last then "└── " else "├── " in
            let next_prefix =
              if is_last then prefix ^ "    " else prefix ^ "│   "
            in
            match x with
            | Atom s -> Printf.printf "%s%s%s\n" prefix branch s
            | List _ ->
                Printf.printf "%s%s()\n" prefix branch;
                aux next_prefix x)
          lst
  in
  aux prefix (simplify sexp)

let testable_nary_tree (pp_a : Format.formatter -> 'a -> unit)
    (equal_a : 'a -> 'a -> bool) =
  Alcotest.testable (pp_nary_tree pp_a) (equal_nary_tree equal_a)

let document_to_range_representation_pairs (doc : Rocq_document.t) :
    (string * Code_range.t) list =
  List.map (fun node -> (Syntax_node.repr node, node.range)) doc.elements

let parse_json_target (json : Yojson.Safe.t) : (string * Code_range.t) list =
  let open Yojson.Safe.Util in
  json |> to_list
  |> List.map (fun elem ->
      let range = Code_range.of_yojson (member "range" elem) |> Result.get_ok in
      let repr = to_string (member "repr" elem) in
      (repr, range))

let get_target (uri_str : string) =
  let uri_str_without_ext = Filename.remove_extension uri_str in
  let target = uri_str_without_ext ^ "_target.v.target.json" in
  let target_doc = Yojson.Safe.from_file target in
  parse_json_target target_doc

let pp_int (fmt : Format.formatter) (x : int) = Format.fprintf fmt "%d" x
let int_tree = testable_nary_tree pp_int ( = )
let proof_status_testable = Alcotest.testable Proof.pp_proof_status ( = )
let range_testable = Alcotest.testable Code_range.pp ( = )
let uuidm_testable = Alcotest.testable Uuidm.pp ( = )
let error_testable = Alcotest.testable Error.pp ( = )
let goal_select_view_testable = Alcotest.testable Goal_select_view.pp ( = )
let sexp_testable = Alcotest.testable Sexplib.Sexp.pp_hum Sexplib.Sexp.equal
let reified_goal_testable = Alcotest.testable Reified_goal.pp ( = )

let vernacexpr_testable =
  Alcotest.testable
    (fun (fmt : Format.formatter) (x : Vernacexpr.vernac_expr) ->
      let repr = Ppvernac.pr_vernac_expr x in
      Pp.pp_with fmt repr)
    ( = )

let vernac_control_gen_r_testable =
  Alcotest.testable
    (fun (fmt : Format.formatter)
         (x :
           ( Vernacexpr.control_flag,
             Vernacexpr.synterp_vernac_expr )
           Vernacexpr.vernac_control_gen_r) ->
      let x_wrapped = CAst.make x in
      let x = Ppvernac.pr_vernac x_wrapped in
      Pp.pp_with fmt x)
    ( = )

let synterp_vernac_expr_testable =
  Alcotest.testable
    (fun (fmt : Format.formatter) (x : Vernacexpr.synterp_vernac_expr) ->
      let s = Serlib.Ser_vernacexpr.sexp_of_synterp_vernac_expr x in
      Sexplib.Sexp.pp_mach fmt s)
    ( = )

let make_dummy_node (start_line : int) (start_char : int) (end_line : int)
    (end_char : int) : Syntax_node.t =
  {
    ast = None;
    repr = lazy "dummy";
    id = Unique_id.uuid ();
    proof_id = None;
    diagnostics = [];
    range =
      {
        start = { line = start_line; character = start_char };
        end_ = { line = end_line; character = end_char };
      };
  }

let make_dummy_node_from_repr (start_line : int) (start_char : int)
    (repr : string) : Syntax_node.t =
  let start_point : Code_point.t =
    { line = start_line; character = start_char }
  in
  let range = Code_range.range_from_starting_point_and_repr start_point repr in
  {
    ast = None;
    repr = lazy repr;
    id = Unique_id.uuid ();
    proof_id = None;
    diagnostics = [];
    range;
  }

let check_list_sorted ~(cmp : 'a -> 'a -> int) ~(pp : 'a Fmt.t) (lst : 'a list)
    =
  let rec find_failure idx = function
    | [] | [ _ ] -> None
    | x :: y :: rest ->
        if cmp x y <= 0 then find_failure (idx + 1) (y :: rest)
        else Some (idx, x, y)
  in
  match find_failure 0 lst with
  | None -> ()
  | Some (idx, x, y) ->
      let pp_list = Fmt.Dump.list pp in
      let list_str = Format.asprintf "@[<v>Full list:@ %a@]" pp_list lst in
      Alcotest.failf "List is not sorted at index %d: %a > %a\n%s" idx pp x pp y
        list_str

let create_fixed_test (test_text : string) (f : Doc.t -> unit -> unit)
    (doc : Doc.t) =
  Alcotest.test_case test_text `Quick (f doc)

let test_parsing_ex1 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let nodes_repr = List.map (fun elem -> Syntax_node.repr elem) doc.elements in
  Alcotest.(check int)
    "More than one element was parsed." 1 (List.length nodes_repr);
  Alcotest.(check (list string))
    "parsed element don't match" [ "Compute 1 + 1." ] nodes_repr

let test_parsing_ex2 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let nodes_repr = List.map (fun elem -> Syntax_node.repr elem) doc.elements in
  Alcotest.(check int)
    "The wrong number of elements was parsed" 7 (List.length nodes_repr);
  Alcotest.(check (list string))
    "parsed element don't match"
    [
      "Theorem modus_ponens:\n  forall A B: Prop, A /\\ (A -> B) -> B.";
      "Proof.";
      "intros.";
      "destruct H as [H1 H2].";
      "apply H2.";
      "assumption.";
      "Qed.";
    ]
    nodes_repr

let test_proof_parsing_ex2 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.(check proof_status_testable)
    "The proof should be proved." Proof.Proved proof.status

let test_parsing_admit (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be admitted."
    Proof.Admitted proof.status

let test_parsing_defined (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved."
    Proof.Proved proof.status

let test_parsing_function (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in

  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved."
    Proof.Proved proof.status

let test_parsing_abort1 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be aborted."
    Proof.Aborted proof.status

let test_parsing_abort2 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 2 (List.length proofs);
  let first_proof = List.hd proofs in
  let second_proof = List.nth proofs 1 in
  Alcotest.check proof_status_testable "The first proof should be aborted"
    Proof.Aborted first_proof.status;
  Alcotest.check proof_status_testable "The second proof is proved" Proof.Proved
    second_proof.status

let test_proof_parsing_name_and_steps_ex2 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let proof = List.hd (Result.get_ok (Rocq_document.get_proofs doc)) in
  Alcotest.(check string)
    "The proof name should be modus ponens" "modus_ponens"
    (Option.default "got none" (Proof.get_proof_name proof));
  Alcotest.(check int)
    "The proof should have 6 steps (including Proof. and Qed.)" 6
    (List.length proof.proof_steps);
  Alcotest.(check string)
    "The proof expression is wrong."
    "Theorem modus_ponens:\n  forall A B: Prop, A /\\ (A -> B) -> B."
    (repr proof.proposition);
  let proof_steps_normalized =
    normalize_strings (List.map (fun s -> repr s) proof.proof_steps)
  in
  Alcotest.(check (list string))
    "The proof should have the following steps."
    [
      "Proof.";
      "intros.";
      "destruct H as [H1 H2].";
      "apply H2.";
      "assumption.";
      "Qed.";
    ]
    proof_steps_normalized

let test_proof_parsing_multiple_proofs_ex3 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed" 2 (List.length proofs);
  let proof_names = List.filter_map (fun p -> Proof.get_proof_name p) proofs in
  Alcotest.(check (list string))
    "One or more proof does't have the correct name"
    [ "and_split"; "and_split_bis" ]
    proof_names;
  ()

let test_parsing_comment_ex4 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  Alcotest.(check int)
    "The wrong number of nodes was parsed" 1 (List.length doc.elements);
  let node = List.hd doc.elements in
  Alcotest.(check string)
    "Comment was badly parsed" "(* single comment *)" (repr node);
  Alcotest.(check bool)
    "Comment node should not have an AST" true (Option.is_empty node.ast)

let test_parsing_multiples_comments_ex5 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 5
    (List.length comment_nodes);
  Alcotest.(check int)
    "The wrong number of total nodes was parsed" 12 (List.length doc.elements)

let test_parsing_embedded_comments_ex6 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  let comment_nodes_repr = List.map (fun node -> repr node) comment_nodes in
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 2
    (List.length comment_nodes);
  Alcotest.(check (list string))
    "Comments badly parsed"
    [ "(* in the same line comment *)"; "(* classical comment *)" ]
    comment_nodes_repr

let test_parsing_weird_comments_ex7 (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  let comment_nodes_repr = List.map (fun node -> repr node) comment_nodes in

  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 2
    (List.length comment_nodes);
  Alcotest.(check (list string))
    "Comments badly parsed"
    [ "(*in the same line comment*)"; "(**weird comment*)" ]
    comment_nodes_repr

let test_parsing_in_then_star_then_parenthesis (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  let other_nodes =
    List.filter (fun node -> Option.has_some node.ast) doc.elements
  in

  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 0
    (List.length comment_nodes);
  Alcotest.(check int)
    "The wrong number of other nodes was parsed" 8 (List.length other_nodes)

let test_parsing_instance (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in

  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let first_proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved" Proof.Proved
    first_proof.status

let test_parsing_unicode (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let first_proof = List.hd proofs in

  let proof_prop = first_proof.proposition in
  Alcotest.check proof_status_testable "The proof should be proved" Proof.Proved
    first_proof.status;

  Alcotest.(check string)
    "The proof prop should be the following: "
    "Lemma demo : forall P Q: Prop, P ∧ Q → Q ∧ P." (repr proof_prop)

let test_reconstructing_stuck_together (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let reconstructed = Rocq_document.dump_to_string doc in
  Alcotest.(check (result string error_testable))
    "The document should be correctly reconstructed"
    (Ok "Lemma a: True /\\ True.\nProof.\nsplit.\n-auto.\n-auto.") reconstructed

let test_creating_valid_syntax_node_from_string (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node = Syntax_node.syntax_node_of_string "Compute 1 + 1." point in
  let node_repr = Result.map Syntax_node.repr node in

  Alcotest.(
    check
      (result string error_testable)
      "The node should be created without error" (Ok "Compute 1 + 1.") node_repr)

let test_creating_invalid_syntax_node_from_string (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node =
    Syntax_node.syntax_node_of_string "Compute Illegal grammar" point
  in
  let node_repr = Result.map Syntax_node.repr node in

  Alcotest.(
    check
      (result string error_testable)
      "The node creation should return an error"
      (Error
         (Error.of_string "'.' expected after [lconstr] (in [query_command])"))
      node_repr)

let test_creating_simple_a_then_b (_ : Doc.t) () : unit =
  let code_point_a : Code_point.t = { line = 0; character = 0 } in
  let code_point_b : Code_point.t = { line = 1; character = 0 } in
  let a =
    Syntax_node.syntax_node_of_string "idtac." code_point_a |> Result.get_ok
  in
  let b =
    Syntax_node.syntax_node_of_string "idtac." code_point_b |> Result.get_ok
  in
  let a_then_b = Syntax_node.apply_tac_then a b () in
  let a_then_b_repr = Result.map Syntax_node.repr a_then_b in

  Alcotest.(
    check
      (result string error_testable)
      "a then b should be constructed correctly" (Ok "idtac; idtac.")
      a_then_b_repr)

let test_creating_a_then_b_assert_by (_ : Doc.t) () : unit =
  let code_point_a : Code_point.t = { line = 0; character = 0 } in
  let code_point_b : Code_point.t = { line = 1; character = 0 } in
  let a =
    Syntax_node.syntax_node_of_string
      "assert (forall A : Prop, (A -> A) /\\ (A -> A)) by (split;auto)."
      code_point_a
    |> Result.get_ok
  in
  let b =
    Syntax_node.syntax_node_of_string "reflexivity." code_point_b
    |> Result.get_ok
  in

  let a_then_b = Syntax_node.apply_tac_then a b () in
  let a_then_b_repr = Result.map Syntax_node.repr a_then_b in

  Alcotest.(
    check
      (result string error_testable)
      "a then b should be constructed correctly"
      (Ok
         "assert (forall A : Prop, (A -> A) /\\ (A -> A)) by (split; auto); \
          reflexivity.")
      a_then_b_repr)

let test_creating_simple_a_thens_b (_ : Doc.t) () : unit =
  let code_point_a : Code_point.t = { line = 0; character = 0 } in
  let code_point_b : Code_point.t = { line = 1; character = 0 } in
  let a =
    Syntax_node.syntax_node_of_string "reflexivity." code_point_a
    |> Result.get_ok
  in
  let b =
    Syntax_node.syntax_node_of_string "reflexivity." code_point_b
    |> Result.get_ok
  in
  let a_thens_b = Syntax_node.apply_tac_thens a [ b ] () in
  let a_thens_b_repr = Result.map Syntax_node.repr a_thens_b in

  Alcotest.(
    check
      (result string error_testable)
      "a then b should be constructed correctly"
      (Ok "reflexivity; [ reflexivity ].") a_thens_b_repr)

let test_creating_a_thens_nothing (_ : Doc.t) () : unit =
  let code_point_a : Code_point.t = { line = 0; character = 0 } in
  let a =
    Syntax_node.syntax_node_of_string "reflexivity." code_point_a
    |> Result.get_ok
  in
  let a_thens_nothing = Syntax_node.apply_tac_thens a [] () in
  let a_thens_nothing_repr = Result.map Syntax_node.repr a_thens_nothing in
  Alcotest.(
    check
      (result string error_testable)
      "a thens nothing should be constructed correctly"
      (Ok "reflexivity; [  ].") a_thens_nothing_repr)

let test_get_goal_select_all (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node =
    Syntax_node.syntax_node_of_string "all:simpl." point |> Result.get_ok
  in

  let goal_selector = Syntax_node.get_node_goal_selector_opt node in

  let expected : Goal_select_view.t option = Some Goal_select_view.SelectAll in

  Alcotest.(check (option goal_select_view_testable))
    "The correct goal selector should be retrieved (SelectAll)" expected
    goal_selector

let test_goal_select_nth_selector (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node =
    Syntax_node.syntax_node_of_string "1:simpl." point |> Result.get_ok
  in

  let goal_selector = Syntax_node.get_node_goal_selector_opt node in

  let expected : Goal_select_view.t option =
    Some (Goal_select_view.SelectList [ Goal_select_view.NthSelector 1 ])
  in

  Alcotest.(check (option goal_select_view_testable))
    "The correct goal selector should be retrieved SelectList (SelectNth 1)"
    expected goal_selector

let test_goal_select_single_range (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in

  let node =
    Syntax_node.syntax_node_of_string "1-2:simpl." point |> Result.get_ok
  in

  let goal_selector = Syntax_node.get_node_goal_selector_opt node in

  let expected : Goal_select_view.t option =
    Some (Goal_select_view.SelectList [ Goal_select_view.RangeSelector (1, 2) ])
  in

  Alcotest.(check (option goal_select_view_testable))
    "The correct goal selector should be retrieved SelectList (RangeSelector \
     (1,2))"
    expected goal_selector

let test_goal_select_multiple_selector (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node =
    Syntax_node.syntax_node_of_string "1-2,3-4:simpl." point |> Result.get_ok
  in

  let goal_selector = Syntax_node.get_node_goal_selector_opt node in

  let expected : Goal_select_view.t option =
    Some
      (Goal_select_view.SelectList
         [
           Goal_select_view.RangeSelector (1, 2);
           Goal_select_view.RangeSelector (3, 4);
         ])
  in

  Alcotest.(check (option goal_select_view_testable))
    "The correct goal selector should be retrieved SelectList (RangeSelector \
     (1,2); (RangeSelector (3,4)))"
    expected goal_selector

let test_drop_goal_selector_nth (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node =
    Syntax_node.syntax_node_of_string "1:simpl." point |> Result.get_ok
  in

  let node_without_selector = Syntax_node.drop_goal_selector node in

  let has_goal_selector =
    Syntax_node.get_node_goal_selector_opt node_without_selector
    |> Option.is_empty
  in

  Alcotest.(
    check bool "The node selector should be None" true has_goal_selector)

let test_creating_select_already_focused (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node =
    Syntax_node.syntax_node_of_string "reflexivity." point |> Result.get_ok
  in

  let node_with_select_already_focused_repr =
    Syntax_node.add_goal_selector node Goal_select_view.SelectAlreadyFocused
    |> Result.map Syntax_node.repr
  in

  Alcotest.(
    check
      (result string error_testable)
      "the node with the selector: select_already_focused should be created \
       correctly"
      (Ok "!: reflexivity.") node_with_select_already_focused_repr)

let test_selecting_first_goal_with_goal_select (doc : Doc.t) () : unit =
  let token = Coq.Limits.Token.create () in
  let parsed_document = Rocq_document.parse_document doc in
  let third_node = List.nth parsed_document.elements 2 in

  let state =
    Runner.get_init_state parsed_document third_node token |> Result.get_ok
  in
  let goals_at_state = Runner.reified_goals_at_state token state in
  let goal_selector : Goal_select_view.t =
    Goal_select_view.SelectList [ Goal_select_view.NthSelector 1 ]
  in

  let selected_goals =
    Goal_select_view.apply_goal_selector_view goal_selector goals_at_state
  in
  let selected_goals_len = Result.map List.length selected_goals in
  let selected_goal_hd = Result.map List.hd selected_goals in

  let expected_goal = List.nth goals_at_state 0 in
  Alcotest.(
    check
      (result int error_testable)
      "Only one goal should have been selected." (Ok 1) selected_goals_len);

  Alcotest.(
    check
      (result reified_goal_testable error_testable)
      "The correct goal should be selected" (Ok expected_goal) selected_goal_hd)

let test_detecting_proof_with (_ : Doc.t) () : unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node =
    Syntax_node.syntax_node_of_string "Proof with easy." point |> Result.get_ok
  in

  let is_node_proof_with = Syntax_node.is_syntax_node_proof_with node in
  Alcotest.(
    check bool "The node should be detected as a \"Proof with\"" true
      is_node_proof_with)

let test_not_detecting_simple_proof_command_with_proof_with (_ : Doc.t) () :
    unit =
  let point : Code_point.t = { line = 0; character = 0 } in
  let node =
    Syntax_node.syntax_node_of_string "Proof." point |> Result.get_ok
  in

  let is_node_proof_with = Syntax_node.is_syntax_node_proof_with node in
  Alcotest.(
    check bool "The node should not have been detected as a \"Proof with\""
      false is_node_proof_with)

let test_searching_node (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let first_node_id = (List.hd doc.elements).id in
  let node_compute = Rocq_document.element_with_id_opt first_node_id doc in
  let node_compute_id = Option.map (fun node -> node.id) node_compute in
  Alcotest.(check (option uuidm_testable))
    "Item with the wrong id was retrieved" (Some first_node_id) node_compute_id;
  Alcotest.(check (option string))
    "The wrong repr was retrieved" (Some "Compute 1.")
    (Option.map Syntax_node.repr node_compute);
  let absurd_node = Rocq_document.element_with_id_opt (Unique_id.uuid ()) doc in
  Alcotest.(check (option uuidm_testable))
    "No element should be retrieved" None
    (Option.map (fun x -> x.id) absurd_node)

let test_reformat_comment_node (_ : Doc.t) () : unit =
  let starting_point : Code_point.t = { line = 0; character = 0 } in

  let comment_node =
    comment_syntax_node_of_string "(* a comment *)" starting_point
    |> Result.get_ok
  in

  let reformatted_node = Syntax_node.reformat_node comment_node in
  let reformat_id = Result.map (fun x -> x.id) reformatted_node in

  Alcotest.(check (result uuidm_testable error_testable))
    "Should return an error"
    (Error.string_to_or_error "The node need to have an AST to be reformatted")
    reformat_id

let test_reformat_keep_id (_ : Doc.t) () : unit =
  let starting_point : Code_point.t = { line = 0; character = 0 } in

  let content_node =
    syntax_node_of_string "Compute 1 + 1." starting_point |> Result.get_ok
  in

  let reformatted_node = Syntax_node.reformat_node content_node in
  let reformat_id = Result.map (fun x -> x.id) reformatted_node in

  Alcotest.(check (result uuidm_testable error_testable))
    "Should return the same id" (Ok content_node.id) reformat_id

let test_id_assign_document (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let nodes_ids = List.map (fun x -> x.id) doc.elements in
  check_list_sorted ~cmp:Uuidm.compare ~pp:Uuidm.pp nodes_ids

let test_sorting_nodes (_ : Doc.t) () : unit =
  let node1 = make_dummy_node 0 0 0 12 in
  (* your example *)
  let node2 = make_dummy_node 0 14 1 2 in
  (* overlaps with node1 *)
  let node3 = make_dummy_node 2 0 2 10 in
  (* does not overlap *)

  let sorted = List.sort Syntax_node.compare_nodes [ node2; node3; node1 ] in
  let ids = List.map (fun n -> n.id) sorted in

  (* node1 and node2 overlap; smallest common = 18 *)
  (* node1 starts at 16 < 18 => node1 before node2 *)
  (* node3 is later and doesn't overlap *)
  let expected = [ node1.id; node2.id; node3.id ] in

  Alcotest.(check (list uuidm_testable))
    "The nodes should be ordered correctly" expected ids

let test_colliding_nodes_no_common_lines (_ : Doc.t) () : unit =
  let target_node = make_dummy_node 0 0 0 12 in
  let other_node = make_dummy_node 1 0 1 10 in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_common_line_no_collision (_ : Doc.t) () : unit =
  let target_node = make_dummy_node_from_repr 0 0 "hello" in
  let other_node = make_dummy_node_from_repr 0 20 "world" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_common_line_collision (_ : Doc.t) () : unit =
  let target_node = make_dummy_node_from_repr 0 0 "hello" in
  let other_node = make_dummy_node_from_repr 0 3 "world" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should be colliding" [ other_node.id ] colliding_nodes_ids

let test_colliding_nodes_one_common_line_no_collision (_ : Doc.t) () : unit =
  let target_node = make_dummy_node 0 0 1 10 in
  let other_node = make_dummy_node 1 12 1 20 in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_multiple_common_lines_collision (_ : Doc.t) () : unit =
  let target_node = make_dummy_node 0 0 2 20 in
  let other_node = make_dummy_node 1 12 2 25 in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should be colliding" [ other_node.id ] colliding_nodes_ids

let test_removing_and_leaving_blank (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in

  let second_node = List.nth doc.elements 3 in
  let parsed_target = get_target uri_str in

  let new_doc =
    Result.get_ok
      (Rocq_document.remove_node_with_id ~remove_method:LeaveBlank
         second_node.id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_and_leaving_blank_multiple_line_nodes (doc : Doc.t) () : unit
    =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in

  let second_node = List.nth doc.elements 1 in
  let parsed_target = get_target uri_str in

  let new_doc =
    Result.get_ok
      (Rocq_document.remove_node_with_id ~remove_method:LeaveBlank
         second_node.id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_and_leaving_blank_middle_of_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in

  let fourth_node = List.nth doc.elements 4 in
  let parsed_target = get_target uri_str in

  let new_doc =
    Result.get_ok
      (Rocq_document.remove_node_with_id ~remove_method:LeaveBlank
         fourth_node.id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_only_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in

  let parsed_target = get_target uri_str in

  let first_node_id = (List.hd doc.elements).id in

  let new_doc =
    Result.get_ok (Rocq_document.remove_node_with_id first_node_id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_multiple_line_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in

  let second_node = List.nth doc.elements 1 in
  let parsed_target = get_target uri_str in

  let new_doc =
    Result.get_ok (Rocq_document.remove_node_with_id second_node.id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_node_middle_of_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let second_node = List.nth doc.elements 1 in
  let new_doc =
    Result.get_ok (Rocq_document.remove_node_with_id second_node.id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in
  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_node_with_one_node_left_same_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let removed_node = List.nth doc.elements 4 in
  let new_doc =
    Result.get_ok (Rocq_document.remove_node_with_id removed_node.id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in
  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_adding_node_on_empty_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 1; character = 0 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." start_point)
  in
  let new_doc = Rocq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_node_before_busy_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 1; character = 0 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." start_point)
  in

  let new_doc = Rocq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_multiple_line_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 2; character = 0 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 1\n        +\n        1."
         start_point)
  in

  let new_doc = Rocq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_node_between (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 1; character = 11 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." start_point)
  in

  let new_doc =
    Rocq_document.insert_node ~shift_method:ShiftHorizontally node doc
  in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_collision_next_line (doc : Doc.t) () : unit =
  (* TODO bugged for now, fix later *)
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 2; character = 0 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 1\n+\n1." start_point)
  in

  let new_doc = Rocq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_node_colliding_many (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 6; character = 2 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 1 +\n  2 + 3 + 4\n  + 5 + 6."
         start_point)
  in

  let new_doc = Rocq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_single_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 2; character = 0 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 42." start_point)
  in

  let second_node_id = (List.nth doc.elements 1).id in

  let new_doc = Rocq_document.replace_node second_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_first_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 2; character = 0 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 123." start_point)
  in

  let second_node_id = (List.nth doc.elements 1).id in

  let new_doc = Rocq_document.replace_node second_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_node_in_middle_of_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 2; character = 11 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 123456." start_point)
  in

  let third_node_id = (List.nth doc.elements 2).id in

  let new_doc = Rocq_document.replace_node third_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_node_end_of_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 2; character = 22 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 12345." start_point)
  in

  let fourth_node_id = (List.nth doc.elements 3).id in

  let new_doc = Rocq_document.replace_node fourth_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_smaller_node_with_bigger_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 1; character = 0 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string
         "Theorem th : forall n : nat,\nn + 0 = n." start_point)
  in

  let first_node_id = (List.hd doc.elements).id in

  let new_doc = Rocq_document.replace_node first_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_bigger_node_with_smaller_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 1; character = 0 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string
         "Theorem th : forall n : nat, n + 0 = n." start_point)
  in

  let first_node_id = (List.hd doc.elements).id in

  let new_doc = Rocq_document.replace_node first_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in
  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_block_by_other_block (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Code_point.t = { line = 16; character = 0 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string
         "Lemma l4_19_stdlib :\n\
         \  forall A B C C' : Point,\n\
         \  Bet A C B -> Cong A C A C' -> Cong B C B C' ->\n\
         \  C = C'."
         start_point)
  in

  let first_proof = Rocq_document.get_proofs doc |> Result.get_ok |> List.hd in
  let thm_id = first_proof.proposition.id in

  let new_doc = Rocq_document.replace_node thm_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_tree_transformation (doc : Doc.t)
    (tree_transformation :
      Rocq_document.t ->
      t nary_tree ->
      (transformation_step list, Error.t) result) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in

  let parsed_target = get_target uri_str in

  let new_doc =
    Transformations.apply_proof_tree_transformation tree_transformation doc
  in

  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in
  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_proof_transformation (doc : Doc.t)
    (proof_transformation :
      Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result)
    () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Rocq_document.parse_document doc in

  let parsed_target = get_target uri_str in

  let new_doc =
    Transformations.apply_proof_transformation proof_transformation doc
  in

  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in
  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_simple_auto_by_steps (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.replace_auto_with_steps ()

let test_replace_multiple_branch_auto_by_steps (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.replace_auto_with_steps ()

let test_replace_auto_using_zarith_by_steps (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.replace_auto_with_steps ()

let test_replace_auto_with_backtracking (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.replace_auto_with_steps ()

let test_turn_into_oneliner_with_commands (doc : Doc.t) () : unit =
  test_tree_transformation doc Transformations.turn_into_oneliner ()

let test_turn_into_onliner_with_curly_braces (doc : Doc.t) () : unit =
  test_tree_transformation doc Transformations.turn_into_oneliner ()

let test_turn_into_oneliner_admitted (doc : Doc.t) () : unit =
  test_tree_transformation doc Transformations.turn_into_oneliner ()

let test_turn_into_oneliner_proof_with (doc : Doc.t) () : unit =
  test_tree_transformation doc Transformations.turn_into_oneliner ()

let test_turn_into_onliner_goal_select (doc : Doc.t) () : unit =
  test_tree_transformation doc Transformations.turn_into_oneliner ()

let test_turn_into_onliner_match (doc : Doc.t) () : unit =
  test_tree_transformation doc Transformations.turn_into_oneliner ()

let explicit_fresh_variables_simple_intros (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.explicit_fresh_variables ()

let explicit_fresh_variables_simple_assert (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.explicit_fresh_variables ()

let explicit_fresh_variables_simple_induction (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.explicit_fresh_variables ()

let explicit_fresh_variables_list_induction (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.explicit_fresh_variables ()

let explicit_fresh_variables_two_induction_hypotheses (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.explicit_fresh_variables ()

let test_flattening_goal_select_simple (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.flatten_goal_selectors ()

let test_flattening_goal_select_range (doc : Doc.t) () : unit =
  test_proof_transformation doc Transformations.flatten_goal_selectors ()

let test_count_goals_simple_proof_without_focus (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let token = Coq.Limits.Token.create () in

  let steps_with_goalcount =
    Runner.proof_steps_with_goalcount token doc.initial_state doc.elements
  in
  let repr_with_goalcount =
    List.map
      (fun (_, step, goal_count) -> (repr step, goal_count))
      steps_with_goalcount
  in

  let expected =
    [
      ("Theorem th: forall n : nat, n + 0 = n.", 1);
      ("Proof.", 1);
      ("intros.", 1);
      ("induction n.", 2);
      ("reflexivity.", 1);
      ("simpl.", 1);
      ("rewrite IHn.", 1);
      ("reflexivity.", 0);
      ("Qed.", 0);
    ]
  in

  Alcotest.(
    check
      (list (pair string int))
      "The two lists should be the same" expected repr_with_goalcount)

let test_count_goals_proof_with_bullets_without_focus (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let token = Coq.Limits.Token.create () in

  let steps_with_goalcount =
    Runner.proof_steps_with_goalcount token doc.initial_state doc.elements
  in
  let repr_with_goalcount =
    List.map
      (fun (_, step, goal_count) -> (repr step, goal_count))
      steps_with_goalcount
  in

  let expected =
    [
      ("Theorem th: forall n : nat, n * 1 = n.", 1);
      ("Proof.", 1);
      ("intros.", 1);
      ("induction n.", 2);
      ("-", 2);
      ("reflexivity.", 1);
      ("-", 1);
      ("simpl.", 1);
      ("rewrite IHn.", 1);
      ("reflexivity.", 0);
      ("Qed.", 0);
    ]
  in

  Alcotest.(
    check
      (list (pair string int))
      "The two lists should be the same" expected repr_with_goalcount)

let test_count_goals_proof_with_brackets_without_focus (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in
  let token = Coq.Limits.Token.create () in
  let first_proof = Rocq_document.get_proofs doc |> Result.get_ok |> List.hd in

  let state =
    Runner.get_init_state doc first_proof.proposition token |> Result.get_ok
  in

  let steps_with_goalcount =
    Runner.proof_steps_with_goalcount token state
      (Proof.proof_nodes first_proof)
  in
  let repr_with_goalcount =
    List.map
      (fun (_, step, goal_count) -> (repr step, goal_count))
      steps_with_goalcount
  in

  let expected =
    [
      ("Theorem fact_pos : forall n : nat, n! > 0.", 1);
      ("Proof.", 1);
      ("induction n.", 2);
      ("{", 2);
      ("simpl.", 2);
      ("lia.", 1);
      ("}", 1);
      ("{", 1);
      ("simpl.", 1);
      ("lia.", 0);
      ("}", 0);
      ("Qed.", 0);
    ]
  in

  Alcotest.(
    check
      (list (pair string int))
      "The two lists should be the same" expected repr_with_goalcount)

let test_count_goals_proof_with_nested_bullets_without_focus (doc : Doc.t) () :
    unit =
  let doc = Rocq_document.parse_document doc in
  let token = Coq.Limits.Token.create () in
  let first_proof = Rocq_document.get_proofs doc |> Result.get_ok |> List.hd in

  let state =
    Runner.get_init_state doc first_proof.proposition token |> Result.get_ok
  in

  let steps_with_goalcount =
    Runner.proof_steps_with_goalcount token state
      (Proof.proof_nodes first_proof)
  in
  let repr_with_goalcount =
    List.map
      (fun (_, step, goal_count) -> (repr step, goal_count))
      steps_with_goalcount
  in
  let expected =
    [
      ("Goal (1=1 /\\ 2=2) /\\ 3=3.", 1);
      ("Proof.", 1);
      ("split.", 2);
      ("-", 2);
      ("split.", 3);
      ("+", 3);
      ("trivial.", 2);
      ("+", 2);
      ("trivial.", 1);
      ("-", 1);
      ("trivial.", 0);
      ("Qed.", 0);
    ]
  in

  Alcotest.(
    check
      (list (pair string int))
      "The two lists should be the same" expected repr_with_goalcount)

let test_count_goals_proof_with_brackets_bullets_without_focus (doc : Doc.t) ()
    : unit =
  let doc = Rocq_document.parse_document doc in
  let token = Coq.Limits.Token.create () in
  let first_proof = Rocq_document.get_proofs doc |> Result.get_ok |> List.hd in

  let state =
    Runner.get_init_state doc first_proof.proposition token |> Result.get_ok
  in

  let steps_with_goalcount =
    Runner.proof_steps_with_goalcount token state
      (Proof.proof_nodes first_proof)
  in
  let repr_with_goalcount =
    List.map
      (fun (_, step, goal_count) -> (repr step, goal_count))
      steps_with_goalcount
  in
  let expected =
    [
      ("Theorem fact_pos : forall n : nat, n! > 0.", 1);
      ("Proof.", 1);
      ("induction n.", 2);
      ("-", 2);
      ("{", 2);
      ("simpl.", 2);
      ("lia.", 1);
      ("}", 1);
      ("-", 1);
      ("{", 1);
      ("simpl.", 1);
      ("lia.", 0);
      ("}", 0);
      ("Qed.", 0);
    ]
  in

  Alcotest.(
    check
      (list (pair string int))
      "The two lists should be the same" expected repr_with_goalcount)

let test_parse_simple_proof_to_proof_tree (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in

  let first_proof = Rocq_document.get_proofs doc |> Result.get_ok |> List.hd in

  let proof_tree = Runner.treeify_proof doc first_proof in

  let proof_tree_sexp =
    Result.map (Nary_tree.sexp_of_nary_tree sexp_of_syntax_node) proof_tree
  in

  let expected_tree =
    [%sexp
      "Theorem th: forall n : nat, n + 0 = n.",
      [
        ( "Proof.",
          [
            ( "intros.",
              [
                ( "induction n.",
                  [
                    ("reflexivity.", []);
                    [
                      "simpl.";
                      [
                        ("rewrite IHn.", [ ("reflexivity.", [ ("Qed.", []) ]) ]);
                      ];
                    ];
                  ] );
              ] );
          ] );
      ]]
  in
  Alcotest.(
    check
      (result sexp_testable error_testable)
      "Tree should match the expected tree" (Ok expected_tree) proof_tree_sexp)

let test_parse_proof_with_bullets_to_proof_tree (doc : Doc.t) () : unit =
  let doc = Rocq_document.parse_document doc in

  let first_proof = Rocq_document.get_proofs doc |> Result.get_ok |> List.hd in

  let proof_tree = Runner.treeify_proof doc first_proof in

  let proof_tree_sexp =
    Result.map (Nary_tree.sexp_of_nary_tree sexp_of_syntax_node) proof_tree
  in

  let expected_tree =
    [%sexp
      "Theorem th: forall n : nat, n * 1 = n.",
      [
        ( "Proof.",
          [
            ( "intros.",
              [
                ( "induction n.",
                  [
                    ("-", [ ("reflexivity.", []) ]);
                    ( "-",
                      [
                        ( "simpl.",
                          [
                            ( "rewrite IHn.",
                              [ ("reflexivity.", [ ("Qed.", []) ]) ] );
                          ] );
                      ] );
                  ] );
              ] );
          ] );
      ]]
  in

  print_tree expected_tree;

  Alcotest.(
    check
      (result sexp_testable error_testable)
      "Tree should match the expected tree" (Ok expected_tree) proof_tree_sexp)

let setup_test_table table (doc : Doc.t) =
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if simply ordered nodes are sorted correctly"
       test_sorting_nodes doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "check if two nodes on different lines are not colliding"
       test_colliding_nodes_no_common_lines doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "check if two nodes on the same line are not colliding"
       test_colliding_nodes_common_line_no_collision doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "check if two nodes on the same line are colliding"
       test_colliding_nodes_common_line_collision doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test
       "check if two nodes with one common line are not colliding"
       test_colliding_nodes_one_common_line_no_collision doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test
       "check if two nodes with multiple common lines are colliding"
       test_colliding_nodes_multiple_common_lines_collision doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if reformat fail on comment"
       test_reformat_comment_node doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if reformat keep the same id"
       test_reformat_keep_id doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test creating a simple node without error"
       test_creating_valid_syntax_node_from_string doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test creating an invalid node"
       test_creating_invalid_syntax_node_from_string doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test creating a then b from AST (a;b)"
       test_creating_simple_a_then_b doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test creating a then b from ambiguous expression"
       test_creating_a_then_b_assert_by doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test creating a thens b from AST (a;[b])"
       test_creating_simple_a_thens_b doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test creating a thens nothing"
       test_creating_a_thens_nothing doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test getting a Goal_select_view.t from all:tactic"
       test_get_goal_select_all doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test getting a Goal_select_view from n:tactic"
       test_goal_select_nth_selector doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test getting a Goal_select_view from a,b:tactic"
       test_goal_select_single_range doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test getting a Goal_select_view from a-b,c-d:tactic"
       test_goal_select_multiple_selector doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test dropping a goal selector from a tactic"
       test_drop_goal_selector_nth doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test adding the goal selector: SelectAlreadyFocused"
       test_creating_select_already_focused doc);
  Hashtbl.add table "ex_goal_selecting_one.v"
    (create_fixed_test "test applying a Goal_select_view to a list of goals"
       test_selecting_first_goal_with_goal_select doc);

  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "test checking if detecting \"Proof with\" is correct"
       test_detecting_proof_with doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test
       "test checking if detecting Proof with doesnt detect normal Proof \
        commands"
       test_not_detecting_simple_proof_command_with_proof_with doc);

  Hashtbl.add table "ex_proof_tree1.v"
    (create_fixed_test "test counting the goals of each steps of a simple proof"
       test_count_goals_simple_proof_without_focus doc);
  Hashtbl.add table "ex_proof_tree2.v"
    (create_fixed_test
       "test counting the goals of each steps of a proof with bullets"
       test_count_goals_proof_with_bullets_without_focus doc);
  Hashtbl.add table "ex_proof_with_brackets.v"
    (create_fixed_test "test counting the goals of a proof with brackets"
       test_count_goals_proof_with_brackets_without_focus doc);
  Hashtbl.add table "ex_proof_brackets_bullets.v"
    (create_fixed_test
       "test counting the goals of a proof with brackets and bullets"
       test_count_goals_proof_with_brackets_bullets_without_focus doc);
  Hashtbl.add table "ex_proof_nested_bullets.v"
    (create_fixed_test "test counting the goals of a proof with nested bullets"
       test_count_goals_proof_with_nested_bullets_without_focus doc);
  Hashtbl.add table "ex_proof_tree1.v"
    (create_fixed_test "test creating a simple proof tree"
       test_parse_simple_proof_to_proof_tree doc);

  Hashtbl.add table "ex_proof_tree2.v"
    (create_fixed_test "test creating a proof tree with bullets"
       test_parse_proof_with_bullets_to_proof_tree doc);
  Hashtbl.add table "ex_parsing1.v"
    (create_fixed_test "test parsing ex 1" test_parsing_ex1 doc);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing ex 2" test_parsing_ex2 doc);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing basic proof properties ex 2"
       test_parsing_ex2 doc);
  Hashtbl.add table "ex_admit.v"
    (create_fixed_test "test parsing admitted proof" test_parsing_admit doc);
  Hashtbl.add table "ex_definition1.v"
    (create_fixed_test "test parsing defined proof" test_parsing_defined doc);
  Hashtbl.add table "ex_function1.v"
    (create_fixed_test "test parsing function proof" test_parsing_function doc);
  Hashtbl.add table "ex_abort1.v"
    (create_fixed_test "test parsing aborted proof 1" test_parsing_abort1 doc);
  Hashtbl.add table "ex_abort2.v"
    (create_fixed_test "test parsing aborted proof 2" test_parsing_abort2 doc);
  Hashtbl.add table "ex_instance1.v"
    (create_fixed_test "test parsing an instance proof" test_parsing_instance
       doc);
  Hashtbl.add table "ex_unicode.v"
    (create_fixed_test "test parsing a file containing Unicode"
       test_parsing_unicode doc);

  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test names and steps retrival ex 2"
       test_proof_parsing_name_and_steps_ex2 doc);
  Hashtbl.add table "ex_parsing3.v"
    (create_fixed_test "test parsing of two proofs ex3"
       test_proof_parsing_multiple_proofs_ex3 doc);
  Hashtbl.add table "ex_parsing4.v"
    (create_fixed_test "test parsing single comment" test_parsing_comment_ex4
       doc);
  Hashtbl.add table "ex_parsing5.v"
    (create_fixed_test "test parsing multiple complex comments"
       test_parsing_multiples_comments_ex5 doc);
  Hashtbl.add table "ex_parsing6.v"
    (create_fixed_test "test parsing embedded comments"
       test_parsing_embedded_comments_ex6 doc);
  Hashtbl.add table "ex_parsing7.v"
    (create_fixed_test "test parsing weird comments"
       test_parsing_weird_comments_ex7 doc);
  Hashtbl.add table "not_parsing_in_star_as_comment.v"
    (create_fixed_test "test not parsing star as a comment ) "
       test_parsing_in_then_star_then_parenthesis doc);

  Hashtbl.add table "ex_reconstructing_stuck_together.v"
    (create_fixed_test "test reconstructing nodes glued together"
       test_reconstructing_stuck_together doc);

  Hashtbl.add table "ex_id_assign1.v"
    (create_fixed_test "test the initial ordering of nodes in the document"
       test_id_assign_document doc);
  Hashtbl.add table "ex_id_assign2.v"
    (create_fixed_test "test the initial ordering of nodes in a simple proof"
       test_id_assign_document doc);
  Hashtbl.add table "ex_id_assign3.v"
    (create_fixed_test "test the initial ordering of nodes with comments"
       test_id_assign_document doc);

  Hashtbl.add table "ex_removing1.v"
    (create_fixed_test "test removing only node on a line"
       test_removing_only_node_on_line doc);
  Hashtbl.add table "ex_removing2.v"
    (create_fixed_test "test removing a node spanning multiple lines"
       test_removing_multiple_line_node doc);
  Hashtbl.add table "ex_removing3.v"
    (create_fixed_test "test removing a node in the middle of a line"
       test_removing_node_middle_of_line doc);
  Hashtbl.add table "ex_removing4.v"
    (create_fixed_test "test removing a node on the right of a line"
       test_removing_node_with_one_node_left_same_line doc);
  Hashtbl.add table "ex_removing_and_leaving_blank1.v"
    (create_fixed_test "test removing a node and leaving blank"
       test_removing_and_leaving_blank doc);
  Hashtbl.add table "ex_removing_and_leaving_blank2.v"
    (create_fixed_test "test removing a multi-lines node and leave it blank"
       test_removing_and_leaving_blank_multiple_line_nodes doc);
  Hashtbl.add table "ex_removing_and_leaving_blank3.v"
    (create_fixed_test
       "test removing a node and leaving a blank in the middle of a line"
       test_removing_and_leaving_blank_middle_of_line doc);
  Hashtbl.add table "ex_adding1.v"
    (create_fixed_test "test searching node" test_searching_node doc);
  Hashtbl.add table "ex_adding1.v"
    (create_fixed_test "test adding new nodes on an empty line"
       test_adding_node_on_empty_line doc);
  Hashtbl.add table "ex_adding2.v"
    (create_fixed_test "test adding new node on a filled line"
       test_adding_node_before_busy_line doc);
  Hashtbl.add table "ex_adding3.v"
    (create_fixed_test "test adding a new node spanning multiple lines"
       test_adding_multiple_line_node doc);
  Hashtbl.add table "ex_adding4.v"
    (create_fixed_test "test adding a node between two nodes on the same line"
       test_adding_node_between doc);
  Hashtbl.add table "ex_adding5.v"
    (create_fixed_test "test adding a node that will collide on another line"
       test_adding_collision_next_line doc);
  Hashtbl.add table "ex_adding6.v"
    (create_fixed_test "test adding a node that will collide with many nodes"
       test_adding_node_colliding_many doc);

  Hashtbl.add table "ex_replacing1.v"
    (create_fixed_test "test replacing the single node on one line"
       test_replacing_single_node_on_line doc);
  Hashtbl.add table "ex_replacing2.v"
    (create_fixed_test "test replacing the first node on one line"
       test_replacing_first_node_on_line doc);
  Hashtbl.add table "ex_replacing3.v"
    (create_fixed_test "test replacing a node in the middle of a line"
       test_replacing_node_in_middle_of_line doc);
  Hashtbl.add table "ex_replacing4.v"
    (create_fixed_test "test replacing a node with some spaces after"
       test_replacing_node_end_of_line doc);
  Hashtbl.add table "ex_replacing5.v"
    (create_fixed_test "test replacing a node with a bigger node"
       test_replacing_smaller_node_with_bigger_node doc);
  Hashtbl.add table "ex_replacing6.v"
    (create_fixed_test "test replacing a node with a smaller node"
       test_replacing_bigger_node_with_smaller_node doc);
  Hashtbl.add table "ex_replacing7.v"
    (create_fixed_test
       "test replacing a theorem block with another theorem block"
       test_replacing_block_by_other_block doc);

  Hashtbl.add table "ex_auto1.v"
    (create_fixed_test "test replacing simple auto with all the taken steps"
       test_replacing_simple_auto_by_steps doc);
  Hashtbl.add table "ex_auto2.v"
    (create_fixed_test "test replacing branching auto with all the taken steps"
       test_replace_multiple_branch_auto_by_steps doc);

  Hashtbl.add table "ex_command_oneliner.v"
    (create_fixed_test "test turning into a oneliner a proof with commands "
       test_turn_into_oneliner_with_commands doc);
  Hashtbl.add table "ex_curly_braces_oneliner.v"
    (create_fixed_test "test turning into a oneliner a proof with curly braces"
       test_turn_into_onliner_with_curly_braces doc);
  Hashtbl.add table "ex_admit_oneliner.v"
    (create_fixed_test
       "test turning into a oneliner an admitted proof (should do nothing)"
       test_turn_into_oneliner_admitted doc);
  Hashtbl.add table "ex_proof_with.v"
    (create_fixed_test "test turning into a oneliner a proof using Proof with"
       test_turn_into_oneliner_proof_with doc);
  Hashtbl.add table "ex_goal_select_oneliner.v"
    (create_fixed_test
       "test turning into a oneliner a proof with a goal selector"
       test_turn_into_onliner_goal_select doc);
  Hashtbl.add table "ex_match_oneliner.v"
    (create_fixed_test "test turning into a oneliner a proof with a match ltac"
       test_turn_into_onliner_match doc);
  Hashtbl.add table "ex_explicit_intros.v"
    (create_fixed_test
       "test making explicit the fresh variables of a simple intros"
       explicit_fresh_variables_simple_intros doc);
  Hashtbl.add table "ex_explicit_assert.v"
    (create_fixed_test
       "test making explicit the fresh variables of a simple assert"
       explicit_fresh_variables_simple_assert doc);
  Hashtbl.add table "ex_explicit_induction.v"
    (create_fixed_test
       "test making explicit the fresh variables of a simple induction"
       explicit_fresh_variables_simple_induction doc);
  Hashtbl.add table "ex_explicit_induction_list.v"
    (create_fixed_test
       "test making explicit the fresh variables of a list induction"
       explicit_fresh_variables_list_induction doc);
  Hashtbl.add table "ex_explicit_induction_long_inductive.v"
    (create_fixed_test
       "test making explicit the fresh variables of an induction with two \
        induction hypotheses"
       explicit_fresh_variables_two_induction_hypotheses doc);
  Hashtbl.add table "ex_goal_select_flattening1.v"
    (create_fixed_test "test flattening a single goal selector"
       test_flattening_goal_select_simple doc);

  (* Hashtbl.add table "ex_auto3.v" *)
  (*   (create_fixed_test "test replacing auto with zarith" *)
  (* test_replace_auto_using_zarith_by_steps doc); *)
  Hashtbl.add table "ex_auto4.v"
    (create_fixed_test "test replacing auto with backtracking by steps"
       test_replace_auto_with_backtracking doc);
  (* TODO commit files *)
  ()

let test_runner ~io:_ ~token:_ ~(doc : Doc.t) =
  let test_hash_table = Hashtbl.create 100 in

  Logs.set_reporter (Logs_fmt.reporter ());

  Logs.set_level (Some Logs.Debug);

  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let uri_name_str = Filename.basename uri_str in

  setup_test_table test_hash_table doc;
  let file_tests = Hashtbl.find_all test_hash_table uri_name_str in
  let tests = [ ("parsing tests", file_tests) ] in
  print_endline
    ("Running "
    ^ string_of_int (List.length file_tests)
    ^ " file test for: " ^ uri_name_str);
  flush_all ();
  if List.length file_tests > 0 then
    Alcotest.run ~and_exit:true
      ~argv:[| "ignored"; "--color=always" |]
      "document parsing and modification tests" tests
  else ()

let main () = Theory.Register.Completed.add test_runner
let () = main ()
