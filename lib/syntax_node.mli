open Fleche
open Vernacexpr

type t = {
  ast : Doc.Node.Ast.t option;
  range : Code_range.t;
  repr : string Lazy.t;
  id : Uuidm.t;
  proof_id : int option;
  diagnostics : Lang.Diagnostic.t list;
}

val repr : t -> string
val compare_nodes : t -> t -> int
val are_colliding : t -> t -> bool

val colliding_nodes : t -> t list -> t list
(** [colliding_nodes target nodes_list] return the nodes in [nodes_lists]
    colliding with [target] *)

val syntax_node_of_coq_ast : Coq.Ast.t -> Code_point.t -> t
(** [syntax_node_of_coq_ast ast starting_point] create a syntax node from a Coq
    AST element and a point to start the node. *)

val comment_syntax_node_of_string :
  string -> Code_point.t -> (t, Error.t) result
(** [comment_syntax_node_of_string content range] create a syntax node
    representing a comment containing the string content starting at the
    specified point *)

val syntax_node_of_string : string -> Code_point.t -> (t, Error.t) result
(** [syntax_node_of_string code start_point] returns a result [Ok Syntax_node]
    if [code] was parsed as only one syntax node that will be positioned
    starting at [start_point] or [Error string] with a string containing the
    error message detailing why the node was not able to be created *)

val reformat_node : t -> (t, Error.t) result
(** [reformat_node node] reformat a node. The [node] is reformatted by turning
    it into a coq_ast and then using pr_vernac to reformat the string. Return
    [Error] if [node.ast] is none. *)

val validate_syntax_node : t -> (t, Error.t) result

val mk_vernac_control :
  ?loc:Loc.t -> synterp_vernac_expr vernac_expr_gen -> vernac_control

val shift_point : int -> int -> Code_point.t -> Code_point.t
(** [shift_point n_line n_char point] shift [point] by [n_line], and [n_char].
*)

val shift_range : int -> int -> Code_range.t -> Code_range.t
(** [shift_range n_line n_char range] shift both points of [range] by [n_line],
    [n_char] *)

val shift_node : int -> int -> t -> t
(** [shift_node n_line n_char node] shift the range of [node] by [n_line],
    [n_char] using [shift_range] *)

val is_syntax_node_command_allowed_in_proof : t -> bool
(** [is_syntax_node_command_allowed_in_proof x] checks if [x] is a command
    allowed inside a proof block context *)

val is_syntax_node_proof_with : t -> bool
val get_syntax_node_proof_with_tactic : t -> string option
val is_syntax_node_ending_with_elipsis : t -> bool

val is_syntax_node_tactic : t -> bool
(** [is_syntax_node_tactic x] checks if [x] represents a tactic. *)

val is_syntax_node_bullet : t -> bool
(** [is_syntax_node_bullet x] check if [x] is a Rocq bullet made of repeated -,
    + or * symbols *)

val is_syntax_node_opening_bracket : t -> bool
val is_syntax_node_closing_bracket : t -> bool
val is_syntax_node_focusing_goal : t -> bool
val is_syntax_node_variable : t -> bool
val is_syntax_node_fixpoint : t -> bool
val is_syntax_node_section_command : t -> bool
val is_syntax_node_end_section_command : t -> bool
val is_syntax_node_definition_command : t -> bool
val is_syntax_node_notation_command : t -> bool
val is_syntax_node_create_hintdb_command : t -> bool
val is_syntax_node_hint_command : t -> bool
val is_syntax_node_instance : t -> bool

val is_syntax_node_focus_command : t -> bool
(** [is_syntax_node_focus_command] check if [x] is the command [Focus] *)

val is_syntax_node_proof_start : t -> bool
(** [is_syntax_node_proof_start x] checks if [x] marks the start of a proof.
    meaning if it's a sentence starting with: Theorem | Lemma | Fact | Remark |
    Property | Proposition | Corollary *)

val is_syntax_node_proof_end : t -> bool
(** [is_syntax_node_proof_end x] checks if [x] marks the end of a proof. meaning
    if it's either Qed. or Admitted. *)

val is_syntax_node_proof_command : t -> bool
(** [is_syntax_node_proof_command x] check if [x] is the command Proof. *)

val is_syntax_node_context : t -> bool
(** [is_syntax_node_context x] check if [x] is a context command. *)

val is_syntax_node_require : t -> bool
(** [is_syntax_node_require x] check if [x] is the Require command. *)

val is_syntax_node_inductive : t -> bool
(** [is_syntax_node_inductive x] check if [x] is the Inductive/Class command. *)

val is_syntax_node_proof_intro_or_end : t -> bool
(** [is_syntax_node_proof_intro_or_end x] check if [x] is an intro of a proof or
    an end of a proof, meaning if it's either a a sentence starting with:
    Theorem | Lemma | Fact | Remark | Property | Proposition | Corollary or the
    command Proof, Qed or Admitted *)

val is_syntax_node_proof_abort : t -> bool
(** [is_syntax_node_proof_abort x] check if [x] abort a proof, meaning it's
    either Abort or Abort all *)

val node_can_open_proof : t -> bool
(** [node_can_open_proof x] check if [x] can start a proof, meaning it's either:
    - a sentence starting with: Theorem | Lemma | Fact | Remark | Property |
      Proposition | Corollary
    - a sentence starting with Goal (anonymous goal)
    - a definition with a proof
    - an Instance with a proof
    - a Function with a proof *)

val node_can_close_proof : t -> bool
(** [node_can_close_proof x] check if [x] can close a proof, meaning it's either
    Qed, Admitted, Abort or Abort all *)

open Raw_gen_args_converter

val get_syntax_node_extend_name : t -> extend_name option

val get_tactic_raw_generic_arguments :
  t -> Genarg.raw_generic_argument list option

val tactic_raw_generic_arguments_to_syntax_node :
  extend_name -> Genarg.raw_generic_argument list -> Code_point.t -> t option

val raw_tactic_expr_to_syntax_node :
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  ?selector:Goal_select_view.t ->
  ?use_default:bool ->
  Code_point.t ->
  (t, Error.t) result

val get_node_goal_selector_opt : t -> Goal_select_view.t option
val get_node_raw_tactic_expr : t -> Ltac_plugin.Tacexpr.raw_tactic_expr option

val get_node_raw_atomic_tactic_expr :
  t -> Ltac_plugin.Tacexpr.raw_atomic_tactic_expr option

val get_node_ltac_elements : t -> ltac_elements option
val drop_goal_selector : t -> t
val add_goal_selector : t -> Goal_select_view.t -> (t, Error.t) result
val is_syntax_node_intros : t -> bool

val apply_tac_then :
  t -> t -> ?start_point:Code_point.t -> unit -> (t, Error.t) result

val apply_tac_thens :
  t -> t list -> ?start_point:Code_point.t -> unit -> (t, Error.t) result
