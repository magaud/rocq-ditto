open Nary_tree

type proof_status = Admitted | Proved | Aborted
[@@deriving show { with_path = false }]

val pp_proof_status : Format.formatter -> proof_status -> unit

type attach_position = LineAfter | LineBefore | SameLine
[@@deriving show { with_path = false }]

type transformation_step =
  | Remove of Uuidm.t
  | Replace of Uuidm.t * Syntax_node.t
  | Add of Syntax_node.t
  | Attach of Syntax_node.t * attach_position * Uuidm.t

val pp_transformation_step : Format.formatter -> transformation_step -> unit
val transformation_step_to_string : transformation_step -> string

type t = {
  proposition : Syntax_node.t;
  proof_steps : Syntax_node.t list;
  status : proof_status;
}
(** Represents a proof in a Coq document. [proof] contains the initial
    proposition and a list of proof steps. *)

val get_names : Syntax_node.t -> string list
(** Get the names of a node. A node can have multiple names (i.e., mutual
    recursive definitions) *)

val get_theorem_kind : t -> Decls.theorem_kind option
(** Get the theorem kind of a proof. If the proof isn't a basic assertion
    command ie: Theorem, Lemma, Fact, Remark, Property, Proposition or
    Corollary, return [None], otherwise return the kind of the theorem. *)

val get_constr_expr : t -> Constrexpr.constr_expr option
(** Get the constr_expr of the proof. If the proof start a theorem or a proof
    (as it should) return the [Constrexpr.constr_expr] representing the
    expression stated by the proof or theorem, otherwise return [None] *)

type theorem_components = {
  kind : Decls.theorem_kind;
  name : Names.lident;
  universe : Constrexpr.universe_decl_expr option;
  binders : Constrexpr.local_binder_expr list;
  expr : Constrexpr.constr_expr;
}

val get_theorem_components : t -> theorem_components option

val syntax_node_of_theorem_components :
  theorem_components -> Code_point.t -> Syntax_node.t

val get_proof_name : t -> string option
(** Retrieve the name of the proof's proposition if available.
    [get_proof_name p] returns [Some name] if the proof [p] has a proposition
    with a name, otherwise it returns [None]. *)

val get_proof_status : t -> proof_status option
(** Get the proof status of a proof. [get_proof_status proof] returns a
    [proof_status] wrapped in [Some] matching the status of the last node of the
    function. returns [Aborted] for both [Abort] and [Abort All]. Returns [None]
    if there isn't a last node or it doesn't match a type in [proof_status]. *)

val proof_status_from_last_node :
  Syntax_node.t -> (proof_status, Error.t) result
(** Get the proof status of the last node of a proof or an error if the node
    isn't a closing node. If the proof was proved, return [Proved], if the proof
    is admitted, return [Admitted], and if the proof was aborted with Abort or
    Abort All, return [Aborted] otherwise, return an error. *)

val print_tree : Syntax_node.t nary_tree -> string -> unit
(** Print a tree structure with indentation. [print_tree tree indent] prints a
    tree, where [tree] is an [Syntax_node.t nary_tree] and [indent] is a string
    used for indentation to represent the tree structure visually. *)

val proof_nodes : t -> Syntax_node.t list
(** Extracts the nodes from a proof. [proof_nodes p] returns a list containing
    the proposition of the proof [p] followed by its proof steps. *)

val proof_from_nodes : Syntax_node.t list -> (t, Error.t) result
(** Create a proof from a list of annotated AST nodes. [proof_from_nodes nodes]
    takes a list of nodes and returns a proof where the first node in the list
    is used as the proposition, and the remaining nodes are the proof steps. If
    the list made of less than three nodes or the last node isn't a valid proof
    end, return an error. *)
