open Proof
open Fleche

type t = {
  filename : string;
  elements : Syntax_node.t list;
  document_repr : string;
  initial_state : Coq.State.t;
}

type removeMethod = LeaveBlank | ShiftNode
type shiftMethod = ShiftVertically | ShiftHorizontally

val pp_coq_document : Format.formatter -> t -> unit
val parse_document : Doc.t -> t

val element_with_id_opt : Uuidm.t -> t -> Syntax_node.t option
(** Find an element with a specific ID in a document.
    [element_with_id_opt element_id doc] returns [Some element] if an element
    with the given [element_id] exists in [doc], otherwise returns [None]. *)

val proof_with_id_opt : Uuidm.t -> t -> Proof.t option
(** Find a proof with a specific proposition ID.
    [proof_with_id_opt proof_id doc] returns [Some element] if a proof has a
    proposition with the given [proof_id] exists in [doc], otherwise returns
    [None]. *)

val proof_with_name_opt : string -> t -> Proof.t option
(** Find a proof with a specific name. [proof_with_name_opt proof_name doc]
    returns [Some element] if a proof has the name [proof_name] where proof_name
    match the ident_decl of a command in \{Theorem, Lemma, Fact, Remark,
    Corollary, Proposition, Property\} for example. *)

val split_at_id : Uuidm.t -> t -> Syntax_node.t list * Syntax_node.t list
(** Split a document in two list of nodes, between and after the target id.
    [split_at_id target_id doc] split [doc.elements] into two list, one with the
    elements positioned before [target_id] and one with the elements after
    [target_id]. [target_id] node is excluded, and if not found, return
    [(doc.elements,[])] *)

val remove_node_with_id :
  Uuidm.t -> ?remove_method:removeMethod -> t -> (t, Error.t) result
(** Remove a node with a specific ID from the document.
    [remove_node_with_id ?remove_method target_id doc] removes the element with
    the given [target_id] from the document [doc]. If the element is found, it
    returns a new document with the element removed wrapped in [Ok], potentially
    adjusting the line numbers of subsequent elements. If the [remove_method] is
    [LeaveBlank] then the other nodes are not moved. If the element is not
    found, it returns an [Error] indicating that the element wasn't found. *)

val insert_node :
  Syntax_node.t -> ?shift_method:shiftMethod -> t -> (t, Error.t) result
(** Insert a new node into the document.
    [insert_node new_node ?shift_method doc] attempt to insert [new_node] into
    the document by shifting the other nodes further to make space. Can fail if
    the [shift_method] is [ShiftHorizontally] and the node inserted has an
    height higher than one or one of the node after on the line has an height
    higher than one. *)

val replace_node : Uuidm.t -> Syntax_node.t -> t -> (t, Error.t) result
(** Replace a node inside the document. [replace_node target_id new_node doc]
    replace the node with id [target_id] by [new_node]. Fail and return [Error]
    if a node with [target_id] isn't found in the document. *)

val replace_proof : Uuidm.t -> Proof.t -> t -> transformation_step list option
(** Get the transformation steps needed to replace a proof inside the document.
    [replace_proof target_id new_proof doc] return either a list of
    transformation steps to replace a proof wrapped in [Some] if a proof
    proposition with the id [target_id] exists and [None] otherwise *)

val get_proofs : t -> (Proof.t list, Error.t) result
(** Extract proofs from a document. [get_proofs doc] takes a document [doc] of
    type [t] and returns a list of proofs. Each proof is constructed by
    aggregating elements of the document that share the same proof identifier.
*)

val dump_to_string : t -> (string, Error.t) result
(** Convert an annotated document to a string representation.
    [dump_to_string doc] returns a string wrapped in [Ok] that represents the
    structure of the annotated document [doc], formatting the nodes according to
    their positions and characters in the document. If the document is
    malformed, return [Error] *)

val apply_transformation_step : transformation_step -> t -> (t, Error.t) result
(** Apply a transformation step to a document.
    [apply_transformation_step step doc] returns a [Rocq_document] wrapped in
    with the following function applied:
    - [Remove id]: [remove_node_with_id id ShiftNode doc]
    - [Replace id new_node]: [replace_node id new_node doc]
    - [Add new_node]: [insert_node new_node doc]
    - [Attach attached_node attach_position anchor_id] : Use an heuristic to
      place a node either a [LineBefore] or a [LineAfter] the node with id
      [anchor_id], fail with error if the anchor isn't found. *)

val apply_transformations_steps :
  transformation_step list -> t -> (t, Error.t) result
(** Repeatably apply [apply_transformation_step].
    [apply_transformation_steps steps doc] fold [doc] until one step return an
    [Error] or the resulting document is returned wrapped in [Ok] *)
