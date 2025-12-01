open Proof
open Nary_tree

val fold_replace_assumption_with_apply :
  Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result

val id_transform :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val remove_unecessary_steps :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val fold_add_time_taken :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val replace_auto_with_steps :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val compress_intro :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val admit_proof :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val admit_and_comment_proof_steps :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val remove_random_step :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val simple_proof_repair :
  Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result

val admit_branch_at_error :
  Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result

val cut_replace_branch :
  string ->
  Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result

val explicit_fresh_variables :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val flatten_goal_selectors :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val turn_into_oneliner :
  Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result

val apply_proof_transformation :
  (Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result) ->
  Rocq_document.t ->
  (Rocq_document.t, Error.t) result

val apply_proof_tree_transformation :
  (Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result) ->
  Rocq_document.t ->
  (Rocq_document.t, Error.t) result
