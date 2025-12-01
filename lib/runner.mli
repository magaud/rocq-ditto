open Nary_tree

val run_with_timeout :
  token:Coq.Limits.Token.t ->
  timeout:int ->
  f:('a -> ('b, Error.t) result) ->
  'a ->
  ('b, Error.t) result

val protect_to_result : ('a, 'b) Coq.Protect.E.t -> ('a, Error.t) result

val protect_to_result_with_feedback :
  ('a, 'b) Coq.Protect.E.t ->
  ('a * 'b Coq.Message.t list, Error.t * 'b Coq.Message.t list) Result.t

val run_node :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  Syntax_node.t ->
  (Coq.State.t, Error.t) result

val run_node_with_diagnostics :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  Syntax_node.t ->
  ( Coq.State.t * Lang.Diagnostic.t list,
    Error.t * Lang.Diagnostic.t list )
  result

val get_init_state :
  Rocq_document.t ->
  Syntax_node.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t, Error.t) result

val goals :
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  ((string Coq.Goals.Reified_goal.t, string) Coq.Goals.t option, Error.t) result

val get_proof_state : (Coq.State.t, Loc.t) Coq.Protect.E.t -> Coq.State.t

val reified_goals_at_state :
  Coq.Limits.Token.t -> Coq.State.t -> string Coq.Goals.Reified_goal.t list

val count_goals : Coq.Limits.Token.t -> Coq.State.t -> int

val proof_steps_with_goalcount :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  Syntax_node.t list ->
  (int * Syntax_node.t * int) list

(* val remove_focus : *)
(*   (int * Syntax_node.t * int) list -> (int * Syntax_node.t * int) list *)

val get_hypothesis_names : string Coq.Goals.Reified_goal.t -> string list

val get_current_goal :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  (string Coq.Goals.Reified_goal.t, Error.t) result

val can_reduce_to_zero_goals : Coq.State.t -> Syntax_node.t list -> bool
val is_valid_proof : Rocq_document.t -> Proof.t -> bool
val tree_to_proof : Syntax_node.t nary_tree -> (Proof.t, Error.t) result

val proof_tree_from_parents :
  int * Syntax_node.t ->
  (int * Syntax_node.t, int * Syntax_node.t) Hashtbl.t ->
  Syntax_node.t nary_tree

val treeify_proof :
  Rocq_document.t -> Proof.t -> (Syntax_node.t nary_tree, Error.t) result

val fold_nodes_with_state :
  (Coq.State.t -> 'acc -> Syntax_node.t -> (Coq.State.t * 'acc, Error.t) result) ->
  Coq.State.t ->
  'acc ->
  Syntax_node.t list ->
  ('acc, Error.t) result

val fold_proof_with_state :
  Rocq_document.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t -> 'acc -> Syntax_node.t -> (Coq.State.t * 'acc, Error.t) result) ->
  'acc ->
  Proof.t ->
  ('acc, Error.t) result

val depth_first_fold_with_state :
  Rocq_document.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t -> 'acc -> Syntax_node.t -> (Coq.State.t * 'acc, Error.t) result) ->
  'acc ->
  Syntax_node.t nary_tree ->
  ('acc, Error.t) result
