type sexp_query =
  | Q_anything
  | Q_empty
  | Q_atom of string
  | Q_field of string * sexp_query
  | Q_field_path of string list
  | Q_list_any of sexp_query
  | Q_list_exact of sexp_query list
  | Q_list_prefix of sexp_query list
  | Q_nth of int * sexp_query
  | Q_hd of sexp_query
  | Q_last of sexp_query
  | Q_and of sexp_query list
  | Q_or of sexp_query list
  | Q_not of sexp_query
  | Q_anywhere of sexp_query
  | Q_sequence of sexp_query list

val get_proof_proposition_sexp : Proof.t -> Sexplib.Sexp.t option
val matches : sexp_query -> Sexplib.Sexp.t -> bool
val extract_match : sexp_query -> Sexplib.Sexp.t -> Sexplib.Sexp.t option
val collect_matches : sexp_query -> Sexplib.Sexp.t -> Sexplib.Sexp.t list
