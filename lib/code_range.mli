type t = { start : Code_point.t; end_ : Code_point.t } [@@deriving sexp, yojson]

val pp : Format.formatter -> t -> unit
val to_string : t -> string
val code_range_from_lang_range : Lang.Range.t -> t
val range_from_starting_point_and_repr : Code_point.t -> string -> t
val are_flat_ranges_colliding : int * int -> int * int -> bool
val common_range : int * int -> int * int -> (int * int) option
