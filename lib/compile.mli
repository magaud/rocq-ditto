open Fleche

type compilerArgs = {
  io : Io.CallBack.t;
  token : Coq.Limits.Token.t;
  env : Doc.Env.t;
}

val find_coqproject_dir : string -> string option
val find_coqproject_file : string -> string option
val find_coqproject_dir_and_file : string -> (string * string) option
val coqproject_sorted_files : string -> (string list, Error.t) result

val coqproject_to_dep_graph :
  string -> ((string, string list) Hashtbl.t, Error.t) result

val get_file_dependencies :
  string -> (string, string list) Hashtbl.t -> string list

val compile_file :
  Io.CallBack.t -> Doc.Env.t -> string -> (Doc.t, Error.t list) result
