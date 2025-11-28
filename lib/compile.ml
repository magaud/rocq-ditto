open Fleche
open Sexplib.Std

type compilerArgs = {
  io : Io.CallBack.t;
  token : Coq.Limits.Token.t;
  env : Doc.Env.t;
}

let rec find_coqproject_dir (dir : string) : string option =
  let coqproject_filename = "_CoqProject" in
  let rocqproject_filename = "_RocqProject" in
  if
    Sys.file_exists (Filename.concat dir coqproject_filename)
    || Sys.file_exists (Filename.concat dir rocqproject_filename)
  then Some dir
  else if dir = "/" || dir = "." then None
  else find_coqproject_dir (Filename.dirname dir)

let rec find_coqproject_file (dir : string) : string option =
  let coqproject_filename = "_CoqProject" in
  let rocqproject_filename = "_RocqProject" in
  if Sys.file_exists (Filename.concat dir coqproject_filename) then
    Some (Filename.concat dir coqproject_filename)
  else if Sys.file_exists (Filename.concat dir rocqproject_filename) then
    Some (Filename.concat dir rocqproject_filename)
  else if dir = "/" || dir = "." then None
  else find_coqproject_file (Filename.dirname dir)

let rec find_coqproject_dir_and_file (dir : string) : (string * string) option =
  let coqproject_filename = "_CoqProject" in
  let rocqproject_filename = "_RocqProject" in
  if Sys.file_exists (Filename.concat dir coqproject_filename) then
    Some (dir, coqproject_filename)
  else if Sys.file_exists (Filename.concat dir rocqproject_filename) then
    Some (dir, rocqproject_filename)
  else if dir = "/" || dir = "." then None
  else find_coqproject_dir_and_file (Filename.dirname dir)

let read_all ic =
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file -> List.rev acc
  in
  loop []

let coqproject_sorted_files (coqproject_file : string) :
    (string list, Error.t) result =
  let cmd =
    Rocq_version.dep_executable ^ Printf.sprintf " -f %s -sort" coqproject_file
  in
  let ic = Unix.open_process_in cmd in
  let lines = read_all ic in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 ->
      Ok
        (List.filter
           (fun x -> String.length x > 0)
           (String.split_on_char ' ' (List.hd lines)))
  | Unix.WEXITED n ->
      Error.format_to_or_error "%s exited with %d; output:\n%s"
        Rocq_version.dep_executable n (String.concat "\n" lines)
  | _ ->
      Error.string_to_or_error
        (Rocq_version.dep_executable ^ " terminated abnormally")

let list_to_str pp_elem l =
  let elems = List.map pp_elem l |> String.concat "; " in
  "[" ^ elems ^ "]"

let list_of_list_to_str pp_elem lsts =
  let inner = List.map (list_to_str pp_elem) lsts |> String.concat "; " in
  "[" ^ inner ^ "]"

let list_of_list_of_str_to_str lsts : string = list_of_list_to_str Fun.id lsts

let string_of_table (tbl : (string, string list) Hashtbl.t) =
  Hashtbl.fold
    (fun key values acc ->
      let joined = String.concat ", " values in
      (key ^ " -> " ^ joined) :: acc)
    tbl []
  |> String.concat "\n"

let coqproject_to_dep_graph (coqproject_file : string) :
    ((string, string list) Hashtbl.t, Error.t) result =
  let cmd =
    Rocq_version.dep_executable ^ Printf.sprintf " -f %s" coqproject_file
  in
  let ic = Unix.open_process_in cmd in
  let lines = read_all ic in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 ->
      let re = Re.compile (Re.str "required_vo:") in
      let split = List.map (Re.split_delim re) lines in
      let filenames =
        List.map
          (fun x ->
            let hd = List.hd x in
            let filename_vo =
              String.split_on_char ' ' hd |> List.hd |> String.trim
            in
            let filename =
              String.sub filename_vo 0 (String.length filename_vo - 1)
            in
            filename)
          split
      in
      let tails =
        List.map
          (fun x ->
            let tl = List.nth x 1 in
            (String.split_on_char ' ') tl)
          split
      in

      let tails_filenames =
        List.map
          (fun l ->
            List.filter_map
              (fun x ->
                let trimmed = String.trim x in
                if String.ends_with ~suffix:".vo" trimmed then
                  Some (String.sub trimmed 0 (String.length trimmed - 1))
                else if String.ends_with ~suffix:".v" trimmed then Some trimmed
                else None)
              l)
          tails
      in

      let parents_table = Hashtbl.create (List.length filenames) in
      List.iteri
        (fun idx x ->
          let matching_tail =
            List.nth tails_filenames idx
            |> List.filter (fun elem_tl -> not (String.equal elem_tl x))
            (* avoid making a recursive parent table *)
          in
          if List.length matching_tail > 0 then
            Hashtbl.add parents_table x matching_tail)
        filenames;

      Ok parents_table
  | Unix.WEXITED n ->
      Error.format_to_or_error "%s exited with %d; output:\n%s"
        Rocq_version.dep_executable n (String.concat "\n" lines)
  | _ ->
      Error.string_to_or_error
        (Rocq_version.dep_executable ^ " terminated abnormally")

let get_file_dependencies (fname : string)
    (dep_graph : (string, string list) Hashtbl.t) : string list =
  let rec aux filename : string list =
    let curr_deps = Hashtbl.find_all dep_graph filename |> List.concat in
    (* we want an empty list in case of no value found *)
    let deps =
      List.map aux curr_deps |> List.concat |> List.sort_uniq String.compare
    in
    curr_deps @ deps
  in
  aux fname

let diagnostic_to_error (x : Lang.Diagnostic.t) : Error.t =
  let msg_string = Pp.string_of_ppcmds x.message in

  let err = Error.of_string msg_string in
  let err =
    Error.tag_arg err "range"
      (Code_range.code_range_from_lang_range x.range)
      Code_range.sexp_of_t
  in
  Error.tag_arg err "severity" x.severity sexp_of_int

let compile_file (io : Io.CallBack.t) (env : Doc.Env.t) (filepath : string) :
    (Doc.t, Error.t list) result =
  let token = Coq.Limits.Token.create () in

  match Lang.LUri.(File.of_uri (of_string filepath)) with
  | Error _ -> Error [ Error.of_string "Invalid uri" ]
  | Ok uri -> (
      let raw =
        Coq.Compat.Ocaml_414.In_channel.(with_open_bin filepath input_all)
      in

      let doc =
        Fleche.Doc.create ~token ~env ~uri ~languageId:"Coq" ~version:0 ~raw
      in
      let doc = Fleche.Doc.check ~io ~token ~target:Doc.Target.End ~doc () in

      match doc.completed with
      | Yes _ -> Ok doc
      | Stopped _ ->
          let diags =
            List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes
          in
          let errors = List.filter Lang.Diagnostic.is_error diags in
          let err = Error.of_string "Parsing stopped" in
          Error (err :: List.map diagnostic_to_error errors)
      | Failed _ ->
          let diags =
            List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes
          in
          let errors = List.filter Lang.Diagnostic.is_error diags in
          let err = Error.of_string "Parsing failed" in
          Error (err :: List.map diagnostic_to_error errors))
