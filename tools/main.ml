open Ditto

let get_dependencies () =
  let ( let* ) = Result.bind in
  if Array.length Sys.argv != 2 then
    Error.string_to_or_error "Usage: get-dependencies file"
  else
    let filename = Sys.argv.(1) in
    if Filesystem.is_directory filename then
      Error.string_to_or_error "Please provide a file, not a directory"
    else if not (Sys.file_exists filename) then
      Error.string_to_or_error "Please provide an existing file"
    else
      match Compile.find_coqproject_dir_and_file filename with
      | None ->
          Error.string_to_or_error
            "No _CoqProject or _RocqProject associated with the file found"
      | Some (project_dir, project_file) ->
          let* dep_graph =
            Compile.coqproject_to_dep_graph
              (Filename.concat project_dir project_file)
          in
          let dependencies = Compile.get_file_dependencies filename dep_graph in
          List.iter print_endline dependencies;
          Ok ()

let main =
  match get_dependencies () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
