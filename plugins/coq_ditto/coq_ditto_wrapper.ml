open Ditto_cli_lib.Cli
open Ditto
open Cmdliner

type cli_options = {
  input : string;
  output : string;
  transformation : transformation_kind;
  verbose : bool;
  quiet : bool;
  save_vo : bool;
  reverse_order : bool;
  skipped_files : string list;
  dependencies_action : dependencies_action;
}

let string_of_process_status = function
  | Unix.WEXITED code -> Printf.sprintf "Exited with code %d" code
  | Unix.WSIGNALED signal -> Printf.sprintf "Killed by signal %d" signal
  | Unix.WSTOPPED signal -> Printf.sprintf "Stopped by signal %d" signal

let remove_prefix (str : string) (prefix : string) =
  let prefix_len = String.length prefix in
  if String.length str >= prefix_len && String.sub str 0 prefix_len = prefix
  then String.sub str prefix_len (String.length str - prefix_len)
  else str

let warn_if_exists (dir_state : Filesystem.newDirState) =
  match dir_state with
  | AlreadyExists ->
      Printf.printf
        "Warning: output directory already exists: replacing files\n%!"
  | _ -> ()

let validate_opts opts pathkind =
  if pathkind = Filesystem.File && opts.skipped_files <> [] then
    Error.string_to_or_error
      "Using --skip with a single file doesn't make sense"
  else if opts.dependencies_action != NoAction && pathkind = Filesystem.Dir then
    Error.string_to_or_error
      "Using a dependency action when targeting a folder doesn't make sense"
  else if opts.verbose && opts.quiet then
    Error.string_to_or_error "Cannot use both --verbose and --quiet"
  else Ok ()

let run_process ~(env : string array) ~(args : string array) (prog : string)
    (stdin : Unix.file_descr) (stdout : Unix.file_descr)
    (stderr : Unix.file_descr) =
  (* Open /dev/null for output redirection *)
  let pid = Unix.create_process_env prog args env stdin stdout stderr in
  let _, status = Unix.waitpid [] pid in
  match status with
  | WEXITED 0 -> Ok ()
  | _ -> Error.string_to_or_error (string_of_process_status status)

let run_process_loud ~(env : string array) ~(args : string array)
    (prog : string) =
  run_process ~env ~args prog Unix.stdin Unix.stdout Unix.stderr

let run_process_silent ~(env : string array) ~(args : string array)
    (prog : string) =
  let devnull = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0o666 in
  run_process ~env ~args prog devnull devnull devnull

let make_args_transform_files (prog : string) (root : string) (verbose : bool)
    (save_vo : bool) (input_file : string) =
  let base =
    [| prog; "--root=" ^ root; "--plugin=ditto-plugin"; input_file |]
  in
  base |> fun a ->
  if verbose then Array.append a [| "--display=verbose" |]
  else
    Array.append a [| "--display=quiet" |] |> fun a ->
    if save_vo then Array.append a [| "--no_vo" |] else a

let make_args_compile_files (root : string) (input_file : string) =
  [| "fcc"; "--root=" ^ root; input_file |]

let transform_files (root : string) (dep_files : string list) (prog : string)
    (total_file_count : int) (base_env : string array) (save_vo : bool)
    (verbose : bool) =
  List.fold_left
    (fun (err_acc, curr_file_count) curr_file ->
      match err_acc with
      | Ok () ->
          let curr_args =
            make_args_transform_files prog root verbose save_vo curr_file
          in
          let curr_env =
            Array.append base_env
              [|
                "OUTPUT_FILENAME=" ^ curr_file;
                "CURRENT_FILE_COUNT=" ^ string_of_int curr_file_count;
                "TOTAL_FILE_COUNT=" ^ string_of_int total_file_count;
              |]
          in
          let status = run_process_loud ~env:curr_env ~args:curr_args prog in
          Printf.printf "\n%!";
          (status, curr_file_count + 1)
      | err -> (err, curr_file_count + 1))
    (Ok (), 1) dep_files

let compile_files (files : string list) (input : string) (root : string) =
  let prog = "fcc" in
  List.fold_left
    (fun (err_acc, curr_file_count) curr_file ->
      match err_acc with
      | Ok () ->
          Printf.printf "compiling file %s\n%!" curr_file;
          let curr_args = make_args_compile_files root curr_file in
          let status = run_process_silent ~env:[||] ~args:curr_args prog in
          (status, curr_file_count + 1)
      | err -> (err, curr_file_count + 1))
    (Ok (), 1) files

let transform_project (opts : cli_options) : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let input = opts.input
  and output = opts.output
  and transformation = transformation_kind_to_string opts.transformation
  and verbose = opts.verbose
  and quiet = opts.quiet
  and save_vo = opts.save_vo
  and reverse_order = opts.reverse_order in

  let out = Format.std_formatter in
  let reporter =
    Logs_fmt.reporter ~pp_header:pp_header_no_app ~app:out ~dst:out ()
  in
  Logs.set_reporter reporter;
  Logs.set_level (Some (if verbose then Debug else Info));

  let exec_name = Filename.basename Sys.argv.(0) in
  (match exec_name with
  | "coq-ditto" ->
      Logs.warn (fun m ->
          m
            "Alias coq-ditto might disappear in the future, please use \
             rocq-ditto instead")
  | _ -> ());

  let pathkind = Filesystem.get_pathkind input in

  let _ = validate_opts opts pathkind in

  let base_env =
    Array.append (Unix.environment ())
      [|
        "DITTO_TRANSFORMATION=" ^ transformation;
        "DEBUG_LEVEL=" ^ string_of_bool verbose;
        "SAVE_VO=" ^ string_of_bool save_vo;
        "QUIET=" ^ string_of_bool quiet;
        "REVERSE_ORDER=" ^ string_of_bool reverse_order;
      |]
  in
  let prog = "fcc" in
  match pathkind with
  | File ->
      if Filesystem.is_directory output then
        Error.string_to_or_error
          "Output must be a filename when input is a file"
      else if not (Sys.file_exists input) then
        Error.string_to_or_error "Input must be an existing file"
      else
        let coqproject_opt = Compile.find_coqproject_dir_and_file input in

        let input_dir =
          match coqproject_opt with
          | Some (dir, _) -> dir
          | None -> Filename.dirname input
        in

        let* _ =
          match opts.dependencies_action with
          | NoAction -> Ok ()
          | CompileDependencies -> (
              match coqproject_opt with
              | None ->
                  Error.string_to_or_error
                    "No _CoqProject or _RocqProject found, impossible to run a \
                     dependency action"
              | Some (dir, file) ->
                  let* dep_graph =
                    Compile.coqproject_to_dep_graph (Filename.concat dir file)
                  in
                  let dependencies =
                    Compile.get_file_dependencies input dep_graph
                  in
                  Printf.printf "Compiling %d dependencies\n%!"
                    (List.length dependencies);
                  let res, _ = compile_files dependencies input dir in
                  res)
          | TransformDependencies -> (
              match coqproject_opt with
              | None ->
                  Error.string_to_or_error
                    "No _CoqProject or _RocqProject found, impossible to run a \
                     dependency action"
              | Some (dir, file) ->
                  let* dep_graph =
                    Compile.coqproject_to_dep_graph (Filename.concat dir file)
                  in
                  let dependencies =
                    Compile.get_file_dependencies input dep_graph
                  in
                  let length_dep = List.length dependencies in
                  Printf.printf "Transforming %d dependencies\n%!" length_dep;
                  let res, _ =
                    transform_files dir dependencies "fcc" length_dep base_env
                      true verbose
                  in
                  res)
        in

        let env = Array.append base_env [| "OUTPUT_FILENAME=" ^ output |] in

        let args =
          make_args_transform_files prog input_dir verbose save_vo input
        in
        run_process_loud ~env ~args prog
  | Dir -> (
      match Compile.find_coqproject_dir_and_file input with
      | None ->
          Error.format_to_or_error
            "No _CoqProject or _RocqProject file found in %s" input
      | Some (coqproject_dir, coqproject_file) ->
          let coqproject_path =
            Filename.concat coqproject_dir coqproject_file
          in
          let open CoqProject_file in
          let p =
            CoqProject_file.read_project_file
              ~warning_fn:(fun _ -> ())
              coqproject_path
          in

          let filenames =
            List.map (fun x -> Filename.basename x.thing) p.files
          in
          let* dep_files = Compile.coqproject_sorted_files coqproject_path in
          let dep_files =
            List.map
              (fun file ->
                let rel_file_path = remove_prefix file input in
                let out_path = Filename.concat output rel_file_path in

                out_path)
              dep_files
          in

          let* new_dir_state = Filesystem.make_dir output in
          warn_if_exists new_dir_state;
          let* _ = Filesystem.copy_dir input output filenames in
          let* _ =
            Filesystem.copy_file coqproject_path
              (Filename.concat output coqproject_file)
          in

          let total_file_count = List.length dep_files in

          let transformations_status =
            transform_files output dep_files prog total_file_count base_env
              save_vo verbose
          in
          fst transformations_status)

(* --- Cmdliner definitions ------------------------------------------- *)

let transformation_kind_conv =
  let parse s =
    match arg_to_transformation_kind s with
    | Ok v -> Ok v
    | Error e -> Error (`Msg (Error.to_string_hum e))
  in
  let print fmt k = Format.fprintf fmt "%s" (transformation_kind_to_string k) in
  Cmdliner.Arg.conv (parse, print)

let dependencies_action_conv =
  let parse s =
    match arg_to_dependencies_action s with
    | Ok v -> Ok v
    | Error e -> Error (`Msg (Error.to_string_hum e))
  in
  let print fmt k = Format.fprintf fmt "%s" (dependencies_action_to_string k) in
  Cmdliner.Arg.conv (parse, print)

let input_t =
  let doc = "Input folder or filename." in
  Arg.(
    required
    & opt (some filepath) None
    & info [ "i"; "input" ] ~docv:"PATH" ~doc)

let output_t =
  let doc = "Output folder or filename." in
  Arg.(
    required
    & opt (some filepath) None
    & info [ "o"; "output" ] ~docv:"PATH" ~doc)

let transformation_t =
  let doc = "Transformation to apply." in
  Arg.(
    required
    & opt (some transformation_kind_conv) None
    & info [ "t"; "transformation" ] ~docv:"KIND" ~doc)

let dependencies_action_t =
  let doc =
    "Action to apply on the dependencies (only when targeting a single file)"
  in
  Arg.(
    value
    & opt dependencies_action_conv NoAction
    & info [ "a"; "action" ] ~docv:"ACTION" ~doc)

let skip_t =
  let doc = "Files to skip (can be given multiple times)." in
  Arg.(value & opt_all string [] & info [ "skip" ] ~docv:"FILE" ~doc)

let verbose_t =
  Arg.(value & flag & info [ "v"; "verbose" ] ~doc:"Enable verbose output.")

let quiet_t =
  Arg.(value & flag & info [ "quiet" ] ~doc:"Suppress non-error output.")

let save_vo_t =
  Arg.(value & flag & info [ "save-vo" ] ~doc:"Save .vo of transformed file.")

let reverse_order_t =
  Arg.(
    value & flag
    & info [ "reverse-order" ]
        ~doc:
          "Reverse the order of proof processing to improve cache hits (may \
           produce invalid output).")

let cli_options_t =
  let combine input output transformation verbose quiet save_vo reverse_order
      skipped_files dependencies_action =
    {
      input;
      output;
      transformation;
      verbose;
      quiet;
      save_vo;
      reverse_order;
      skipped_files;
      dependencies_action;
    }
  in
  Term.(
    const combine $ input_t $ output_t $ transformation_t $ verbose_t $ quiet_t
    $ save_vo_t $ reverse_order_t $ skip_t $ dependencies_action_t)

let main opts =
  match opts.transformation with
  | Help ->
      Printf.printf "Available transformations:\n";
      Printf.printf "%s\n%!" (help_to_string transformations_help);
      exit 0
  | _ -> (
      match transform_project opts with
      | Ok res -> exit 0
      | Error err ->
          prerr_endline (Error.to_string_hum err);
          exit 1)

let cmd =
  let doc = "Apply transformations to Coq projects or files." in
  Cmd.v (Cmd.info "rocq-ditto" ~doc) Term.(const main $ cli_options_t)

let () = exit (Cmd.eval cmd)
