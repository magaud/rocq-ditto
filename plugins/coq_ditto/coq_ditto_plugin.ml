open Ditto_cli_lib.Cli
open Fleche
open Ditto
open Ditto.Proof

type scoped_function =
  | ProofScope of
      (Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result)
  | DocScope of (Rocq_document.t -> (transformation_step list, Error.t) result)

let wrap_to_treeify (doc : Rocq_document.t) (x : Proof.t) :
    (Syntax_node.t Nary_tree.nary_tree, Error.t) result =
  Runner.treeify_proof doc x

let transformation_kind_to_scoped_function (kind : transformation_kind) :
    scoped_function =
  let ( let* ) = Result.bind in
  match kind with
  | Help -> DocScope (fun _ -> Ok [])
  | ExplicitFreshVariables ->
      ProofScope Transformations.explicit_fresh_variables
  | TurnIntoOneliner ->
      ProofScope
        (fun doc x ->
          let* proof_tree = wrap_to_treeify doc x in
          Transformations.turn_into_oneliner doc proof_tree)
  | ReplaceAutoWithSteps -> ProofScope Transformations.replace_auto_with_steps
  | CompressIntro -> ProofScope Transformations.compress_intro
  | FlattenGoalSelectors -> ProofScope Transformations.flatten_goal_selectors
  | ConstructivizeGeocoq -> DocScope Constructivisation.constructivize_doc
  | RocqToLean -> DocScope Rocq_to_lean.rocq_to_lean
  | IdTransformation -> ProofScope Transformations.id_transform

let local_apply_doc_transformation (doc_acc : Rocq_document.t)
    (trans : Rocq_document.t -> (transformation_step list, Error.t) result)
    (transformation_kind : transformation_kind) (verbose : bool) (quiet : bool)
    : (Rocq_document.t, Error.t) result =
  let transformation_steps = trans doc_acc in
  match transformation_steps with
  | Ok steps ->
      List.fold_left
        (fun doc_acc_err step ->
          match doc_acc_err with
          | Ok doc -> Rocq_document.apply_transformation_step step doc
          | Error err -> Error err)
        (Ok doc_acc) steps
  | Error err -> Error err

let print_current_running (proof_count : int) (proof_total : int)
    (proof_name : string) (transformation_kind : transformation_kind) quiet
    verbose =
  if verbose then
    Printf.printf "Running transformation %s on %-20s (%d/%d)%!\n%!"
      (transformation_kind_to_string transformation_kind)
      proof_name (proof_count + 1) proof_total
  else if not quiet then
    Printf.printf "\027[2K\rRunning transformation %s on %-20s(%d/%d)%!"
      (transformation_kind_to_string transformation_kind)
      proof_name (proof_count + 1) proof_total
  else ()

let apply_steps
    (transformation_steps : (transformation_step list, Error.t) result)
    (curr_doc : Rocq_document.t) (proof_count : int) (proof : 'a) =
  match transformation_steps with
  | Ok steps ->
      ( List.fold_left
          (fun doc_acc_err step ->
            match doc_acc_err with
            | Ok doc -> Rocq_document.apply_transformation_step step doc
            | Error err -> Error err)
          (Ok curr_doc) steps,
        proof_count + 1,
        curr_doc,
        Some proof )
  | Error err -> (Error err, proof_count, curr_doc, Some proof)

let display_transformation_error (prev_proof : Proof.t option)
    (transformation_kind : transformation_kind) (err : Error.t) =
  let prev_proof_name =
    match prev_proof with
    | Some prev_proof ->
        Option.default "anonymous" (Proof.get_proof_name prev_proof)
    | None -> "None"
  in
  let transformation_name = transformation_kind_to_string transformation_kind in

  Printf.eprintf
    "Error when running the transformation %s on %s, canceling it\nError: %s%!"
    transformation_name prev_proof_name (Error.to_string_hum err)

let local_apply_proof_transformation (doc_acc : Rocq_document.t)
    (transformation :
      Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result)
    (transformation_kind : transformation_kind) (proof_list : Proof.t list)
    (verbose : bool) (quiet : bool) : Rocq_document.t =
  let proof_total = List.length proof_list in
  let first_proof = List.nth_opt proof_list 0 in
  let token = Coq.Limits.Token.create () in
  let res, _, prev_doc, prev_proof =
    List.fold_left
      (fun (doc_acc_bis, proof_count, prev_doc, (prev_proof : Proof.t option))
           proof ->
        let curr_doc =
          match doc_acc_bis with
          | Ok curr_doc -> curr_doc
          | Error err ->
              display_transformation_error prev_proof transformation_kind err;
              prev_doc
        in

        let status_before =
          Runner.get_init_state curr_doc proof.proposition token
        in
        let proof_name =
          Option.default "anonymous" (Proof.get_proof_name proof)
        in
        print_current_running proof_count proof_total proof_name
          transformation_kind quiet verbose;
        match status_before with
        | Ok _ ->
            let transformation_steps = transformation curr_doc proof in
            apply_steps transformation_steps curr_doc proof_count proof
        | Error _ ->
            let prev_proof_name =
              Option.map (fun p -> Proof.get_proof_name p) prev_proof
              |> Option.flatten
              |> Option.default "No previous proof ? This might be a bug\n"
            in
            Printf.printf
              "Invalid state after transforming proof %s, canceling it \n"
              prev_proof_name;
            let transformation_steps = transformation prev_doc proof in
            apply_steps transformation_steps prev_doc proof_count proof)
      (Ok doc_acc, 0, doc_acc, first_proof)
      proof_list
  in
  match res with
  | Ok res -> res
  | Error err ->
      display_transformation_error prev_proof transformation_kind err;
      doc_acc

let print_info (filename : string) (verbose : bool) : unit =
  Printf.printf "\nAll transformations applied, writing to file %s\n%!" filename;

  if verbose then (
    let stats = Stats.Global.dump () in
    Printf.printf "rocq-ditto stats: %s\n" (Stats.Global.to_string stats);
    Printf.printf "rocq-ditto %s\n" (Memo.GlobalCacheStats.stats ()))
  else ()

let ditto_plugin ~io:_ ~(token : Coq.Limits.Token.t) ~(doc : Doc.t) :
    (unit, Error.t) result =
  let ( let* ) = Result.bind in

  let verbose = Option.default "false" (Sys.getenv_opt "DEBUG_LEVEL") in

  let verbose = Option.default false (bool_of_string_opt verbose) in

  let quiet =
    Option.default "false" (Sys.getenv_opt "QUIET")
    |> bool_of_string_opt |> Option.default false
  in

  let out = Format.std_formatter in
  let reporter =
    Logs_fmt.reporter ~pp_header:pp_header_no_app ~app:out ~dst:out ()
  in
  Logs.set_reporter reporter;

  if verbose then Logs.set_level (Some Logs.Debug)
  else Logs.set_level (Some Logs.Info);

  Printexc.record_backtrace true;
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  let max_errors = 5 in
  let limited_errors = List.filteri (fun i _ -> i < max_errors) errors in

  let total_files =
    Sys.getenv_opt "TOTAL_FILE_COUNT"
    |> Option.map int_of_string_opt
    |> Option.flatten
  in

  let current_file_count =
    Sys.getenv_opt "CURRENT_FILE_COUNT"
    |> Option.map int_of_string_opt
    |> Option.flatten
  in
  let _ =
    match (current_file_count, total_files) with
    | Some curr_count, Some total_files ->
        Printf.printf
          "Running rocq-ditto on %s (file %d/%d in the project) \n%!" uri_str
          curr_count total_files
    | _, _ -> Printf.printf "running rocq-ditto on %s\n%!" uri_str
  in

  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      Error.format_to_or_error
        "parsing stopped at %s\n\
         %s\n\
         NOTE: errors after the first might be due to the first error."
        (Lang.Range.to_string range_stop)
        (String.concat "\n"
           (List.map Diagnostic_utils.diagnostic_to_string limited_errors))
  | Doc.Completion.Failed range_failed ->
      Error.format_to_or_error
        "parsing failed at %s\n\
         %s\n\
         NOTE: errors after the first might be due to the first error."
        (Lang.Range.to_string range_failed)
        (String.concat "\n"
           (List.map Diagnostic_utils.diagnostic_to_string limited_errors))
  | Doc.Completion.Yes _ -> (
      if errors <> [] then
        Error.format_to_or_error
          "Document was parsed with errors:\n\
           %s\n\
           NOTE: errors after the first might be due to the first error."
          (String.concat "\n"
             (List.map Diagnostic_utils.diagnostic_to_string limited_errors))
      else
        let transformations_steps =
          Sys.getenv_opt "DITTO_TRANSFORMATION"
          |> Option.map (String.split_on_char ',')
          |> Option.map (List.map arg_to_transformation_kind)
        in

        let reverse_order =
          Option.default false
            (Sys.getenv_opt "REVERSE_ORDER"
            |> Option.map bool_of_string_opt
            |> Option.flatten)
        in

        match transformations_steps with
        | None ->
            Error.string_to_or_error
              "Please specify the wanted transformation using the environment \
               variable: DITTO_TRANSFORMATION\n\
               If you want help about the different transformation, specify \
               DITTO_TRANSFORMATION=HELP"
        | Some steps when List.exists Result.is_error steps ->
            let not_recognized =
              String.concat "\n"
                (List.map
                   (fun x -> Error.to_string_hum (Result.get_error x))
                   ((List.filter Result.is_error) steps))
            in
            Error.format_to_or_error
              "Transformations not recognized:\n\
               %s\n\
               Recognized transformations: %s"
              not_recognized
              (String.concat "\n" transformations_list)
        | Some steps when List.mem (Ok Help) steps ->
            Printf.printf "%s\n" (help_to_string transformations_help);
            Ok ()
        | Some steps -> (
            let transformations_steps = List.map Result.get_ok steps in
            let parsed_document = Rocq_document.parse_document doc in
            let scoped_transformations :
                (transformation_kind * scoped_function) list =
              List.map
                (fun x -> (x, transformation_kind_to_scoped_function x))
                transformations_steps
            in

            let res =
              List.fold_left
                (fun (doc_acc : (Rocq_document.t, Error.t) result)
                     (transformation_kind, transformation) ->
                  match (doc_acc, transformation) with
                  | Ok doc_acc, scoped_trans -> (
                      match scoped_trans with
                      | ProofScope trans ->
                          Printf.printf "applying transformation : %s\n"
                            (transformation_kind_to_string transformation_kind);

                          let* proof_list =
                            if reverse_order then
                              Result.map List.rev
                                (Rocq_document.get_proofs doc_acc)
                            else Rocq_document.get_proofs doc_acc
                          in

                          Ok
                            (local_apply_proof_transformation doc_acc trans
                               transformation_kind proof_list verbose quiet)
                      | DocScope trans ->
                          local_apply_doc_transformation doc_acc trans
                            transformation_kind verbose quiet)
                  | Error err, _ -> Error err)
                (Ok parsed_document) scoped_transformations
            in

            let filename =
              Option.default
                (Filename.remove_extension uri_str ^ "_bis.v")
                (Sys.getenv_opt "OUTPUT_FILENAME")
            in

            let save_vo =
              Option.default false
                (Sys.getenv_opt "SAVE_VO"
                |> Option.map bool_of_string_opt
                |> Option.flatten)
            in

            match (res, save_vo) with
            | Ok res, false ->
                print_info filename verbose;
                let out = open_out filename in

                let* doc_repr = Rocq_document.dump_to_string res in

                output_string out doc_repr;
                flush_all ();
                Ok ()
            | Ok res, true ->
                print_info filename verbose;

                let out = open_out filename in
                let* doc_repr = Rocq_document.dump_to_string res in
                output_string out doc_repr;
                Printf.printf "Saving vo: ";
                let uri =
                  Lang.LUri.of_string filename
                  |> Lang.LUri.File.of_uri |> Result.get_ok
                in

                let ldir = Coq.Workspace.dirpath_of_uri ~uri:doc.uri in
                let in_file = Lang.LUri.File.to_string_file uri in
                let* state =
                  match List_utils.last res.elements with
                  | Some last ->
                      let* st = Runner.get_init_state res last token in
                      Runner.run_node token st last
                  | None -> Ok res.initial_state
                in

                let res =
                  Coq.Save.save_vo ~token ~st:state ~ldir ~in_file
                  |> Runner.protect_to_result
                in
                Result.iter
                  (fun _ -> Printf.printf "vo saved successfully\n")
                  res;
                res
            | Error err, _ ->
                Printf.eprintf "%s\n%!" (Error.to_string_hum err);
                exit 1))

let ditto_plugin_hook ~io ~token ~(doc : Doc.t) : unit =
  match ditto_plugin ~io ~token ~doc with
  | Ok _ -> exit 0
  | Error err ->
      prerr_endline (Error.to_string_hum err);
      exit 1

let main () = Theory.Register.Completed.add ditto_plugin_hook
let () = main ()
