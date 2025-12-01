open Fleche
open Ditto
open Ditto.Nary_tree
open Ditto.Diagnostic_utils

let sexp_of_syntax_node (x : Syntax_node.t) : Sexplib.Sexp.t =
  let open Sexplib in
  Sexp.(Atom (Syntax_node.repr x))

let sexp_of_proof_tree (x : Syntax_node.t nary_tree) =
  Nary_tree.sexp_of_nary_tree sexp_of_syntax_node x

let rec simplify sexp =
  let open Sexplib.Sexp in
  match sexp with
  | List [ x ] -> simplify x
  | List xs -> List (List.map simplify xs)
  | Atom _ as a -> a

let print_tree ?(prefix = "") sexp =
  let open Sexplib.Sexp in
  let rec aux prefix sexp =
    match sexp with
    | Atom s -> Printf.printf "%s%s\n" prefix s
    | List lst ->
        let len = List.length lst in
        List.iteri
          (fun i x ->
            let is_last = i = len - 1 in
            let branch = if is_last then "└── " else "├── " in
            let next_prefix =
              if is_last then prefix ^ "    " else prefix ^ "│   "
            in
            match x with
            | Atom s -> Printf.printf "%s%s%s\n" prefix branch s
            | List _ ->
                Printf.printf "%s%s()\n" prefix branch;
                aux next_prefix x)
          lst
  in
  aux prefix (simplify sexp)

let neat_compile ~io:_ ~token:_ ~(doc : Doc.t) =
  Random.self_init ();
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in

  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  let first_errors = List.filteri (fun i _ -> i < 5) errors in

  print_endline ("compiling " ^ uri_str ^ " ...");
  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stop);
      print_diagnostics first_errors
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics first_errors
  | Doc.Completion.Yes _ -> (
      if List.length errors != 0 then print_diagnostics first_errors
      else
        let ( let* ) = Result.bind in

        let parsed_document = Rocq_document.parse_document doc in

        let final_res =
          let* proofs = Rocq_document.get_proofs parsed_document in

          let steps =
            List.fold_left
              (fun step_acc proof ->
                let steps =
                  Transformations.admit_proof parsed_document proof
                  |> Result.get_ok
                in
                steps @ step_acc)
              [] proofs
          in
          let* res =
            Rocq_document.apply_transformations_steps steps parsed_document
          in

          let* proofs = Rocq_document.get_proofs res in
          List.iter
            (fun (x : Proof.t) ->
              print_endline (Syntax_node.repr x.proposition))
            proofs;
          let proof_trees =
            List.map (Runner.treeify_proof res) proofs |> List.map Result.get_ok
          in

          let remove_random_tactics_steps =
            List.fold_left
              (fun step_acc tree ->
                let proof_of_tree =
                  Runner.tree_to_proof tree |> Result.get_ok
                in
                let step =
                  Transformations.remove_random_step res proof_of_tree
                  |> Result.get_ok |> List.hd
                in
                step :: step_acc)
              [] proof_trees
            |> List.rev
          in

          let* res =
            Rocq_document.apply_transformations_steps
              remove_random_tactics_steps res
          in

          let transformed_trees =
            List.map2
              (fun tree step ->
                Proof_tree.apply_transformation_step step tree |> Result.get_ok)
              proof_trees remove_random_tactics_steps
          in

          let _, res =
            List.fold_left
              (fun (step_acc, doc_acc) tree ->
                let steps = Transformations.simple_proof_repair doc_acc tree in
                match steps with
                | Ok steps ->
                    let new_doc =
                      Rocq_document.apply_transformations_steps steps doc_acc
                      |> Result.get_ok
                    in
                    (steps :: step_acc, new_doc)
                | Error err ->
                    print_endline (Error.to_string_hum err);
                    (step_acc, doc_acc))
              ([], res) transformed_trees
          in

          Ok res
        in

        match final_res with
        | Ok res ->
            let filename = Filename.remove_extension uri_str ^ "_bis.v" in
            print_endline
              ("All transformations applied, writing to file" ^ filename);

            let out = open_out filename in
            Result.fold
              ~ok:
                (print_endline "ok";
                 output_string out)
              ~error:(fun e ->
                print_endline "Error:";
                print_endline (Error.to_string_hum e))
              (Rocq_document.dump_to_string res)
        | Error err ->
            print_endline "In error case";
            print_endline (Error.to_string_hum err))

let main () = Theory.Register.Completed.add neat_compile
let () = main ()
