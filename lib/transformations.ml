open Nary_tree
open Proof
open Syntax_node
open Runner
open Sexplib.Conv
open Re

(* let add_bullets (doc : Rocq_document.t) (proof_tree : Syntax_node.t nary_tree) : *)
(*     (transformation_step list, Error.t) result = *)
(*   let token = Coq.Limits.Token.create () in *)
(*   let rec aux state acc depth tree = *)
(*     match tree with *)
(*     | Node (x, children) -> *)
(*        let new_state = Result.get_ok (Runner.run_node token state x) in *)
(*        let new_acc = if  List.length children > 0 then *)

(*         List.fold_left *)
(*           (fun (state_acc, res_acc) child -> aux state_acc res_acc 0 child) *)
(*           (new_state, acc) children *)
(*   in *)
(*   match get_init_state doc (root proof_tree) token with *)
(*   | Ok state -> *)
(*       let a = aux state [] 0 proof_tree in *)
(*       Ok [] *)
(*   | Error _ -> Error.string_to_or_error "Unable to retrieve initial state" *)

let simple_proof_repair (doc : Rocq_document.t)
    (proof_tree : Syntax_node.t nary_tree) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  let token = Coq.Limits.Token.create () in
  let admit_creator =
   fun node -> Syntax_node.syntax_node_of_string "admit." node.range.start
  in
  let module SyntaxNodeSet = Set.Make (struct
    type t = Syntax_node.t

    let compare = Syntax_node.compare_nodes
  end) in
  let ignore_set = SyntaxNodeSet.empty in

  match get_init_state doc (root proof_tree) token with
  | Ok state ->
      let* _, steps_acc, ignore_acc, _ =
        Nary_tree.depth_first_fold_with_children_as_trees
          (fun acc node children ->
            match acc with
            | Ok (state_acc, steps_acc, ignore_acc, prev_goal_count) -> (
                if SyntaxNodeSet.mem node ignore_acc then
                  Ok (state_acc, steps_acc, ignore_acc, prev_goal_count)
                else
                  let state_res = Runner.run_node token state_acc node in
                  match state_res with
                  | Ok new_state ->
                      let num_goals = Runner.count_goals token new_state in
                      if
                        List.length children = 0
                        && (not
                              (Syntax_node.is_syntax_node_proof_intro_or_end
                                 node))
                        && prev_goal_count <= num_goals
                      then
                        let* admit_node = admit_creator node in
                        let* admit_state =
                          Runner.run_node token new_state admit_node
                        in
                        Ok (admit_state, steps_acc, ignore_acc, prev_goal_count)
                      else Ok (new_state, steps_acc, ignore_acc, num_goals)
                  | Error _ ->
                      let childs =
                        List.concat (List.map Nary_tree.flatten children)
                        |> List.filter (fun x ->
                            not (is_syntax_node_proof_intro_or_end x))
                      in

                      let ignore_acc =
                        SyntaxNodeSet.union ignore_acc
                          (SyntaxNodeSet.of_list childs)
                      in
                      let* admit_node = admit_creator node in
                      let* admit_state =
                        Runner.run_node token state_acc admit_node
                        |> Result.map_error Error.tag_with_debug_infos
                      in
                      let num_goals = Runner.count_goals token admit_state in

                      Ok
                        ( admit_state,
                          Replace (node.id, admit_node) :: steps_acc,
                          ignore_acc,
                          num_goals ))
            | Error err -> Error err)
          (Ok (state, [], ignore_set, 1))
          proof_tree
      in

      let removed_steps =
        SyntaxNodeSet.elements ignore_acc |> List.map (fun x -> Remove x.id)
      in
      Ok (steps_acc @ removed_steps)
  | _ -> Error.string_to_or_error "Unable to retrieve initial state"

let admit_branch_at_error (doc : Rocq_document.t)
    (proof_tree : Syntax_node.t nary_tree) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  let token = Coq.Limits.Token.create () in
  let admit_creator =
   fun node ->
    Result.get_ok (Syntax_node.syntax_node_of_string "admit" node.range.start)
  in
  let rec aux state_acc tree steps_acc =
    match tree with
    | Node (x, children) -> (
        if is_syntax_node_proof_intro_or_end x then
          let state = Result.get_ok (Runner.run_node token state_acc x) in
          List.fold_left
            (fun (state, acc) child ->
              let new_state, new_acc = aux state child acc in
              (new_state, new_acc))
            (state, steps_acc) children
        else
          let state = Runner.run_node token state_acc x in

          (* Fold over the children using the updated state and accumulator *)
          match state with
          | Ok state ->
              List.fold_left
                (fun (state, acc) child ->
                  let new_state, new_acc = aux state child acc in
                  (new_state, new_acc))
                (state, steps_acc) children
          | Error _ ->
              let admit_node = admit_creator x in
              let cut_node_state =
                Runner.run_node token state_acc admit_node |> Result.get_ok
              in

              let cut_node_goals_count =
                Runner.count_goals token cut_node_state
              in
              let children_nodes =
                List.concat (List.map Nary_tree.flatten children)
              in

              let next_state =
                List.fold_left
                  (fun state_acc node ->
                    if node_can_close_proof node then state_acc
                    else Result.get_ok (Runner.run_node token state_acc node))
                  cut_node_state children_nodes
              in

              let next_state_goals = Runner.count_goals token next_state in

              if cut_node_goals_count = next_state_goals then
                let children_nodes =
                  List.concat (List.map Nary_tree.flatten children)
                in

                let remove_steps =
                  List.filter_map
                    (fun node ->
                      if node_can_open_proof node || node_can_close_proof node
                      then None
                      else Some (Remove node.id))
                    (x :: children_nodes)
                in
                (cut_node_state, steps_acc @ (Add admit_node :: remove_steps))
              else
                List.fold_left
                  (fun (state, acc) child ->
                    let new_state, new_acc = aux state child acc in
                    (new_state, new_acc))
                  (cut_node_state, steps_acc)
                  children)
  in
  let* cur_proof = Runner.tree_to_proof proof_tree in
  match get_init_state doc cur_proof.proposition token with
  | Ok state ->
      let _, steps = aux state proof_tree [] in
      Ok steps
  | _ -> Error.string_to_or_error "Unable to retrieve initial state"

let cut_replace_branch (cut_tactic : string) (doc : Rocq_document.t)
    (proof_tree : Syntax_node.t nary_tree) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  let token = Coq.Limits.Token.create () in
  let node_creator =
   fun node ->
    Result.get_ok
      (Syntax_node.syntax_node_of_string cut_tactic node.range.start)
  in

  let rec aux state_acc tree steps_acc =
    match tree with
    | Node (x, children) -> (
        let state = Result.get_ok (Runner.run_node token state_acc x) in
        if is_syntax_node_proof_intro_or_end x then
          List.fold_left
            (fun (state, acc) child ->
              let new_state, new_acc = aux state child acc in
              (new_state, new_acc))
            (state, steps_acc) children
        else
          let cut_node = node_creator x in
          let cut_node_state_res = Runner.run_node token state_acc cut_node in
          (* Fold over the children using the updated state and accumulator *)
          match cut_node_state_res with
          | Ok cut_node_state ->
              let cut_node_goals_count =
                Runner.count_goals token cut_node_state
              in
              let children_nodes =
                List.concat (List.map Nary_tree.flatten children)
              in

              let next_state =
                List.fold_left
                  (fun state_acc node ->
                    if node_can_close_proof node then state_acc
                    else Result.get_ok (Runner.run_node token state_acc node))
                  state children_nodes
              in

              let next_state_goals = Runner.count_goals token next_state in

              if cut_node_goals_count = next_state_goals then
                let children_nodes =
                  List.concat (List.map Nary_tree.flatten children)
                in

                let remove_steps =
                  List.filter_map
                    (fun node ->
                      if node_can_open_proof node || node_can_close_proof node
                      then None
                      else Some (Remove node.id))
                    (x :: children_nodes)
                in
                (cut_node_state, steps_acc @ (Add cut_node :: remove_steps))
              else
                List.fold_left
                  (fun (state, acc) child ->
                    let new_state, new_acc = aux state child acc in
                    (new_state, new_acc))
                  (state, steps_acc) children
          | Error _ ->
              List.fold_left
                (fun (state, acc) child ->
                  let new_state, new_acc = aux state child acc in
                  (new_state, new_acc))
                (state, steps_acc) children)
  in
  let* cur_proof = Runner.tree_to_proof proof_tree in
  match get_init_state doc cur_proof.proposition token with
  | Ok state ->
      let _, steps = aux state proof_tree [] in
      Ok steps
  | _ -> Error.string_to_or_error "Unable to retrieve initial state"

let fold_replace_assumption_with_apply (doc : Rocq_document.t)
    (proof_tree : Syntax_node.t nary_tree) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  let token = Coq.Limits.Token.create () in
  let res =
    Runner.depth_first_fold_with_state doc token
      (fun state acc node ->
        let* state_node = Runner.run_node token state node in
        if
          String.starts_with ~prefix:"assumption" (repr node)
          && not (String.contains (repr node) ';')
        then
          let goal_count_after_assumption =
            Runner.count_goals token state_node
          in

          let curr_goal_err = Runner.get_current_goal token state in
          match curr_goal_err with
          | Ok curr_goal ->
              let hypothesis_apply_repr =
                List.map
                  (fun name -> "apply " ^ name ^ ".")
                  (Runner.get_hypothesis_names curr_goal)
              in
              let apply_nodes =
                List.map
                  (fun repr ->
                    Result.get_ok
                      (Syntax_node.syntax_node_of_string repr node.range.start))
                  hypothesis_apply_repr
              in

              let apply_states =
                List.filter_map
                  (fun node ->
                    match Runner.run_node token state node with
                    | Ok state_uw -> Some (node, state_uw)
                    | Error _ -> None)
                  apply_nodes
              in

              let replacement =
                List.find
                  (fun tuple_n_r ->
                    Runner.count_goals token (snd tuple_n_r)
                    = goal_count_after_assumption)
                  apply_states
              in
              let new_node = fst replacement in

              Ok (state_node, Replace (node.id, new_node) :: acc)
          | Error _ -> Ok (state_node, acc)
        else Ok (state_node, acc))
      [] proof_tree
  in
  res

let id_transform (_ : Rocq_document.t) (_ : proof) :
    (transformation_step list, Error.t) result =
  Ok []

(* let buggy_transformation (_ : Rocq_document.t) (_ : proof) : (transformation_step list, Error.t) result  *)

let admit_proof (_ : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  let proof_close_node =
    List.find Syntax_node.is_syntax_node_proof_end proof.proof_steps
  in
  let* admitted_node =
    syntax_node_of_string "Admitted." proof_close_node.range.start
  in
  Ok [ Replace (proof_close_node.id, admitted_node) ]

let int_in_range ~min ~max =
  if min > max then invalid_arg "int_in_range";
  min + Random.int (max - min + 1)

let remove_random_step (_ : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let num_steps = List.length proof.proof_steps in
  if num_steps <= 2 then Ok []
  else
    let rand_num = int_in_range ~min:1 ~max:(num_steps - 2) in
    let rand_node = List.nth proof.proof_steps rand_num in
    let incorrect_node =
      Syntax_node.syntax_node_of_string "fail." rand_node.range.start
      |> Result.get_ok
    in
    Ok [ Replace (rand_node.id, incorrect_node) ]

let admit_and_comment_proof_steps (_ : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let remove_all_steps =
    List.map (fun step -> Remove step.id) proof.proof_steps
  in
  let first_proof_node = List.hd proof.proof_steps in

  let comment_content =
    List.fold_left
      (fun str_acc step -> str_acc ^ repr step ^ "\n")
      "(* "
      (List_utils.take
         (max 0 (List.length proof.proof_steps - 1))
         proof.proof_steps)
    ^ " *)"
  in

  let comment_node =
    Result.get_ok
      (Syntax_node.comment_syntax_node_of_string comment_content
         first_proof_node.range.start)
  in

  let admitted_start =
    shift_point 1 (-comment_node.range.end_.character) comment_node.range.end_
  in

  let admitted_node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Admitted." admitted_start)
  in
  Ok
    (remove_all_steps
    @ [
        Attach (comment_node, LineAfter, proof.proposition.id);
        Attach (admitted_node, LineAfter, comment_node.id);
      ])

let remove_unecessary_steps (doc : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token_reduce = Coq.Limits.Token.create () in

  let rec aux (state : Coq.State.t)
      (acc : (transformation_step list, Error.t) result)
      (nodes : Syntax_node.t list) : (transformation_step list, Error.t) result
      =
    let ( let* ) = Result.bind in
    match nodes with
    | [] -> acc
    | x :: tail -> (
        if
          ((not (is_syntax_node_proof_intro_or_end x))
          && not (is_syntax_node_bullet x))
          && Runner.can_reduce_to_zero_goals state tail
        then
          let* acc = acc in
          aux state (Ok (Remove x.id :: acc)) tail
        else
          match Runner.run_node token_reduce state x with
          | Ok state_node -> aux state_node acc tail
          | Error err -> Error err)
  in
  match get_init_state doc proof.proposition token_reduce with
  | Ok state -> aux state (Ok []) (proof_nodes proof)
  | _ -> Error.string_to_or_error "Unable to retrieve initial state"

let flatten_goal_selectors (doc : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let ( let* ) = Result.bind in

  let reified_goal_hashtbl = Hashtbl.create 50 in

  let* steps =
    Runner.fold_proof_with_state doc token
      (fun (state : Coq.State.t) step_acc node ->
        let goals = Runner.reified_goals_at_state token state in
        let* new_state = Runner.run_node token state node in
        let node_without_selector = Syntax_node.drop_goal_selector node in
        let* new_step_acc =
          match Syntax_node.get_node_goal_selector_opt node with
          | Some goal_selector ->
              Logs.debug (fun m -> m "found a goal selector: %s" (repr node));

              let new_goals = Runner.reified_goals_at_state token new_state in
              (*Otherwise we can never get them later *)
              let* selected_goals =
                Goal_select_view.apply_goal_selector_view goal_selector
                  new_goals
              in

              Logs.debug (fun m -> m "selected goals:");
              List.iter
                (fun x -> Logs.debug (fun m -> m "%a" Reified_goal.pp x))
                selected_goals;
              Logs.debug (fun m -> m "-------------");

              let _ =
                List.iter
                  (fun goal ->
                    Hashtbl.add reified_goal_hashtbl goal node_without_selector)
                  selected_goals
              in

              Ok (Remove node.id :: step_acc)
          | None -> Ok step_acc
        in
        match List.nth_opt goals 0 with
        | Some goal ->
            let all_found = Hashtbl.find_all reified_goal_hashtbl goal in
            let _ =
              if List.length all_found > 0 then
                Logs.debug (fun m ->
                    m "attaching to %s at %s " (repr node)
                      (Code_range.to_string node.range))
              else ()
            in
            let attach_steps =
              List.map (fun x -> Attach (x, LineBefore, node.id)) all_found
            in
            List.iter
              (fun _ -> Hashtbl.remove reified_goal_hashtbl goal)
              all_found;

            Ok (new_state, attach_steps @ new_step_acc)
        | None -> Ok (new_state, new_step_acc))
      [] proof
  in

  List.iter
    (fun step ->
      pp_transformation_step Format.std_formatter step;
      Format.pp_print_newline Format.std_formatter ())
    steps;
  Ok (List.rev steps)

let compress_intro (doc : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let rec aux state (acc_intro, acc_steps) nodes =
    match nodes with
    | [] -> acc_steps
    | x :: tail ->
        let state_node = Result.get_ok (Runner.run_node token state x) in
        if
          String.starts_with ~prefix:"intro." (repr x)
          && not (String.contains (repr x) ';')
        then aux state_node (x :: acc_intro, acc_steps) tail
        else if List.length acc_intro > 0 then
          let steps =
            List.mapi
              (fun i node ->
                if i = 0 then
                  let intros_node =
                    Result.get_ok
                      (Syntax_node.syntax_node_of_string "intros."
                         node.range.start)
                  in
                  Replace (node.id, intros_node)
                else Remove node.id)
              acc_intro
          in
          aux state_node ([], acc_steps @ steps) tail
        else aux state_node ([], acc_steps) tail
  in

  match get_init_state doc proof.proposition token with
  | Ok state ->
      let steps = aux state ([], []) (proof_nodes proof) in
      Ok steps
  | _ -> Error.string_to_or_error "Unable to retrieve initial state"

let fold_add_time_taken (doc : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  match
    Runner.fold_proof_with_state doc token
      (fun state acc node ->
        let t1 = Unix.gettimeofday () in
        let new_state_run = Runner.run_node token state node in
        let t2 = Unix.gettimeofday () in
        let time_to_run = t2 -. t1 in
        let new_state = Result.get_ok new_state_run in
        if time_to_run > 0.0 then
          let comment_content =
            "Time spent on this step: " ^ string_of_float time_to_run
          in

          let nodes_on_same_line =
            List.filter
              (fun x -> x != node && x.range.start.line = node.range.start.line)
              (proof_nodes proof)
          in
          let furthest_char_node =
            List.fold_left
              (fun max_char_node elem ->
                if
                  elem.range.start.character
                  > max_char_node.range.start.character
                then elem
                else max_char_node)
              node nodes_on_same_line
          in

          let comment_start_point =
            shift_point 0 5 furthest_char_node.range.end_
          in
          match
            Syntax_node.comment_syntax_node_of_string comment_content
              comment_start_point
          with
          | Ok comment_node -> Ok (new_state, Add comment_node :: acc)
          | Error err -> Error err
        else Ok (new_state, acc))
      [] proof
  with
  | Ok acc -> Ok acc
  | Error err -> Error err

let replace_auto_with_steps (doc : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let ( let* ) = Result.bind in
  let re =
    Re.Perl.compile_pat "auto(.*?)\\." ~opts:[ `Multiline; `Dotall; `Ungreedy ]
  in

  let re_in_remove = Str.regexp " (in.*)\\." in

  let extract text =
    match Re.exec_opt re text with
    | Some group -> Re.Group.get group 1
    | None -> "No match"
  in

  let count_leading_spaces s =
    let re = Str.regexp "^ *" in
    if Str.string_match re s 0 then String.length (Str.matched_string s) else 0
  in

  let rec pop_until_split stack =
    match stack with
    | [] -> []
    | (_, _, _, num_children, _, _) :: tail ->
        if num_children <= 1 then pop_until_split tail else stack
  in

  let rec pop_until_prev_depth stack target_depth =
    match stack with
    | [] -> []
    | (_, _, depth, _, _, reduced_goals) :: tail ->
        if depth >= target_depth && not reduced_goals then
          pop_until_prev_depth tail target_depth
        else stack
  in

  let res =
    Runner.fold_proof_with_state doc token
      (fun state acc node ->
        if Option.is_empty node.ast then Ok (state, acc)
        else
          let* new_state = Runner.run_node token state node in

          if
            String.starts_with ~prefix:"auto" (repr node)
            && not (String.contains (repr node) ';')
          then (
            let node_args = extract (repr node) in

            let info_auto = "info_auto" ^ node_args ^ "." in
            let* info_auto_node =
              Syntax_node.syntax_node_of_string info_auto node.range.start
            in

            let* _, diagnostics =
              Runner.run_node_with_diagnostics token state info_auto_node
              |> Result.map_error fst
            in

            let tactic_diagnostic_repr =
              Pp.string_of_ppcmds (List.nth diagnostics 1).message
            in

            let auto_tactics =
              String.split_on_char '\n' tactic_diagnostic_repr
            in
            let intros =
              List_utils.take_while (fun tac -> tac = "intro.") auto_tactics
            in
            let intros_nodes =
              List.map
                (fun repr ->
                  Result.get_ok
                    (Syntax_node.syntax_node_of_string repr node.range.start))
                intros
            in

            let after_intros =
              List_utils.drop_while (fun tac -> tac = "intro.") auto_tactics
            in
            let rest_cleaned =
              List.map
                (fun repr -> Str.global_replace re_in_remove "." repr)
                after_intros
            in

            let depth_tuples =
              List.map (fun tac -> (count_leading_spaces tac, tac)) rest_cleaned
            in

            let depth_tuples_nodes_rev =
              List.rev_map
                (fun (depth, tac) ->
                  ( depth,
                    Result.get_ok
                      (Syntax_node.syntax_node_of_string tac node.range.start)
                  ))
                depth_tuples
            in

            let depth_tuple_nodes_rev_indexed =
              List.mapi
                (fun i (depth, node) -> (depth, node, i))
                depth_tuples_nodes_rev
            in

            let* default_node =
              Syntax_node.syntax_node_of_string "idtac." node.range.start
            in

            let default_node_tuple =
              (-1, default_node, List.length depth_tuples_nodes_rev)
            in

            let parents = Hashtbl.create (List.length depth_tuples_nodes_rev) in

            List.iteri
              (fun i (current_depth, current_node) ->
                let next_nodes =
                  List_utils.drop i depth_tuple_nodes_rev_indexed
                in

                let prev_node_tuple =
                  Option.default default_node_tuple
                    (List.find_opt
                       (fun (depth, _, _) -> depth < current_depth)
                       next_nodes)
                in
                let prev_node_depth, prev_node, prev_node_index =
                  prev_node_tuple
                in

                if current_depth > prev_node_depth then
                  Hashtbl.add parents
                    (prev_node_index, prev_node)
                    (i, current_node))
              depth_tuples_nodes_rev;

            let tree =
              Runner.proof_tree_from_parents
                (List.length depth_tuples_nodes_rev, default_node)
                parents
            in

            let tree_with_depths =
              Nary_tree.mapi
                (fun i node ->
                  let matching_tuple =
                    List.nth ((-1, "idtac") :: depth_tuples) i
                  in
                  (node, fst matching_tuple + 1))
                tree
            in
            let* before_state =
              List.fold_left
                (fun state_acc node ->
                  let* state_acc = state_acc in
                  match Runner.run_node token state_acc node with
                  | Ok new_state -> Ok new_state
                  | Error err -> Error err)
                (Ok state) intros_nodes
            in

            let auto_steps =
              Nary_tree.depth_first_fold_with_children
                (fun steps_stack (node, depth) children ->
                  let _, _, prev_depth, _, _, _ = List.hd steps_stack in
                  let steps_stack =
                    if prev_depth >= depth then
                      pop_until_prev_depth steps_stack depth
                    else steps_stack
                  in
                  let _, prev_state, _, _, prev_goal_count, _ =
                    List.hd steps_stack
                  in

                  let number_children = List.length children in
                  let cur_state =
                    Result.get_ok (Runner.run_node token prev_state node)
                  in

                  let goal_count = Runner.count_goals token cur_state in
                  if number_children = 0 then
                    if goal_count < prev_goal_count then
                      (node, cur_state, depth, number_children, goal_count, true)
                      :: steps_stack
                    else pop_until_split steps_stack
                  else
                    (node, cur_state, depth, number_children, goal_count, false)
                    :: steps_stack)
                [ (default_node, before_state, -1, 0, 0, false) ]
                tree_with_depths
            in

            let tactics =
              intros
              @ List.rev_map
                  (fun (node, _, _, _, _, _) -> String.trim (repr node))
                  auto_steps
            in
            let filtered_tactics =
              List.filter (fun repr -> repr != "idtac.") tactics
            in

            let tactic_nodes =
              List.mapi
                (fun i repr ->
                  Result.get_ok
                    (Syntax_node.syntax_node_of_string repr
                       (shift_point i 0 node.range.start)))
                filtered_tactics
            in
            let shifted_nodes =
              snd
                (List.fold_left_map
                   (fun acc node ->
                     let char_shift =
                       if acc != 0 then node.range.start.character else 0
                     in
                     (acc + char_shift + String.length (repr node) + 1, node))
                   0 tactic_nodes)
            in

            let add_steps = List.map (fun node -> Add node) shifted_nodes in

            Ok (new_state, add_steps @ (Remove node.id :: acc)))
          else Ok (new_state, acc))
      [] proof
  in
  res

let ( let* ) = Result.bind

let map_children f lst =
  let open Result in
  let rec aux acc = function
    | [] -> Ok (List.rev acc)
    | x :: xs ->
        let* v = f x in
        aux (v :: acc) xs
  in
  aux [] lst

let rec get_oneliner (suffix : Syntax_node.t option)
    (tree : Syntax_node.t nary_tree) :
    (Ltac_plugin.Tacexpr.raw_tactic_expr, Error.t) result =
  match tree with
  | Node (x, childrens) -> (
      let* new_x_raw_expr =
        if Syntax_node.is_syntax_node_ending_with_elipsis x then
          match suffix with
          | None ->
              Error.format_to_or_error
                "Error applying then between %s and None." (repr x)
          | Some s -> (
              match Syntax_node.apply_tac_then x s () with
              | Ok r ->
                  Ok (r |> Syntax_node.get_node_raw_tactic_expr |> Option.get)
              | Error _ ->
                  let suffix_repr = repr s in
                  Error.format_to_or_error
                    "Error applying then between %s and %s." (repr x)
                    suffix_repr)
        else
          Syntax_node.get_node_raw_tactic_expr x
          |> Option_utils.to_result
               ~none:
                 (Error.format_to_or_error
                    "%s isn't convertible to a raw_tactic_expr (It probably \
                     isn't Ltac)"
                    (repr x))
      in

      let last_children_opt, childrens_length =
        List_utils.last_and_len childrens
      in

      let childrens_length_without_proof_end =
        match last_children_opt with
        | Some (Node (last, _)) when is_syntax_node_proof_end last ->
            childrens_length - 1
        | _ -> childrens_length
      in

      let* mapped =
        if childrens_length_without_proof_end = 0 then Ok []
        else map_children (get_oneliner suffix) childrens
      in
      match mapped with
      | [] -> Ok new_x_raw_expr
      | [ single ] ->
          Ok (CAst.make (Ltac_plugin.Tacexpr.TacThen (new_x_raw_expr, single)))
      | _ ->
          Ok (CAst.make (Ltac_plugin.Tacexpr.TacThens (new_x_raw_expr, mapped)))
      )

let turn_into_oneliner (_ : Rocq_document.t)
    (proof_tree : Syntax_node.t nary_tree) :
    (transformation_step list, Error.t) result =
  let* proof = Runner.tree_to_proof proof_tree in

  let dummy_point : Code_point.t = { line = 0; character = 0 } in

  match Proof.get_proof_status proof with
  | None ->
      Error.string_to_or_error
        "Can't find the proof status of the proof: invalid proof"
  | Some (Proof.Aborted | Proof.Admitted) -> Ok []
  | Some Proof.Proved -> (
      let suffix_node =
        proof.proof_steps
        |> List.find_map Syntax_node.get_syntax_node_proof_with_tactic
        |> Option.map (fun x ->
            Syntax_node.syntax_node_of_string (x ^ ".") dummy_point
            |> Result.get_ok)
      in

      let cleaned_tree =
        Nary_tree.filter
          (fun node ->
            (not (is_syntax_node_command_allowed_in_proof node))
            && ((not (node_can_open_proof node))
               && not (node_can_close_proof node))
            && Option.has_some node.ast)
          proof_tree
      in

      match cleaned_tree with
      | None -> Ok []
      | Some cleaned_tree -> (
          let* one_liner_node_raw_expr =
            get_oneliner suffix_node cleaned_tree
          in

          let flattened = Nary_tree.flatten proof_tree in
          let rev_flattened = List.rev flattened in

          let remove_steps =
            List.filter_map
              (fun node ->
                if
                  node_can_open_proof node || node_can_close_proof node
                  || is_syntax_node_proof_command node
                then None
                else Some (Remove node.id))
              flattened
          in

          let* first_proof_node_idx =
            List_utils.find_index
              (fun x -> is_syntax_node_proof_command x || node_can_open_proof x)
              rev_flattened
            |> Option_utils.to_result
                 ~none:
                   (Error.format_to_or_error
                      "can't find a starting node to attach to.")
          in

          let first_proof_node = List.nth rev_flattened first_proof_node_idx in

          let* first_step_node =
            List.nth_opt rev_flattened (first_proof_node_idx - 1)
            (* the list is reverse so next is prev *)
            |> Option_utils.to_result
                 ~none:
                   (Error.format_to_or_error
                      "There should be a node after the Proof or proposition \
                       node in this case")
          in

          let* one_liner_node =
            Syntax_node.raw_tactic_expr_to_syntax_node one_liner_node_raw_expr
              first_step_node.range.start
          in

          let attach_position =
            if
              first_proof_node.range.end_.line
              = first_step_node.range.start.line
            then SameLine
            else LineAfter
          in

          match suffix_node with
          | Some suffix_node ->
              let* proof_node =
                Syntax_node.syntax_node_of_string "Proof."
                  suffix_node.range.start
              in
              Ok
                (remove_steps
                @ [
                    Replace (first_proof_node.id, proof_node);
                    (* Here, we are sure to have a Proof node in first_proof_node *)
                    Attach (one_liner_node, attach_position, proof_node.id);
                  ])
          | None ->
              Ok
                (remove_steps
                @ [
                    Attach (one_liner_node, attach_position, first_proof_node.id);
                  ])))

let constrexpr_to_string (x : Constrexpr.constr_expr) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = Ppconstr.pr_constr_expr env sigma x in
  Pp.string_of_ppcmds pp

let destruction_arg_to_string
    (x : Constrexpr.constr_expr Tactypes.with_bindings Tactics.destruction_arg)
    : string =
  let _, with_bindings = x in
  match with_bindings with
  | Tactics.ElimOnConstr constr ->
      let constr_expr, _ = constr in
      constrexpr_to_string constr_expr
  | Tactics.ElimOnIdent ident ->
      let id = ident.v in
      Names.Id.to_string id
  | Tactics.ElimOnAnonHyp _ -> "anonymous"

let is_syntax_node_intros_without_set_var (x : Syntax_node.t) : bool =
  match Syntax_node.get_node_raw_atomic_tactic_expr x with
  | Some (TacIntroPattern (_, intro_pattern)) -> (
      match intro_pattern with
      | [ { v; _ } ] -> (
          match v with Tactypes.IntroForthcoming false -> true | _ -> false)
      | _ -> false)
  | _ -> false

let is_syntax_node_assert_without_set_var (x : Syntax_node.t) : bool =
  match Syntax_node.get_node_raw_atomic_tactic_expr x with
  | Some (TacAssert (false, true, _, None, _)) -> true
  | _ -> false

let is_syntax_node_assert_by (x : Syntax_node.t) : bool =
  match Syntax_node.get_node_raw_atomic_tactic_expr x with
  | Some (TacAssert (false, true, Some (Some _), _, _)) -> true
  | _ -> false

let is_syntax_node_induction_without_set_var (x : Syntax_node.t) : bool =
  match Syntax_node.get_node_raw_atomic_tactic_expr x with
  | Some (TacInductionDestruct (true, false, (induction_clause_l, _))) ->
      List.exists
        (fun x ->
          let _, (_, locus_or_var_or_and_intro_pattern_opt), _ = x in
          Option.is_empty locus_or_var_or_and_intro_pattern_opt)
        induction_clause_l
  | _ -> false

let string_to_intro_pattern_naming_expr (x : string) :
    Namegen.intro_pattern_naming_expr option =
  let ( let* ) = Option.bind in
  let* name =
    try Some (Names.Id.of_string x) with CErrors.UserError _ -> None
  in
  Some (Namegen.IntroIdentifier name)

let string_to_intro_pattern_expr (x : string) :
    'constr Tactypes.intro_pattern_expr option =
  Option.map
    (fun a -> Tactypes.IntroNaming a)
    (string_to_intro_pattern_naming_expr x)

let list_to_str pp_elem l =
  let elems = List.map pp_elem l |> String.concat "; " in
  "[" ^ elems ^ "]"

let list_of_list_to_str pp_elem lsts =
  let inner = List.map (list_to_str pp_elem) lsts |> String.concat "; " in
  "[" ^ inner ^ "]"

let list_of_list_of_str_to_str lsts : string = list_of_list_to_str Fun.id lsts

let get_new_vars ?(keep : string list = [])
    (old_goals_vars : string list list option)
    (new_goals_vars : string list list option) : string list list option =
  match (old_goals_vars, new_goals_vars) with
  | Some old_goals_vars, Some new_goals_vars ->
      Some
        (List_utils.map2_pad
           ~pad1:(List.nth_opt old_goals_vars 0)
           (fun old_vars new_vars ->
             List.filter
               (fun x -> (not (List.mem x old_vars)) || List.mem x keep)
               new_vars)
           old_goals_vars new_goals_vars)
  | _ -> None

let explicit_fresh_variables (doc : Rocq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let ( let* ) = Result.bind in

  let rewrite_induction (x : Syntax_node.t)
      (old_goals_vars : string list list option)
      (new_goals_vars : string list list option) : Syntax_node.t option =
    let open Ltac_plugin.Tacexpr in
    match (old_goals_vars, new_goals_vars) with
    | Some old_goals_vars, Some new_goals_vars ->
        let raw_atomic_expr =
          Syntax_node.get_node_raw_atomic_tactic_expr x |> Option.get
        in
        let rflag, eflag, (induction_clause_l, with_bindings) =
          match raw_atomic_expr with
          | TacInductionDestruct
              (rflag, eflag, (induction_clause_l, with_bindings)) ->
              (rflag, eflag, (induction_clause_l, with_bindings))
          | _ -> assert false
        in

        (* Apply the same transformation to all clauses *)
        let new_induction_clause_l =
          List.map
            (fun ( destruction_arg,
                   (intro_pattern_naming_expr_opt, _),
                   clause_expr_opt ) ->
              let destruct_arg_str =
                destruction_arg_to_string destruction_arg
              in

              let new_or_and_intro_pattern =
                if List.length old_goals_vars = List.length new_goals_vars then
                  []
                else
                  let new_goals_vars =
                    List_utils.take
                      (List.length new_goals_vars - List.length old_goals_vars
                     + 1)
                      new_goals_vars
                  in
                  let new_vars =
                    get_new_vars ~keep:[ destruct_arg_str ]
                      (Some old_goals_vars) (Some new_goals_vars)
                    |> Option.get
                  in

                  let rec reorder other_vars induction_vars =
                    match other_vars with
                    | [] -> []
                    | x :: tl -> (
                        match
                          List.find_opt
                            (fun elem -> elem = "IH" ^ x)
                            induction_vars
                        with
                        | Some induction_hyp ->
                            x :: induction_hyp :: reorder tl induction_vars
                        | None -> x :: reorder tl induction_vars)
                  in

                  let new_vars_sorted =
                    List.map
                      (fun l ->
                        let induction_vars, other_vars =
                          List.partition
                            (fun x -> String.starts_with ~prefix:"IH" x)
                            l
                        in
                        reorder other_vars induction_vars)
                      new_vars
                  in

                  List.mapi
                    (fun _ l ->
                      let mapped =
                        List.map
                          (fun x ->
                            string_to_intro_pattern_expr x
                            |> Option.get |> CAst.make)
                          l
                      in
                      mapped)
                    new_vars_sorted
              in

              let new_or_intro_pattern :
                  Constrexpr.constr_expr Tactypes.or_and_intro_pattern_expr
                  CAst.t =
                Tactypes.IntroOrPattern new_or_and_intro_pattern |> CAst.make
              in

              let new_locus_or_and_intro_pattern_l :
                  Constrexpr.constr_expr Tactypes.or_and_intro_pattern_expr
                  CAst.t
                  Locus.or_var =
                Locus.ArgArg new_or_intro_pattern
              in

              ( destruction_arg,
                ( intro_pattern_naming_expr_opt,
                  Some new_locus_or_and_intro_pattern_l ),
                clause_expr_opt ))
            induction_clause_l
        in

        let new_raw_tac =
          TacAtom
            (TacInductionDestruct
               (rflag, eflag, (new_induction_clause_l, with_bindings)))
          |> CAst.make
        in

        Syntax_node.raw_tactic_expr_to_syntax_node new_raw_tac x.range.start
        |> Result.to_option
    | _ -> None
  in

  let rewrite_assert (x : Syntax_node.t)
      (old_goals_vars : string list list option)
      (new_goals_vars : string list list option) : Syntax_node.t option =
    let open Ltac_plugin.Tacexpr in
    let new_vars = get_new_vars old_goals_vars new_goals_vars in
    match new_vars with
    | Some new_vars ->
        let raw_atomic_expr =
          Syntax_node.get_node_raw_atomic_tactic_expr x |> Option.get
        in

        let eflag, b, tacexpr_opt_opt, _, term =
          match raw_atomic_expr with
          | TacAssert (eflag, b, tacexpr_opt_opt, _, term) ->
              (eflag, b, tacexpr_opt_opt, None, term)
          | _ -> assert false
        in

        let assert_generated_name =
          if is_syntax_node_assert_by x then List.nth new_vars 0 |> List.hd
          else List.nth new_vars 1 |> List.hd
        in

        let intro_pattern_expr =
          string_to_intro_pattern_expr assert_generated_name
          |> Option.get |> CAst.make
        in

        let new_raw_tac =
          TacAtom
            (TacAssert (eflag, b, tacexpr_opt_opt, Some intro_pattern_expr, term))
          |> CAst.make
        in
        Syntax_node.raw_tactic_expr_to_syntax_node new_raw_tac x.range.start
        |> Result.to_option
    | None -> None
  in

  let rewrite_intros (x : Syntax_node.t)
      (old_goals_vars : string list list option)
      (new_goals_vars : string list list option) : Syntax_node.t option =
    let open Ltac_plugin.Tacexpr in
    let new_vars = get_new_vars old_goals_vars new_goals_vars in
    match new_vars with
    | Some new_vars ->
        let raw_atomic_expr =
          Syntax_node.get_node_raw_atomic_tactic_expr x |> Option.get
        in

        let eflag, _ =
          match raw_atomic_expr with
          | TacIntroPattern (e, p) -> (e, p)
          | _ -> assert false
        in

        let intro_pattern_expr =
          List.hd new_vars
          |> List.map (fun x ->
              string_to_intro_pattern_expr x |> Option.get |> CAst.make)
        in
        let new_raw_tac =
          TacAtom (TacIntroPattern (eflag, intro_pattern_expr)) |> CAst.make
        in
        Syntax_node.raw_tactic_expr_to_syntax_node new_raw_tac x.range.start
        |> Result.to_option
    | None -> None
  in

  let rewriters :
      ((Syntax_node.t -> bool)
      * (Syntax_node.t ->
        string list list option ->
        string list list option ->
        Syntax_node.t option))
      list =
    [
      (is_syntax_node_intros_without_set_var, rewrite_intros);
      (is_syntax_node_assert_without_set_var, rewrite_assert);
      (is_syntax_node_induction_without_set_var, rewrite_induction);
    ]
  in

  let find_rewriter (node : Syntax_node.t) :
      (Syntax_node.t ->
      string list list option ->
      string list list option ->
      Syntax_node.t option)
      option =
    List.find_map
      (fun (predicate, rewriter) ->
        if predicate node then Some rewriter else None)
      rewriters
  in
  Runner.fold_proof_with_state doc token
    (fun state acc node ->
      let* new_state = Runner.run_node token state node in
      match find_rewriter node with
      | Some rewriter -> (
          let old_goals_vars =
            Runner.reified_goals_at_state token state
            |> List.map Runner.get_hypothesis_names
          in

          let new_goals_vars =
            Runner.reified_goals_at_state token new_state
            |> List.map Runner.get_hypothesis_names
          in

          match rewriter node (Some old_goals_vars) (Some new_goals_vars) with
          | Some x -> Ok (new_state, Replace (node.id, x) :: acc)
          | None -> Ok (new_state, acc))
      | None -> Ok (new_state, acc))
    [] proof

let apply_proof_transformation
    (transformation :
      Rocq_document.t ->
      Proof.proof ->
      (transformation_step list, Error.t) result) (doc : Rocq_document.t) :
    (Rocq_document.t, Error.t) result =
  let proofs_rec = Rocq_document.get_proofs doc in
  match proofs_rec with
  | Ok proofs ->
      List.fold_left
        (fun (doc_acc : (Rocq_document.t, Error.t) result) (proof : Proof.proof)
           ->
          match doc_acc with
          | Ok acc -> (
              let transformation_steps = transformation acc proof in
              match transformation_steps with
              | Ok steps ->
                  List.fold_left
                    (fun doc_acc_err step ->
                      match doc_acc_err with
                      | Ok doc ->
                          Rocq_document.apply_transformation_step step doc
                      | Error err -> Error err)
                    doc_acc steps
              | Error err -> Error err)
          | Error err -> Error err)
        (Ok doc) proofs
  | Error err -> Error err

let apply_proof_tree_transformation
    (transformation :
      Rocq_document.t ->
      Syntax_node.t nary_tree ->
      (transformation_step list, Error.t) result) (doc : Rocq_document.t) :
    (Rocq_document.t, Error.t) result =
  let proofs_rec = Rocq_document.get_proofs doc in
  match proofs_rec with
  | Ok proofs ->
      let proof_trees =
        List.filter_map
          (fun proof -> Result.to_option (Runner.treeify_proof doc proof))
          proofs
      in
      List.fold_left
        (fun (doc_acc : (Rocq_document.t, Error.t) result)
             (proof_tree : Syntax_node.t nary_tree) ->
          match doc_acc with
          | Ok acc -> (
              let transformation_steps = transformation acc proof_tree in
              match transformation_steps with
              | Ok steps ->
                  List.fold_left
                    (fun doc_acc_err step ->
                      match doc_acc_err with
                      | Ok doc ->
                          Rocq_document.apply_transformation_step step doc
                      | err -> err)
                    doc_acc steps
              | Error err -> Error err)
          | err -> err)
        (Ok doc) proof_trees
  | Error err -> Error err
