open Syntax_node
open Nary_tree
open Proof

let protect_to_result (r : ('a, 'b) Coq.Protect.E.t) : ('a, Error.t) result =
  match r with
  | { r = Interrupted; feedback = _ } -> Error.string_to_or_error "Interrupted"
  | { r = Completed (Error (User { msg; _ })); feedback = _ } ->
      Error.string_to_or_error (Pp.string_of_ppcmds msg)
  | { r = Completed (Error (Anomaly { msg; _ })); feedback = _ } ->
      Error.string_to_or_error ("Anomaly " ^ Pp.string_of_ppcmds msg)
  | { r = Completed (Ok r); feedback = _ } -> Ok r

let protect_to_result_with_feedback (r : ('a, 'b) Coq.Protect.E.t) :
    ('a * 'b Coq.Message.t list, Error.t * 'b Coq.Message.t list) result =
  match r with
  | { r = Interrupted; feedback } ->
      Error (Error.of_string "Interrupted", feedback)
  | { r = Completed (Error (User { msg; _ })); feedback } ->
      Error (Error.of_string (Pp.string_of_ppcmds msg), feedback)
  | { r = Completed (Error (Anomaly { msg; _ })); feedback } ->
      Error (Error.of_string ("Anomaly " ^ Pp.string_of_ppcmds msg), feedback)
  | { r = Completed (Ok r); feedback } -> Ok (r, feedback)

let run_with_timeout ~(token : Coq.Limits.Token.t) ~(timeout : int)
    ~(f : 'a -> ('b, Error.t) result) x : ('b, Error.t) result =
  (* Start a timeout thread *)
  let completed = ref false in

  let _ =
    Thread.create
      (fun () ->
        Unix.sleep timeout;
        if not !completed then Coq.Limits.Token.set token)
      ()
  in

  if Coq.Limits.Token.is_set token then Error (Error.of_string "Interrupted")
  else
    let () = Control.interrupt := false in
    try
      let y = f x in
      completed := true;
      y
    with Sys.Break -> Error.string_to_or_error "Interrupted"

let goals ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t) :
    ( (string Coq.Goals.Reified_goal.t, string) Coq.Goals.t option,
      Error.t )
    result =
  let f goals =
    let f = Coq.Goals.Reified_goal.map ~f:Pp.string_of_ppcmds in
    let g = Pp.string_of_ppcmds in
    Option.map (Coq.Goals.map ~f ~g) goals
  in

  Coq.Protect.E.map ~f
    (Fleche.Info.Goals.goals ~pr:Fleche.Info.Goals.to_pp ~token ~st)
  |> protect_to_result

let message_to_diagnostic (range : Code_range.t) (msg : Loc.t Coq.Message.t) :
    Lang.Diagnostic.t =
  (* TODO: remove dummy value use *)
  let lang_start_point : Lang.Point.t =
    { line = range.start.line; character = range.start.character; offset = -1 }
  in
  let lang_end_point : Lang.Point.t =
    { line = range.end_.line; character = range.end_.character; offset = -1 }
  in
  let lang_range : Lang.Range.t =
    { start = lang_start_point; end_ = lang_end_point }
  in
  let severity, payload = msg in
  { severity; message = payload.msg; data = None; range = lang_range }

(* Adaptor, should be supported in memo directly *)
let eval_no_memo ~token (st, cmd) =
  Coq.Interp.interp ~token ~intern:Vernacinterp.fs_intern ~st cmd

(* TODO, what to do with feedback, what to do with errors *)
let rec parse_execute_loop ~token ~memo pa ~msg_acc st =
  let open Coq.Protect.E.O in
  let eval = if memo then Fleche.Memo.Interp.eval else eval_no_memo in
  let* ast = Coq.Parsing.parse ~token ~st pa in
  match ast with
  | Some ast -> (
      match eval ~token (st, ast) with
      | Coq.Protect.E.
          { r = Coq.Protect.R.Completed (Ok st); feedback = messages } ->
          parse_execute_loop ~token ~memo pa ~msg_acc:(msg_acc @ messages) st
      | res -> Coq.Protect.E.map ~f:(fun x -> (x, msg_acc)) res)
  (* On EOF we return the previous state, the command was the empty string or a
     comment *)
  | None -> Coq.Protect.E.ok (st, msg_acc)

let parse_and_execute_in ~token ~loc tac st =
  let str = Gramlib.Stream.of_string tac in
  let pa = Coq.Parsing.Parsable.make ?loc str in
  parse_execute_loop ~token pa st

let run_with_diagnostics ~(token : Coq.Limits.Token.t) ?(loc : Loc.t option)
    ?(memo = true) ~(st : Coq.State.t) (cmds : string) :
    (Coq.State.t * Loc.t Coq.Message.t list, Loc.t) Coq.Protect.E.t =
  Coq.State.in_stateM ~token ~st
    ~f:(parse_and_execute_in ~token ~loc ~memo ~msg_acc:[] cmds)
    st

let run_node (token : Coq.Limits.Token.t) (prev_state : Coq.State.t)
    (node : Syntax_node.t) : (Coq.State.t, Error.t) result =
  let execution =
    let st =
      Fleche.Doc.run ~token ~memo:true ?loc:None ~st:prev_state (repr node)
    in
    st
  in

  protect_to_result execution

let run_node_with_diagnostics (token : Coq.Limits.Token.t)
    (prev_state : Coq.State.t) (node : Syntax_node.t) :
    ( Coq.State.t * Lang.Diagnostic.t list,
      Error.t * Lang.Diagnostic.t list )
    result =
  let execution =
    let st =
      run_with_diagnostics ~token ~memo:true ?loc:None ~st:prev_state
        (repr node)
    in
    st
  in

  let res = protect_to_result_with_feedback execution in
  match res with
  | Ok x ->
      let state_msgs, messages = x in
      let state = fst state_msgs in
      let all_msgs = snd state_msgs @ messages in
      Ok (state, List.map (message_to_diagnostic node.range) all_msgs)
  | Error err ->
      let err, messages = err in
      Error (err, List.map (message_to_diagnostic node.range) messages)

let get_init_state (doc : Rocq_document.t) (node : Syntax_node.t)
    (token : Coq.Limits.Token.t) : (Coq.State.t, Error.t) result =
  let open Sexplib.Std in
  let nodes_before, _ = Rocq_document.split_at_id node.id doc in
  let init_state = doc.initial_state in
  let error_tagged = false in
  let state, error_tagged, last_node =
    List.fold_left
      (fun (state, error_tagged, prev_node) node ->
        match state with
        | Ok state -> (run_node token state node, error_tagged, Some node)
        | Error err ->
            if error_tagged then (Error err, error_tagged, Some node)
            else
              let prev_node_repr = Option.map (fun x -> repr x) prev_node in
              let msg =
                [%message
                  ""
                    ~loc:(node.range : Code_range.t)
                    ~repr:(prev_node_repr : string option)]
              in
              (Error (Error.tag_sexp err "info" msg), true, Some node))
      (Ok init_state, error_tagged, None)
      nodes_before
  in
  Result.map_error
    (fun err ->
      if not error_tagged then
        let last_node_repr =
          Option.map (fun x -> Syntax_node.repr x) last_node
        in
        let msg =
          [%message
            ""
              ~loc:(node.range : Code_range.t)
              ~repr:(last_node_repr : string option)]
        in
        Error.tag_sexp err "info" msg
      else err)
    state

let get_hypothesis_names (goal : string Coq.Goals.Reified_goal.t) : string list
    =
  List.concat_map
    (fun (hyp : string Coq.Goals.Reified_goal.hyp) -> hyp.names)
    goal.hyps

let get_proof_state (start_result : (Coq.State.t, Loc.t) Coq.Protect.E.t) :
    Coq.State.t =
  match protect_to_result start_result with
  | Ok run_result -> run_result
  | Error err ->
      Printf.eprintf "Error: %s\n" (Error.to_string_hum err);
      raise (Failure "Failed to start proof")

let count_goals (token : Coq.Limits.Token.t) (st : Coq.State.t) : int =
  let goals = goals ~token ~st in
  match goals with
  | Ok (Some reified_goals) -> List.length reified_goals.goals
  | Ok None -> 0
  | Error _ -> 0

let reified_goals_at_state (token : Coq.Limits.Token.t) (st : Coq.State.t) :
    string Coq.Goals.Reified_goal.t list =
  let goals = goals ~token ~st in
  match goals with
  | Ok (Some reified_goals) -> reified_goals.goals
  | Ok None -> []
  | Error _ -> []

let proof_steps_with_goalcount (token : Coq.Limits.Token.t) (st : Coq.State.t)
    (steps : Syntax_node.t list) : (int * Syntax_node.t * int) list =
  let rec aux (token : Coq.Limits.Token.t) (st : Coq.State.t)
      (steps : Syntax_node.t list) =
    match steps with
    | [] -> []
    | step :: tail ->
        let before_count = count_goals token st in
        if
          is_syntax_node_focusing_goal step
          || is_syntax_node_closing_bracket step
        then (before_count, step, before_count) :: aux token st tail
        else
          let state = Fleche.Doc.run ~token ~st (repr step) in
          let agent_state = get_proof_state state in
          let goal_count = count_goals token agent_state in
          (before_count, step, goal_count) :: aux token agent_state tail
  in
  aux token st steps

let can_reduce_to_zero_goals (init_state : Coq.State.t)
    (nodes : Syntax_node.t list) : bool =
  let token = Coq.Limits.Token.create () in

  let rec aux state acc nodes =
    match nodes with
    | [] -> Ok acc
    | x :: tail -> (
        let state_node_res = run_node token state x in
        match state_node_res with
        | Ok state_node -> aux state_node state_node tail
        | Error _ -> Error "")
  in
  match aux init_state init_state nodes with
  | Ok state -> count_goals token state = 0
  | Error _ -> false

let get_current_goal (token : Coq.Limits.Token.t) (state : Coq.State.t) :
    (string Coq.Goals.Reified_goal.t, Error.t) result =
  let goals_err_opt = goals ~token ~st:state in
  match goals_err_opt with
  | Ok (Some goals) -> (
      match List.nth_opt goals.goals 0 with
      | Some goal -> Ok goal
      | None -> Error.string_to_or_error "zero goal at this state")
  | Ok None -> Error.string_to_or_error "zero goal at this state"
  | Error err -> Error err

type parent_category = Fork | Linear

let rec pop_until_free_fork
    (prev_pars : (int * int * Syntax_node.t * parent_category) list)
    (parents : (int * Syntax_node.t, int * Syntax_node.t) Hashtbl.t) :
    (int * int * Syntax_node.t * parent_category) list =
  match prev_pars with
  | [] -> []
  | (goal_count, par_id, par_node, cat_par) :: tail_par -> (
      match cat_par with
      | Fork ->
          let childs_count =
            List.length (Hashtbl.find_all parents (par_id, par_node))
          in
          if childs_count < goal_count then prev_pars
          else pop_until_free_fork tail_par parents
      | Linear -> pop_until_free_fork tail_par parents)

let rec get_parents_rec (steps_with_goals : (int * Syntax_node.t * int) list)
    (prev_pars : (int * int * Syntax_node.t * parent_category) list) (idx : int)
    (parents : (int * Syntax_node.t, int * Syntax_node.t) Hashtbl.t) =
  match steps_with_goals with
  | [] -> parents
  | (prev_goals, step, new_goals) :: tail -> (
      match prev_pars with
      | [] ->
          if new_goals > prev_goals then
            get_parents_rec tail
              [ (new_goals - prev_goals + 1, idx, step, Fork) ]
              (idx + 1) parents
          else
            get_parents_rec tail
              [ (new_goals, idx, step, Linear) ]
              (idx + 1) parents
      | (_, idx_par, tactic_par, _) :: _ ->
          let par = (idx_par, tactic_par) in
          if new_goals < prev_goals then (
            Hashtbl.add parents par (idx, step);
            if new_goals > 0 then
              get_parents_rec tail
                (pop_until_free_fork prev_pars parents)
                (idx + 1) parents
            else
              get_parents_rec tail
                [ (new_goals, idx, step, Linear) ]
                (idx + 1) parents)
          else if new_goals = prev_goals then (
            Hashtbl.add parents par (idx, step);
            get_parents_rec tail
              ((new_goals, idx, step, Linear) :: prev_pars)
              (idx + 1) parents)
          else (
            Hashtbl.add parents par (idx, step);
            get_parents_rec tail
              ((new_goals - prev_goals + 1, idx, step, Fork) :: prev_pars)
              (idx + 1) parents))

let rec proof_tree_from_parents (cur_node : int * Syntax_node.t)
    (parents : (int * Syntax_node.t, int * Syntax_node.t) Hashtbl.t) :
    Syntax_node.t nary_tree =
  let _, tactic = cur_node in
  let childs = Hashtbl.find_all parents cur_node in
  Node
    ( tactic,
      List.rev_map (fun node -> proof_tree_from_parents node parents) childs )

let treeify_proof (doc : Rocq_document.t) (p : Proof.t) :
    (Syntax_node.t nary_tree, Error.t) result =
  let token = Coq.Limits.Token.create () in
  match get_init_state doc p.proposition token with
  | Ok init_state ->
      let steps_with_goals =
        proof_steps_with_goalcount token init_state (Proof.proof_nodes p)
      in

      let parents = Hashtbl.create (List.length steps_with_goals) in
      let _ = get_parents_rec steps_with_goals [] 0 parents in
      Ok (proof_tree_from_parents (0, p.proposition) parents)
  | Error err -> Error err

let is_valid_proof (doc : Rocq_document.t) (p : Proof.t) : bool =
  let token = Coq.Limits.Token.create () in
  match get_init_state doc p.proposition token with
  | Ok init_state -> can_reduce_to_zero_goals init_state p.proof_steps
  | Error _ -> false

let rec proof_tree_to_node_list (Node (value, children)) : Syntax_node.t list =
  value :: List.concat (List.map proof_tree_to_node_list children)

let tree_to_proof (tree : Syntax_node.t nary_tree) : (Proof.t, Error.t) result =
  let ( let* ) = Result.bind in
  let nodes = proof_tree_to_node_list tree in
  let* nodes_head =
    List.nth_opt (List.rev nodes) 0
    |> Option.cata Result.ok
         (Error.format_to_or_error
            "proof_tree_to_node_list returned an empty list")
  in

  let* last_node_status = nodes_head |> proof_status_from_last_node in

  Ok
    {
      proposition = List.hd nodes;
      proof_steps = List.tl nodes;
      status = last_node_status;
    }

(* take a full tree and return an acc *)
(* fold over the proof while running the expr each time to get a new state *)
let depth_first_fold_with_state (doc : Rocq_document.t)
    (token : Coq.Limits.Token.t)
    (f :
      Coq.State.t ->
      'acc ->
      Syntax_node.t ->
      (Coq.State.t * 'acc, Error.t) result) (acc : 'acc)
    (tree : Syntax_node.t nary_tree) : ('acc, Error.t) result =
  let ( let* ) = Result.bind in

  let rec aux
      (f :
        Coq.State.t ->
        'acc ->
        Syntax_node.t ->
        (Coq.State.t * 'acc, Error.t) result) (state : Coq.State.t) (acc : 'acc)
      (tree : 'a nary_tree) : (Coq.State.t * 'acc, Error.t) result =
    match tree with
    | Node (x, children) ->
        let* state, acc = f state acc x in
        (* Fold over the children using the updated state and accumulator *)
        List.fold_left
          (fun res_acc child ->
            let* state, acc = res_acc in
            aux f state acc child)
          (Ok (state, acc))
          children
    (* Fold over the children, threading the state and updating acc *)
    (* Update state and accumulator for the current node *)
  in

  let* proof = tree_to_proof tree in
  match get_init_state doc proof.proposition token with
  | Ok state ->
      let* _, acc = aux f state acc tree in
      Ok acc
  | Error err ->
      Error
        (Error.tag err
           ~tag:"depth_first_with_state: Unable to retrieve initial state")

let fold_nodes_with_state
    (f :
      Coq.State.t ->
      'acc ->
      Syntax_node.t ->
      (Coq.State.t * 'acc, Error.t) result) (init_state : Coq.State.t)
    (acc : 'acc) (l : Syntax_node.t list) : ('acc, 'err) result =
  let ( let* ) = Result.bind in
  let rec aux (l : Syntax_node.t list) (state : Coq.State.t) (acc : 'acc) :
      (Coq.State.t * 'acc, Error.t) result =
    match l with
    | [] -> Ok (state, acc)
    | x :: tail ->
        let* new_state, acc = f state acc x in
        aux tail new_state acc
  in
  Result.map (fun (_, acc) -> acc) (aux l init_state acc)

let fold_proof_with_state (doc : Rocq_document.t) (token : Coq.Limits.Token.t)
    (f :
      Coq.State.t ->
      'acc ->
      Syntax_node.t ->
      (Coq.State.t * 'acc, Error.t) result) (acc : 'acc) (p : Proof.t) :
    ('acc, Error.t) result =
  let proof_nodes = Proof.proof_nodes p in

  match get_init_state doc p.proposition token with
  | Ok state -> fold_nodes_with_state f state acc proof_nodes
  | Error err ->
      Error
        (Error.tag err
           ~tag:"depth_first_with_state: Unable to retrieve initial state")
