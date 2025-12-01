open Sexplib.Sexp
open Proof
open Vernacexpr
open Fleche

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

let get_proof_proposition_sexp (x : Proof.t) : Sexplib.Sexp.t option =
  let coq_ast =
    Option.map
      (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v)
      x.proposition.ast
  in
  match coq_ast with
  | Some ast -> (
      match ast.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | Vernacexpr.VernacStartTheoremProof _ ->
              let sexp_expr =
                Serlib.Ser_vernacexpr.sexp_of_synpure_vernac_expr expr_syn
              in
              Some sexp_expr
          | _ -> None))
  | None -> None

let rec matches (q : sexp_query) (sexp : Sexplib.Sexp.t) : bool =
  match (q, sexp) with
  | Q_anything, _ -> true
  | Q_empty, List [] -> true
  | Q_atom s, Atom a -> a = s
  | Q_field (key, qv), List [ Atom k; v ] ->
      if k = key then matches qv v else false
  | Q_field_path [], _ -> true
  | Q_field_path (k :: ks), List [ Atom k'; v ] when k = k' ->
      matches (Q_field_path ks) v
  | Q_list_any q, List l -> List.exists (matches q) l
  | Q_list_exact qs, List l ->
      List.length qs = List.length l && List.for_all2 matches qs l
  | Q_list_prefix qs, List l ->
      let len = List.length qs in
      if List.length l < len then false
      else List.for_all2 matches qs (List_utils.take len l)
  | Q_nth (n, qs), List l -> (
      match List.nth_opt l n with Some elem -> matches qs elem | None -> false)
  | Q_hd qs, List (x :: _) -> matches qs x
  | Q_last qs, List l ->
      if List.length l < 1 then false
      else
        let last_elem = List.nth l (List.length l - 1) in
        matches qs last_elem
  | Q_and qs, _ -> List.for_all (fun q -> matches q sexp) qs
  | Q_or qs, _ -> List.exists (fun q -> matches q sexp) qs
  | Q_not q, _ -> not (matches q sexp)
  | Q_anywhere q, sexp ->
      let rec go s =
        matches q s
        || match s with Atom _ -> false | List lst -> List.exists go lst
      in
      go sexp
  | Q_sequence seq, sexp ->
      print_endline "Not sure if this is correct";
      List.fold_left (fun acc action -> acc && matches action sexp) true seq
  | _, _ -> false

let rec extract_match (q : sexp_query) (sexp : Sexplib.Sexp.t) :
    Sexplib.Sexp.t option =
  match (q, sexp) with
  | Q_anything, ex -> Some ex
  | Q_empty, List [] -> Some (List [])
  | Q_atom s, Atom a -> if a = s then Some sexp else None
  | Q_field (key, qv), List [ Atom k; v ] ->
      if k = key then extract_match qv v else None
  | Q_field_path [], _ -> Some sexp
  | Q_field_path (k :: ks), List [ Atom k'; v ] when k = k' ->
      extract_match (Q_field_path ks) v
  | Q_list_any q, List l ->
      if List.exists (matches q) l then Some sexp else None
  | Q_list_exact qs, List l ->
      if List.length qs = List.length l && List.for_all2 matches qs l then
        Some sexp
      else None
  | Q_list_prefix qs, List l ->
      let len = List.length qs in
      if List.length l < len then None
      else if List.for_all2 matches qs (List_utils.take len l) then Some sexp
      else None
  | Q_nth (n, qs), List l -> (
      match List.nth_opt l n with
      | Some elem -> extract_match qs elem
      | None -> None)
  | Q_hd qs, List (x :: _) -> extract_match qs x
  | Q_last qs, List l ->
      if List.length l < 1 then None
      else
        let last_elem = List.nth l (List.length l - 1) in
        extract_match qs last_elem
  | Q_and qs, _ ->
      if List.for_all (fun q -> matches q sexp) qs then Some sexp else None
  | Q_or qs, _ ->
      if List.exists (fun q -> matches q sexp) qs then Some sexp else None
  | Q_not q, _ -> if not (matches q sexp) then Some sexp else None
  | Q_anywhere q, sexp ->
      let rec go s =
        match extract_match q s with
        | Some _ as res -> res
        | None -> (
            match s with Atom _ -> None | List lst -> List.find_map go lst)
      in
      go sexp
  | Q_sequence seq, sexp ->
      List.fold_left
        (fun acc action ->
          match acc with Some acc -> extract_match action acc | None -> None)
        (Some sexp) seq
  | _, _ -> None

let collect_matches (q : sexp_query) (sexp : Sexplib.Sexp.t) :
    Sexplib.Sexp.t list =
  let open Sexplib.Sexp in
  let rec collect s acc =
    let extraction = extract_match q s in
    let acc =
      if Option.has_some extraction then Option.get extraction :: acc else acc
    in
    match s with
    | Atom _ -> acc
    | List l -> List.fold_left (fun fold_acc x -> collect x fold_acc) acc l
  in
  collect sexp [] |> List.rev
