open Proof

let constructivize_doc (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in

  let* proofs = Rocq_document.get_proofs doc in
  let* admit_proof_steps =
    List.fold_left
      (fun res_acc proof ->
        match res_acc with
        | Ok res_acc ->
            let* steps = Transformations.admit_proof doc proof in
            Ok (steps @ res_acc)
        | Error err -> Error err)
      (Ok []) proofs
  in
  Ok admit_proof_steps
