open Code_point

type t = { start : Code_point.t; end_ : Code_point.t } [@@deriving sexp, yojson]

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "{start_pos = %a; end_pos = %a}" Code_point.pp x.start
    Code_point.pp x.end_

let to_string (x : t) : string = Format.asprintf "%a" pp x

let code_range_from_lang_range (x : Lang.Range.t) : t =
  {
    start = code_point_from_lang_point x.start;
    end_ = code_point_from_lang_point x.end_;
  }

let range_from_starting_point_and_repr (starting_point : Code_point.t)
    (repr : string) : t =
  let number_line_jump =
    String.fold_left
      (fun count char -> if char = '\n' then count + 1 else count)
      0 repr
  in
  let last_jump = String.rindex_opt repr '\n' in
  let offset_length = String.length repr in
  {
    start = starting_point;
    end_ =
      {
        line = starting_point.line + number_line_jump;
        character =
          (if number_line_jump > 0 then
             String.length repr - Option.get last_jump - 1
           else starting_point.character + offset_length);
      };
  }

let are_flat_ranges_colliding (a : int * int) (b : int * int) : bool =
  let a_start, a_end = a in
  let b_start, b_end = b in
  not (a_end < b_start || b_end < a_start)

let common_range (a : int * int) (b : int * int) : (int * int) option =
  let a_start, a_end = a in
  let b_start, b_end = b in
  if are_flat_ranges_colliding (a_start, a_end) (b_start, b_end) then
    Some (max a_start b_start, min a_end b_end)
  else None
