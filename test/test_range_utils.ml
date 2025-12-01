(* test_range_utils.ml *)

open Alcotest
open Ditto.Code_range

let test_simple_overlapping () =
  check bool "overlapping simple" true (are_flat_ranges_colliding (2, 5) (4, 6))

let test_no_overlapping () =
  check bool "no overlap" false (are_flat_ranges_colliding (1, 3) (4, 6))

let test_exact_match_collision () =
  check bool "exact match" true (are_flat_ranges_colliding (2, 5) (2, 5))

let test_a_contains_b_collision () =
  check bool "a contains b" true (are_flat_ranges_colliding (2, 10) (4, 5))

let test_b_contains_a_collision () =
  check bool "b contains a" true (are_flat_ranges_colliding (4, 5) (2, 10))

let test_get_simple_common_range () =
  check
    (option (pair int int))
    "common simple"
    (Some (4, 5))
    (common_range (2, 5) (4, 6))

let test_no_common_range () =
  check (option (pair int int)) "no common" None (common_range (1, 3) (4, 6))

let test_exact_common_range () =
  check
    (option (pair int int))
    "exact"
    (Some (2, 5))
    (common_range (2, 5) (2, 5))

let test_a_contains_b_common_range () =
  check
    (option (pair int int))
    "a contains b"
    (Some (4, 5))
    (common_range (2, 10) (4, 5))

let test_b_contains_a_common_range () =
  check
    (option (pair int int))
    "b contains a"
    (Some (4, 5))
    (common_range (4, 5) (2, 10))

let () =
  run "Range utils"
    [
      ( "Collisions",
        [
          test_case "test two ranges overlapping" `Quick test_simple_overlapping;
          test_case "test two ranges not overlapping" `Quick test_no_overlapping;
          test_case "test two ranges exactly overlapping" `Quick
            test_exact_match_collision;
          test_case "test two ranges where a contains b" `Quick
            test_a_contains_b_collision;
          test_case "test two ranges where b contains a" `Quick
            test_b_contains_a_collision;
        ] );
      ( "Common range",
        [
          test_case "get a simple common range" `Quick
            test_get_simple_common_range;
          test_case "return none when no common range" `Quick
            test_no_common_range;
          test_case "get the common range of twice the same range" `Quick
            test_exact_common_range;
          test_case "get the common range of a range a containing a range b"
            `Quick test_a_contains_b_common_range;
          test_case "get the common range of a range b containing a range a"
            `Quick test_b_contains_a_common_range;
        ] );
    ]
