(lang dune 3.15)

(name rocq-ditto)
(generate_opam_files true)

(source (github blackbird1128/rocq-ditto))

(license LGPL-3.0-or-later)

(authors "Alexandre Jean")
(maintainers "Alexandre Jean")

(documentation "https://url/to/documentation")

(package
 (name ditto-config)
 (synopsis "Configuration helpers for rocq-ditto")
 (description "Utilities to deduce configuration values for rocq-ditto.")
 (depends
  ocaml
  base-unix)
  )

(package
 (name coq-ditto)
 (synopsis "Rocq ditto library")
 (description "Core libraries used by the rocq-ditto plugins.")
 (depends
  ocaml 
  (coq-lsp (>= 0.2.4))
  base-unix
  re
  fpath
  logs
  alcotest
  uuidm
  ppx_import
  ppx_deriving
  ppx_deriving_yojson
  ppx_sexp_message
  ppx_sexp_value
  ))

(package
 (name ditto-cli-lib)
 (synopsis "Library behind the ditto CLI")
 (description "Helper library used by the ditto command-line interface.")
 (depends
  ocaml
  coq-ditto
  ppx_deriving
  ))

(package
 (name ditto-plugin)
 (synopsis "Basic Fleche plugin used by rocq-ditto")
 (description "Plugin used to run transformations in rocq-ditto.")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  coq-ditto))

(package
 (name shelley-plugin)
 (synopsis "Plugin to test proof-repair methods")
 (description "Plugin experimenting with several proof-repair approaches.")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  coq-ditto))

(package
 (name lens-query-plugin)
 (synopsis "Plugin using a lens datastructure for theorem queries")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  coq-ditto))

(package
 (name constructive-plugin)
 (synopsis "GeoCoq constructivisation plugin")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  coq-ditto))

(package
 (name get-basic-tactics-plugin)
 (synopsis "Extract basic tactics used in a file")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  coq-ditto))

(package
 (name neat-fcc-plugin)
 (synopsis "Compile a file and display any errors")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  coq-ditto))

(package
 (name target-generator-plugin)
 (synopsis "Generate JSON results for test comparisons")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  coq-ditto))

(package
 (name ditto-test-plugin)
 (synopsis "Run the rocq-ditto tests")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  uuidm
  coq-ditto))

(package
 (name json-dump-plugin)
 (synopsis "Dump a Rocq-AST to JSON")
 (description "Plugin to explore Rocq internal ASTs by dumping them to JSON.")
 (allow_empty)
 (depends
  ocaml
  (coq-lsp (>= 0.2.3))
  base-unix
  re
  coq-ditto))