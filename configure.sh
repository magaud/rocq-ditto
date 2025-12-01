#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "Usage: $0 [latest|<rocq-version>]"
  echo "Example: $0 latest"
  echo "         $0 9.0.0"
  exit 1
}

detect_pkg() {
  local ver="$1"
  [[ "$ver" == "latest" ]] && echo "rocq-core" && return
  [[ "${ver%%.*}" -ge 9 ]] && echo "rocq-core" || echo "coq-core"
}

if [[ $# -ne 1 ]]; then
  usage
fi

VERSION="$1"

if [[ "$VERSION" == "latest" ]]; then
  echo ">> Setting up with the latest Rocq version..."
  opam switch -y create . ocaml-base-compiler --deps-only
#  opam install -y rocq-stdlib
  eval "$(opam env)"
  mkdir -p vendor/
  ln -f  _opam/bin/rocq _opam/bin/coqc
  cp ./_opam/bin/fcc ./vendor/fcc
  make build
else
  echo ">> Setting up with Rocq version $VERSION..."
  opam switch create . ocaml-base-compiler.5.4.0 --no-install
  # Pin either rocq-core (>=9.0.0) or coq-core (<9.0.0)

  PKG="$(detect_pkg "$VERSION")"
  echo ">> Pinning $PKG $VERSION..."
  opam pin add -y "$PKG" "$VERSION"
  
  opam install -y . --deps-only
  # For pinned Rocq version, dune still expects coqc to exist
  if [[ -f _opam/bin/rocq ]]; then
      ln -f _opam/bin/rocq _opam/bin/coqc
  fi
  mkdir -p vendor/
  cp ./_opam/bin/fcc ./vendor/fcc
fi

echo "Configuration completed successfully!"
