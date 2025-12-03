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
PKG="$(detect_pkg "$VERSION")"

if [[ -d _opam ]]; then
  echo ">> Trying to reuse local opam switch"
  eval "$(opam env)"
  if [[ "$VERSION" == "latest" ]]; then
      echo ">> Creating fresh local switch"
      REUSE_SWITCH=0
  else
      # Try to detect the version of the pinned package inside _opam
      CURRENT_VERSION="$(opam show --field=version "$PKG" 2>/dev/null || echo none)"
      
      if [[ "$CURRENT_VERSION" == "$VERSION" ]]; then
	  echo ">> Switch matches requested version ($CURRENT_VERSION) (reusing)"
	  REUSE_SWITCH=1
	  eval "$(opam env --switch=./ --set-switch)"
      else
	  echo ">> Switch mismatch ($CURRENT_VERSION <> $VERSION) (rebuilding)"
	  REUSE_SWITCH=0
      fi
  fi
else
  REUSE_SWITCH=0
fi

if [[ $REUSE_SWITCH -eq 0 ]]; then
    if [[ "$VERSION" == "latest" ]]; then
	echo ">> Setting up with the latest Rocq version..."
	opam switch -y create . ocaml-base-compiler --deps-only
	#  opam install -y rocq-stdlib
    else
	echo ">> Setting up with Rocq version $VERSION..."
	opam switch create . ocaml-base-compiler.5.4.0 --no-install
	# Pin either rocq-core (>=9.0.0) or coq-core (<9.0.0)

	echo ">> Pinning $PKG $VERSION..."
	opam pin add -y "$PKG" "$VERSION"
  
	opam install -y . --deps-only
	# For pinned Rocq version, dune still expects coqc to exist

    fi    
fi

if [[ -f _opam/bin/rocq ]]; then
    ln -f _opam/bin/rocq _opam/bin/coqc
fi
mkdir -p vendor/
cp ./_opam/bin/fcc ./vendor/fcc


echo "Configuration completed successfully!"
