# Rocq ditto

## Description

`rocq-ditto` is a plugin and a library allowing to write transformations of Rocq proof scripts using the Rocq AST.
It use [rocq-lsp](https://github.com/ejgallego/coq-lsp) to extract and run the Rocq AST of a file.

`rocq-ditto` then provide utilities to add, delete and replace nodes in the AST, as well as extract proofs and 
transform them into different representations.

## install

### prerequisites

To configure `rocq-ditto`, you will first need a working and initialized `opam` installation.
You will also need the `gmp-dev` and `linux-headers` library.

### configuration

`rocq-ditto` can be configured by running `./configure.sh $ROCQ_VERSION_HERE` with `$ROCQ_VERSION_HERE` being either a full Rocq version (ie 9.0.0)
to pin `rocq-ditto` to that version, or using `latest` to have the latest Rocq version not pinned.

Once this is done, run `eval $(opam) env`.

If `./configure.sh` fail, run `rm -rf _opam/` in the `rocq-ditto` directory to remove the local opam switch and retry.
If for some reasons, you can't or don't want to use the `./configure.sh` script, you can use the following manual instructions:

If you want to configure `rocq-ditto` with the latest version of Rocq, use the following instructions:
```shell
opam switch -y create . ocaml-base-compiler --deps-only
opam install rocq-stdlib # the stdlib is not packaged with rocq anymore, not used to build but used to run rocq files
eval $(opam env)
mkdir -p vendor/
ln -s _opam/bin/rocq _opam/bin/coqc # this is needed for now so that dune can use coq variables like %{coq:version.major}
cp ./_opam/bin/fcc ./vendor/fcc
make build
```
Otherwise, to configure with a specific Rocq version, use the following instructions:
```shell
opam switch create . --empty
opam pin add # (coq-core $COQ_VERSION_HERE (ie 8.20.0) for version < 9.0) or rocq-core $ROCQ_VERSION_HERE (ie 9.0.0)
opam install . --deps-only
# if you are pinning a Rocq version: ln _opam/bin/rocq _opam/bin/coqc
mkdir -p vendor/
cp ./_opam/bin/fcc ./vendor/fcc
make build
```

To run `rocq-ditto` on a project needing Rocq libraries, install them in the same switch as `rocq-ditto`

## running on a simple file

To first know what transformations are available, you can run the following command:

``` shell
dune exec --profile=release rocq-ditto -- -i _ -o _ -t help
```

Then, to run the plugin on a single file, run the following command:

```shell
dune exec --profile=release rocq-ditto -- -i FILENAME -o OUTPUT_NAME -t TRANSFORMATION
```
Where each transformation(s) is one listed with the previous command. You can run multiple transformations in sequence by separating them by ",".

## running on a project

To run the plugin on a project, you must first install the project dependencies inside the opam switch of rocq-ditto.
Then, you can run the following command
```shell
dune exec --profile=release rocq-ditto -- -i PROJECT_FOLDER -o OUTPUT_FOLDER -t TRANSFORMATION
```

## upgrading 

When upgrading rocq-ditto using git, you might encounter these kinds of errors:
```shell
Dynlink.Error (Dynlink.Cannot_open_dll Failure ... undefined symbol: ...)
```

These errors are usually fixed by copying `fcc` again:
```shell
cp ./_opam/bin/fcc ./vendor/fcc
```

When upgrading, you may also encounter issues with the optcomp part used by `rocq-ditto` to adapt to different `rocq` version.
These issues are usually fixed by using `make clean` before rebuilding.
