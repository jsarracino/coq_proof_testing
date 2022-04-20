Coq Serapy Scraper
==================

A project for scraping proof data from a Coq .v file into static text,
using the [coq_serapy](https://github.com/HazardousPeach/coq_serapy)
interface to Coq (a python binding for coq-serapi).

This code was originally developed as part of the
[Proverbot9001](https://github.com/UCSD-PL/proverbot9001) project. If
you use this library as part of published research, some sort of
acknowledgement would be nice, but is not required.

Dependencies
------------

To use this project, you need:

Opam 2.0 or later
Installed through Opam:
* Coq 8.9-8.12 (versions past 8.12 may also work, but have not been tested)
* coq-serapi

Installed through pip (you can install these with `pip install -r requirements.txt`):
* pathlib_revised
* tqdm
* sexpdata
* pampy

Installed through github:
* coq_serapy

Usage
-----

First, make sure that opam binaries like `sertop` are in your path:
   `eval $(opam env)`

Then, scrape the file. The simplest form of the command is:
`python3 /path/to/scraper/__init__.py /path/to/source/file.v`

This assumes that you are currently in the root of the target project,
and that if your files require any arguments to compile, they are
found in a `_CoqProject` in the current directory. Sometimes this file
is called `Make`, if so rename or copy it to `_CoqProject`. If you're
not in the project root, or the `_CoqProject` file is in a different
directory, pass the argument
`--prelude=/path/to/coqproject/dir/`. Then, all filenames that are
relative should be specified relative to that directory.

Output is produced in the same location as each input, as a
`*.v.scrape` file, and the output for all files is concatenated and
printed to standard out. You can suppress output to standard out with
`-o /dev/null`, or print the output to a file with `-o /path/to/file`
(individual file output will still also be outputted to `*.v.scrape`
in the source file directory).

The `-j` option can be used to specify a number of threads, when there
are multiple file arguments; scraping is parallelized at the file
level.

The `-c` option can be used to skip scraping when a `*.v.scrape` file
already exists, and use the existing file instead.

`-P` will print progress bars for files that are being scraped and
linearized.

More options can be found in `__init__.py` at the top of the `main`
function.


Data format
-------------

As input, the scraper takes a `*.v` file that runs to completion with
the installed Coq version.


For ease of streaming parsing, the datafile contains information about
one Coq command per line. The lines are in order that the Coq commands
appear in the source file. There are two types of lines in the output
file:

**Vernacular commands** ([coq
docs](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html))
are stored as a single json-formatted string constant.

**Tactics (proof commands)** ([coq
docs](https://coq.inria.fr/refman/proof-engine/tactics.html)) are
stored as a json object with fields "relevant\_lemmas",
"prev\_tactics", "context", and "tactic".

relevant_lemmas is a list of strings, where each string has the form
"lemma\_name : lemma\_type".

"prev\_tactics" is a list of strings, where each string is a previous
tactic in the proof. Importantly, this field only contains the tactics
relevant to the current subgoal. So if your proof so far is:

```
...
auto. induction.
{ reflexivity. }
{ eauto.
```

Then your tactic history will be [..., "auto.", "induction.",
"eauto."], and will *not* contain the "reflexivity" from the previous
subgoal.

"context" is the json serialization of the
[ProofContext](https://github.com/HazardousPeach/coq_serapy/blob/f17813b3f699152fb4d0f0424ac7c2129e602264/contexts.py#L40)
object defined in coq serapy.

Finally, "tactic" is a single string representing the tactic command.

Linearization
-------------

This scraper is designed for automated tooling which processes Coq
proofs. To aid these tools, the scraper first "linearizes" proofs
before scraping them. This means it attempts to take compound commands
which use the ";" (semicolon) operator, and unroll them. This can be a
complex process, and is not always possible. In cases where the
unrolling is not possible, or is too hard for the unrolling algorithm
we use, the linearizer will skip proofs and simply output their
original, non-linearized version.

Since linearizing can be slow (it involves running the file again to
understand dynamic subgoal information), the linearizer stores its
output in a `*.v.lin` file next to the original `*.v` file. The first
line of this file is a hash of the contents of the original `*.v`
file. The rest is a valid Coq file with the same theorems and
vernacular as the original file, but with linearized proofs where
possible.

The first scrape of a file does this linearization before scraping,
and subsequent scrapes check the hash on the linearized file, and use
its contents if the hash matches the current content of the `*.v`
file. If the hash doesn't match, the file will be re-linearized.

If you don't want your source file linearized, and want to scrape it
as-is, you can pass the flag `--no-linearize`.

The linearizer can also be invoked as a standalone module to just
linearize coq files, with `python3
path/to/scraper/linearize_semicolons.py filename ...`.
