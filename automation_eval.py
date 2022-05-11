#!/usr/bin/env python3

import os, sys
import shutil; sys.path.append(os.path.dirname(os.path.realpath(__file__)))

from dataclasses import dataclass
from typing import TypeVar

import argparse
import multiprocessing
import functools
import sys
import contextlib
import json
import re

import coq_serapy_scraper.coq_serapy as serapi_instance

from coq_serapy_scraper.util import eprint, mybarfmt

from typing import TextIO, List, Tuple, Optional
from tqdm import tqdm # type: ignore

import numpy as np

import sh


def main():
    # Parse the command line arguments.
    parser = argparse.ArgumentParser(description="scrape a proof")
    parser.add_argument('-o', '--output', help="output data file name",
                        default=None)
    parser.add_argument('-j', '--threads', default=1, type=int)
    parser.add_argument('-c', '--continue', dest='cont', default=False,
                        const=True, action='store_const')
    parser.add_argument('--hardfail', default=False, const=True,
                        action='store_const')
    parser.add_argument('--hardfail-scrape', action='store_true')
    parser.add_argument('--prelude', default=".")
    parser.add_argument('-v', '--verbose', action='count', default=0)
    parser.add_argument("--progress", "-P", help="show progress of files",
                        action='store_const', const=True, default=False)
    parser.add_argument('--skip-nochange-tac', default=False, const=True,
                        action='store_const',
                        dest='skip_nochange_tac')
    parser.add_argument('inputs', nargs="+", help="proof file name(s) (*.v)")
    args = parser.parse_args()

    try:
        with open(args.prelude + "/_CoqProject", 'r') as includesfile:
            includes = includesfile.read()
    except FileNotFoundError:
        eprint("Didn't find a _CoqProject file in prelude dir", args.prelude)
        includes = ""
    # Set up the command which runs sertop.
    coqargs = ["sertop", "--implicit"]
    tasks = [(idx % args.threads, filename) for (idx, filename)
             in enumerate(args.inputs)]
    with multiprocessing.Pool(args.threads) as pool:
        result_files = pool.imap(
            functools.partial(edit_file, coqargs, args),
            tasks)
        with (open(args.output, 'w') if args.output
              else contextlib.nullcontext(sys.stdout)) as out:
            for idx, result_file in enumerate(result_files,
                                                     start=1):
                if result_file is None:
                    eprint("Failed file {} of {}"
                           .format(idx, len(args.inputs)))
                else:
                    if args.verbose:
                        eprint("Finished file {} of {}"
                               .format(idx, len(args.inputs)))
                    # with open(result_file, 'r') as f:
                    #     for line in f:
                    #         out.write(line)

def make_name(cmd: str): 
 
  nme = serapi_instance.kill_comments(cmd).split()[1]
  if nme[-1] == ":":
    nme = nme[:-1]
  return nme

def edit_file(coqargs: List[str], args: argparse.Namespace,
                file_tuple: Tuple[int, str]) -> Optional[str]:
    sys.setrecursionlimit(4500)
    file_idx, filename = file_tuple
    full_filename = str(args.prelude) + "/" + filename
    result_file = full_filename
    temp_file = full_filename + ".partial"
    if args.cont:
        with contextlib.suppress(FileNotFoundError):
            with open(result_file, 'r') as f:
                if args.verbose:
                    eprint(f"Found existing result at {result_file}! Using it")
                return result_file
    try:
        commands = serapi_instance.load_commands_preserve(args, file_idx, str(full_filename))
        lemmas = lemmas_idx_in_cmds(commands)
        with serapi_instance.SerapiContext(
                coqargs,
                serapi_instance.get_module_from_filename(filename),
                args.prelude, False) as coq:
            coq.verbose = args.verbose
            try:
                with open(temp_file, 'w') as f: 
                  for cmd_idx, cmd in enumerate(commands): 

                    if serapi_instance.ending_proof(cmd):
                      proof_match = re.match(r"Proof.*", cmd.strip())
                      parens_match = re.match(r".*\((.*)\).*", cmd) 
                      direct_match = re.match(r"Proof (.*)\.", cmd)

                      if proof_match:
                        if args.verbose: eprint("matched proof", cmd)
                        if parens_match:
                          if args.verbose: eprint("matched parens!", cmd)
                          lemma = parens_match.group(1)
                          f.write("Proof. exact (%s). Qed.\n" % lemma)
                        elif direct_match:
                          lemma = direct_match.group(1)
                          f.write("Proof. exact (%s). Qed.\n" % lemma)
                        else: 
                          f.write(cmd)
                      else: 
                        if args.verbose: eprint("did not match proof", cmd)
                        f.write(cmd)
                    else:
                      if args.verbose: eprint("did not end proof", cmd)
                      f.write(cmd)

                    if (cmd_idx, cmd) in lemmas:
                      name = make_name(cmd)
                      f.write("idtac \"beginning proof of %s using int-eauto.\".\n" % name)
                      f.write("try (auto_eval_wrapper ltac:(intuition eauto; fail)).\n")
                      f.write("""all: try idtac "int-eauto tactic failed". Restart.\n""")
                      f.write("idtac \"beginning proof of %s using hammer.\".\n" % name)
                      f.write("try (auto_eval_wrapper ltac:(hammer)).\n")
                      f.write("""all: try idtac "hammer tactic failed". Restart.\n""")

                shutil.move(temp_file, result_file)
                sh.Command("./prefix_hammer.sh")([result_file])
                return result_file
            except serapi_instance.TimeoutError:
                eprint("Command in {} timed out.".format(filename))
                return temp_file
    except Exception as e:
        eprint("FAILED: In file {}:".format(filename))
        eprint(e)
        if args.hardfail or len(args.inputs) == 1:
            raise e
    return None

def lemmas_idx_in_cmds(cmds: List[str],
                   include_proof_relevant: bool = False) \
        -> List[Tuple[int, str]]:
    lemmas = []
    proof_relevant = False
    in_proof = False
    for cmd_idx, cmd in reversed(list(enumerate(cmds))):
        if in_proof and serapi_instance.possibly_starting_proof(cmd):
            in_proof = False
            proof_relevant = proof_relevant or \
                cmd.strip().startswith("Derive") or \
                cmd.strip().startswith("Equations")
            if not proof_relevant or include_proof_relevant:
                lemmas.append((cmd_idx, cmd))
        if serapi_instance.ending_proof(cmd):
            in_proof = True
            proof_relevant = cmd.strip() == "Defined."
            
    return lemmas

if __name__ == "__main__":
    main()
