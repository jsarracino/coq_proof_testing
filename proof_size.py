#!/usr/bin/env python3

import os, sys
import shutil; sys.path.append(os.path.dirname(os.path.realpath(__file__)))

from dataclasses import dataclass
from typing import TypeVar, Dict, Any

from pampy import match, _ #type: ignore

from sexpdata import dumps #type: ignore

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
            functools.partial(measure_file, coqargs, args, includes),
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
                    with open(result_file, 'r') as f:
                        for line in f:
                            out.write(line)


def measure_file(coqargs: List[str], args: argparse.Namespace, includes: str,
                file_tuple: Tuple[int, str]) -> Optional[str]:
    sys.setrecursionlimit(4500)
    file_idx, filename = file_tuple
    full_filename = str(args.prelude) + "/" + filename
    result_file = full_filename + ".complex"
    temp_file = full_filename + ".complex.partial"
    if args.cont:
        with contextlib.suppress(FileNotFoundError):
            with open(result_file, 'r') as f:
                if args.verbose:
                    eprint(f"Found existing result at {result_file}! Using it")
                return result_file
    try:
        commands = serapi_instance.load_commands_preserve(args, file_idx, str(full_filename))
        with serapi_instance.SerapiContext(
                coqargs,
                serapi_instance.get_module_from_filename(filename),
                args.prelude, False) as coq:
            coq.verbose = args.verbose
            try:
                with open(temp_file, 'w') as f: 
                  lemmas = lemmas_in_commands(commands)
                  curr_lemma = None

                  for c_idx, cmd in enumerate([serapi_instance.kill_comments(c).strip() for c in commands]):
                    ser_cmd = f"(Add () \"{cmd}\")"
                    coq.run_stmt(cmd)
                    # send the initial command
                    # coq._send_acked(ser_cmd)
                    # # not sure what these are doing but ok
                    # coq._update_state()
                    # coq._get_completed()

                    # # send the exec command, presumably cur_state is updated from get_completed
                    # coq._send_acked("(Exec {})\n".format(coq.cur_state))
                    # # parse a bunch of feedbacks and an answer, discard the feedbacks + answer
                    # coq._get_feedbacks()


                    if c_idx in lemmas: 
                      curr_lemma = lemmas[c_idx]
                    if serapi_instance.ending_proof(cmd):
                      assert curr_lemma, "current lemma not set at end of proof" 
                      name = curr_lemma.name

                      type = get_type(coq, curr_lemma)

                      data = {
                        "name": filename + "." + name,
                        "length": curr_lemma.body_length(), 
                        "type": type
                      }
                      json.dump(data,fp=f)
                      f.write('\n')

                shutil.move(temp_file, result_file)
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

def split_cmd(c: str) -> List[str]: 
  # print("splitting", c)
  output = [x for x in re.split(";", c) if len(x) > 0]
  return output

@dataclass 
class Lemma: 
  defn: str
  body: List[str]

  def body_length(self) -> int: 
    all_cmds = [len(y) for y in [split_cmd(x) for x in self.body]]
    return sum(all_cmds)

  @property
  def name(self) -> str : 
    nme = serapi_instance.kill_comments(self.defn).split()[1]
    if nme[-1] == ":":
      nme = nme[:-1]
    return nme
    

T = TypeVar('T')
def rev_new(xs: List[T]) -> List[T]:
  return [x for x in reversed(xs)]

def skip_proof_cmd(cmd: str):
  return cmd.strip().startswith("Proof.")


def get_type(coq: serapi_instance.SerapiInstance, lemma: Lemma):
  # command looks like
  # (Query () (TypeOf "lemma_name"))

  ser_cmd = f"(Query () (TypeOf \"{lemma.name}\"))"
  # send the command
  coq._send_acked(ser_cmd)
  # there are 3 responses: 
  # an ack, handled above
  # the actual result, as an answer, where the 3rd term is an s-expr of the AST
  result = coq._get_message()
  parsed = match(serapi_instance.normalizeMessage(result),
              ["Answer", int, ["ObjList", _]],
              lambda _, inner: inner,
              _, 
              lambda msg: serapi_instance.raise_(serapi_instance.UnrecognizedError(msg)))

  if not len(parsed) == 1: 
    serapi_instance.raise_(serapi_instance.UnrecognizedError(parsed))
  # match(normalizeMessage(completed),
  #       ["Answer", int, "Completed"], lambda state: None,
  #       _, lambda msg: raise_(CompletedError(completed)))

  # an answer with Completed
  coq._get_completed()
  return dumps(parsed[0])


# TODO: get module prefix for lemma name
def lemmas_in_commands(cmds: List[str], include_proof_relevant: bool = False) \
        -> Dict[int, Lemma]:
    lemmas: Dict[int, Lemma] = {}
    in_proof = False
    proof_relevant = False
    curr_lemma_body : List[str] = []
    for c_idx, cmd in reversed(list(enumerate(cmds))):
        cmd = serapi_instance.kill_comments(cmd)
        if cmd == "":
          continue
        if in_proof:
          if serapi_instance.possibly_starting_proof(cmd):
              in_proof = False
              nxt_lemma = Lemma(defn = cmd, body = rev_new(curr_lemma_body))
              curr_lemma_body = []
              proof_relevant = proof_relevant or \
                  cmd.strip().startswith("Derive") or \
                  cmd.strip().startswith("Equations")
              if include_proof_relevant or not proof_relevant:
                  lemmas[c_idx] = nxt_lemma
          else: 
            if not skip_proof_cmd(cmd): curr_lemma_body.append(cmd.strip())
        if serapi_instance.ending_proof(cmd):
            proof_match = re.match(r"Proof.*", cmd)
            with_match = re.match(r".*with.*", cmd)
            parens_match = re.match(r".*\((.*)\).*", cmd) 

            in_proof = True
            curr_lemma_body = []
            proof_relevant = cmd.strip() == "Defined."


            if proof_match:
              if parens_match:
                curr_lemma_body = [parens_match.group(1)]
              if with_match: 
                print("found with match in:", cmd)


    return lemmas


if __name__ == "__main__":
    main()

def import_stats(f_name: str):
  lens = []
  with open(f_name, 'r') as f:
    for data in f: 
      if data: 
        parsed_data = json.loads(data)
        lens.append(int(parsed_data["length"]))
  print("parsed lens")
  print("1/4 quantile:", np.quantile(lens, 0.25))
  print("1/2 quantile:", np.quantile(lens, 0.5))
  print("3/4 quantile:", np.quantile(lens, 0.75))
