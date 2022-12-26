#!/usr/bin/env python3

import os, sys
import shutil

from coq_serapy.contexts import ProofContext

from coq_serapy.contexts import SexpObligation; sys.path.append(os.path.dirname(os.path.realpath(__file__)))

from dataclasses import dataclass
from typing import Deque, TypeVar, Dict, Any

from typing_extensions import TypedDict

from pampy import match, _ #type: ignore

from sexpdata import dumps #type: ignore

import argparse
import multiprocessing
import functools
import sys
import contextlib
import json
import re

import coq_serapy as serapi_instance

from coq_serapy_scraper.util import eprint, mybarfmt

from typing import TextIO, List, Tuple, Optional
from tqdm import tqdm # type: ignore

import numpy as np

from collections import deque

from coq_serapy_scraper.linearize_semicolons import get_linearized


def main():
    # Parse the command line arguments.
    parser = argparse.ArgumentParser(description="scrape a proof")
    parser.add_argument('-o', '--output', help="output data file name",
                        default=None)
    parser.add_argument('-j', '--threads', default=8, type=int)
    parser.add_argument('--linearizer-timeout', default=False, type=bool)
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

    if args.threads > 1:
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
    else:
      with (open(args.output, 'w') if args.output
          else contextlib.nullcontext(sys.stdout)) as out:
        for idx, filename in enumerate(args.inputs, start=1):
          result_file = measure_file(coqargs, args, includes, (idx, filename))
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


def opens_proof(cmd: str):
  return cmd.startswith("{")
def closes_proof(cmd: str):
  return cmd.startswith("}")

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
        collect_proof = True
        try:
          commands = get_linearized(args, coqargs, file_idx, filename)
          # print("linearized!", filename)
        except Exception as e:
          eprint("can't linearize:", str(full_filename))
          # raise e
          collect_proof = False
          commands = serapi_instance.load_commands_preserve(args, file_idx, str(full_filename))
        with serapi_instance.SerapiContext(
                coqargs,
                serapi_instance.get_module_from_filename(filename),
                args.prelude, False) as coq:
            coq.verbose = args.verbose
            try: 
                with open(temp_file, 'w') as f, open("proof_size_debug.out", 'w') as debug_file: 
                  lemmas = lemmas_in_commands(commands, collect_proof)
                  curr_lemma = None
                  proof_call_stack : Deque[ProofState] = deque()
                  curr_proof : Optional[ProofState] = None
                  goal : Optional[SexpObligation] = None

                  for c_idx, cmd in enumerate([serapi_instance.kill_comments(c).strip() for c in commands]):

                    if curr_proof and not coq.proof_context:
                      curr_proof = None

                    if curr_proof: 
                      # print(coq.proof_context)
                      goal = get_goal(coq)

                    print(cmd, file = debug_file)

                    if hides_info(cmd):
                      cmd = extract_info(coq, cmd)
                    else:
                      coq.run_stmt(cmd)


                    if args.threads == 1:
                      print(cmd, file = debug_file)
                    # if curr_lemma:
                      # print(f"(* current lemma: {curr_lemma.name} *)",file=debug_file)

                    if c_idx in lemmas: 
                      curr_lemma = lemmas[c_idx]
                      # print(f"lemma for {curr_lemma.name}:", curr_lemma)
                      curr_proof = ProofState.empty() if collect_proof else None
                      # print("opening proof, curr cmd is", cmd)
                      continue

                    if serapi_instance.ending_proof(cmd):
                      # print("closing proof:", cmd)
                      if not curr_lemma:
                        print(f"lemma not set on command #{c_idx}, {cmd}")
                        # assert curr_lemma, "current lemma not set at end of proof" 
                        curr_proof = None
                        proof_call_stack.clear()
                        continue

                      if curr_lemma.body_length() < 1:
                        print(f"weird zero length proof? at #{c_idx}, {cmd}")
                        curr_proof = None
                        proof_call_stack.clear()
                        continue

                      name = curr_lemma.name.strip()
                      # print(f"getting type for {name} at idx {c_idx}")
                      # print(f"command: {cmd}")
                      try:
                        type_sexpr = get_type_sexpr(coq, f"{name}")
                        type_str = get_type_str(coq, f"{name}")

                        data = {
                          "name": f"{filename}:{coq.module_prefix}{name}",
                          "length": curr_lemma.body_length(), 
                          "linear": curr_lemma.linear,
                          "type": str(type_sexpr),
                          "goal_str" : type_str
                        }

                        if curr_proof:
                          if len(proof_call_stack) > 0:
                            print(proof_call_stack)
                            print(curr_proof)
                            assert len(proof_call_stack) == 0, "nonempty ltac stack on proof close"
                          
                          data["proof"] = curr_proof.to_dict()

                          curr_proof = None
                          curr_lemma = None
                          proof_call_stack.clear()

                        json.dump(data,fp=f)
                        f.write('\n')
                      except Exception as e:
                        eprint(f"exception for: {filename}:{coq.module_prefix}{name}")
                        eprint(e)
                        if args.hardfail: raise e
                        curr_proof = None
                        proof_call_stack.clear()
                        continue

                      if curr_proof:
                        if opens_proof(cmd):
                          proof_call_stack.append(curr_proof)
                          curr_proof = ProofState.empty()
                        elif closes_proof(cmd):
                          next_proof = proof_call_stack.pop()
                          next_proof.append_child(curr_proof)
                          curr_proof = next_proof
                        else:
                          if re.match("Proof", cmd):
                            if cmd.strip() == "Proof.": continue
                            else:
                              curr_proof = None
                          if not goal: continue
                          # print("goals:")
                          # print(coq.goals)
                          # print(kill_whitespace(coq.goals))
                          curr_proof.append_tac(cmd, ctx = {
                              "hypos": [str(x) for x in goal.hypotheses]
                            , "type": str(goal.goal)
                            , "goal_str": kill_whitespace(coq.goals)
                            , "hypo_strs": [kill_whitespace(x) for x in coq.hypotheses]
                          })
                    

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

def hides_info(cmd: str):
  return cmd.strip() in ["eauto.", "auto.", "trivial."]


def extract_info(coq : serapi_instance.SerapiInstance, cmd: str):
  info_cmd = f"info_{cmd}"

  coq.run_stmt(info_cmd)
  tactic_str = str(coq.feedbacks[3][1][3][1][-1][-1])

  tactic_str = tactic_str.split('(in ')[0]

  return tactic_str.strip() + '.'


def split_cmd(c: str) -> List[str]: 
  # print("splitting", c)
  output = [x for x in re.split(";", c) if len(x) > 0]
  return output

class ProofCtx(TypedDict):
  # these two strs are Sexprs
  hypos: List[str]
  type: str
  # and these two are coq string representations of terms
  goal_str: str
  hypo_strs: List[str]

@dataclass 
class ProofStep:
  tacs: List[str]
  ctx: ProofCtx

  def to_dict(self):
    return {
        "tacs": self.tacs
      , "ctx": self.ctx
    }

@dataclass
class ProofState:
  steps: List[ProofStep]
  children: List['ProofState']

  def append_tac(self, tac: str, ctx: ProofCtx):
    self.steps.append(ProofStep(split_cmd(tac), ctx))

  def append_child(self, child: Any):
    self.children.append(child)

  @staticmethod
  def empty(): return ProofState([], [])

  def to_dict(self): 
    return {
        "steps": [x.to_dict() for x in self.steps]
      , "children": [x.to_dict() for x in self.children] 
    }

# find the final prefix and take the next identifier as the name
# prefixes: 
# Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property | Definition | Fixpoint | Equations
# technically also Let and CoFixpoint
# final_prefixes = ["Theorem", "Lemma", "Fact", "Remark", "Corollary", "Proposition", "Property", "Definition", "Fixpoint", "Equations"]

def kill_whitespace(s: str) -> str:
  return re.sub("\s+", ' ', s)

@dataclass 
class Lemma: 
  defn: str
  body: List[str]
  linear: bool

  def body_length(self) -> int: 
    all_cmds = [len(y) for y in [split_cmd(x) for x in self.body if not opens_proof(x) and not closes_proof(x)]]
    return sum(all_cmds)

  @property
  def name(self) -> str : 
    nme = serapi_instance.kill_comments(self.defn).split()[1]
    if nme[-1] == ":":
      nme = nme[:-1]
    return nme
    
  @property
  def goal(self) -> str : 
    goal = ' '.join(serapi_instance.kill_comments(self.defn).split()[2:])

    return kill_whitespace(goal)

T = TypeVar('T')
def rev_new(xs: List[T]) -> List[T]:
  return [x for x in reversed(xs)]

def skip_proof_cmd(cmd: str):
  return cmd.strip().startswith("Proof.")


def get_type_str(coq: serapi_instance.SerapiInstance, term: str):
  # command looks like
  # (Query () (TypeOf "lemma_name"))

  ser_cmd = f"(Query ((pp ((pp_format PpStr)))) (TypeOf \"{term}\"))"
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
  return parsed[0][1]

def get_type_sexpr(coq: serapi_instance.SerapiInstance, term: str):
  # print("getting type of:", term)
  # command looks like
  # (Query () (TypeOf "lemma_name"))

  ser_cmd = f"(Query () (TypeOf \"{term}\"))"
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
  return parsed[0]

def get_goal(coq: serapi_instance.SerapiInstance):

  goal_types = coq.get_all_sexp_goals()

  if len(goal_types) > 0:
    return goal_types[0]
  else:
    return None

def lemmas_in_commands(cmds: List[str], linear: bool, include_proof_relevant: bool = False) \
        -> Dict[int, Lemma]:
    lemmas: Dict[int, Lemma] = {}
    in_proof = False
    curr_lemma_body : List[str] = []
    for c_idx, cmd in reversed(list(enumerate(cmds))):
        cmd = serapi_instance.kill_comments(cmd)
        if serapi_instance.ending_proof(cmd):
            proof_match = re.match(r"Proof.*", cmd)
            with_match = re.match(r".*with.*", cmd)
            parens_match = re.match(r".*\((.*)\).*", cmd) 

            in_proof = True
            curr_lemma_body = []


            if proof_match:
              if parens_match:
                curr_lemma_body = [parens_match.group(1)]
              if with_match: 
                print("found with match in:", cmd)
        if cmd == "":
          continue
        if in_proof:
          if serapi_instance.possibly_starting_proof(cmd):
              in_proof = False
              nxt_lemma = Lemma(defn = cmd, linear = linear, body = rev_new(curr_lemma_body))
              curr_lemma_body = []
              uses_obligations = cmd.strip().startswith("Equations") or \
                  cmd.strip().startswith("Program") or \
                  cmd.strip().startswith("Next Obligation")
              if (include_proof_relevant and uses_obligations) or not uses_obligations:
                  lemmas[c_idx] = nxt_lemma
              else:
                  nxt_lemma = None
          else: 
            if not skip_proof_cmd(cmd): curr_lemma_body.append(cmd.strip())
        


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
