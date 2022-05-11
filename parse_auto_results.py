#!/usr/bin/env python3

import argparse
from dataclasses import dataclass
from optparse import Option

from typing import Set, Dict, Union, cast, List

import re

from numpy import require


@dataclass(frozen=True)
class Attempt:
  fname: str
  lemma: str


def parse_attempts(input_fname: str): 

  output : Set[Attempt] = set()
  current_file = None

  with open(input_fname) as input_file:
    for line in input_file:

      line=line.strip()

      file_pat = r"COQC (.*)"
      begin_proof_pat = r"beginning proof of (.+) using (.+)\."

      file_match = re.match(file_pat, line)
      begin_proof_match = re.match(begin_proof_pat, line)
      

      if file_match: 
        current_file = file_match.group(1)
      elif begin_proof_match: 
        lemma, _ = cast("tuple[str, str]", begin_proof_match.groups())
        assert current_file, f"current file was not set when parsing {lemma}"
        output.add(Attempt(current_file, lemma))

  return output

def parse_results(input_fname: str, attempts: Set[Attempt]) -> Dict[Attempt, Dict[str, bool]] : 

  output : Dict[Attempt, Dict[str, bool]] = {at : {} for at in attempts}
  current_file : Union[str, None] = None
  current_lemma : Union[str, None] = None
  current_tactic : Union[str, None] = None

  with open(input_fname) as input_file:
    for line in input_file:

      line=line.strip()

      file_pat = r"COQC (.*)"
      begin_proof_pat = r"beginning proof of (.+) using (.+)\."
      end_proof_pat = r"(.+) tactic failed"

      file_match = re.match(file_pat, line)
      begin_proof_match = re.match(begin_proof_pat, line)
      end_proof_match = re.match(end_proof_pat, line)
      

      if file_match: 
        if current_lemma: 
          assert current_tactic and current_file, f"current tactic/file was not set when switching to {file_match.group(1)}"
          # previous one succeeded
          attempt = Attempt(current_file, current_lemma)
          assert attempt in output, f"missing attempt {attempt}"
          output[attempt][current_tactic] = True
          current_lemma = None

        current_file = file_match.group(1)
      elif begin_proof_match: 

        lemma, tactic = cast("tuple[str, str]", begin_proof_match.groups())
        assert current_file, f"current file was not set when parsing {lemma}/{tactic}"

        if current_lemma: 
          assert current_tactic, f"current tactic was not set when parsing {lemma}"
          # previous one succeeded
          attempt = Attempt(current_file, current_lemma)
          assert attempt in output, f"missing attempt {attempt}"
          output[attempt][current_tactic] = True

        current_lemma = lemma
        current_tactic = tactic

      elif end_proof_match:
        # proof tactic failed
        tactic = end_proof_match.group(1)
        assert current_tactic == tactic, f"current and ending tactics do not match: {current_tactic} vs {tactic}"
        if not current_lemma: 
          continue
        assert current_file and current_tactic and current_lemma, f"current file/tactic/lemma was not set when parsing {lemma}: {current_file}/{current_tactic}/{current_lemma}"
        attempt = Attempt(current_file, current_lemma)
        assert attempt in output, f"missing attempt {attempt} in {output}"
        output[attempt][tactic] = False
        current_lemma = None
  return output

def fmt_result(attempt: Attempt, results: Dict[str, bool]) -> str :
  strs : List[str] = []
  for tactic, success in results.items():
    split_path = attempt.fname.split('/')
    if len(split_path) == 1:
      prefix = ""
      suffix = split_path[0]
    else: 
      prefix = "/".join(split_path[:-1])
      suffix = split_path[-1]

    succ_str = "1" if success else "0"
    strs.append(",".join([prefix, suffix, attempt.lemma, tactic, succ_str]))
  return "\n".join(strs)


if __name__ == "__main__":
  parser = argparse.ArgumentParser(description="parse an automation run")
  parser.add_argument('--input', type=str, help="file name of automation run", required=True)
  parser.add_argument('--output', type=str, help="file name of output", required=True)

  args = parser.parse_args()
    
  attempts = parse_attempts(args.input)

  results = parse_results(args.input, attempts)

  with open(args.output, 'w') as out_file:
    print("path,file,lemma,tactic,success/fail", file=out_file)
    for attempt, result in results.items():
      print(fmt_result(attempt, result), file=out_file)


