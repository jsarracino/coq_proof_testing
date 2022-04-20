#!/usr/bin/env python3
##########################################################################
#
#    This file is part of Proverbot9001.
#
#    Proverbot9001 is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 3 of the License, or
#    (at your option) any later version.
#
#    Proverbot9001 is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with Proverbot9001.  If not, see <https://www.gnu.org/licenses/>.
#
#    Copyright 2019 Alex Sanchez-Stern and Yousef Alhessi
#
##########################################################################

import re
from typing import (List, Tuple, TypeVar,
                    Optional, Pattern, Match)

T = TypeVar('T')

import hashlib
BLOCKSIZE = 65536

def hash_file(filename : str) -> str:
    hasher = hashlib.md5()
    with open(filename, 'rb') as f:
        buf = f.read(BLOCKSIZE)
        while len(buf) > 0:
            hasher.update(buf)
            buf = f.read(BLOCKSIZE)
    return hasher.hexdigest()

import sys
def eprint(*args, **kwargs):
    if "guard" not in kwargs or kwargs["guard"]:
        print(*args, file=sys.stderr, **{i:kwargs[i] for i in kwargs if i!='guard'})
        sys.stderr.flush()

import contextlib

class DummyFile:
    def write(self, x): pass
    def flush(self): pass

@contextlib.contextmanager
def silent():
    save_stderr = sys.stderr
    save_stdout = sys.stdout
    sys.stderr = DummyFile()
    sys.stdout = DummyFile()
    try:
        yield
    finally:
        sys.stderr = save_stderr
        sys.stdout = save_stdout

mybarfmt = '{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}]'


def split_to_next_matching(openpat : str, closepat : str, target : str) \
    -> Tuple[str, str]:
    counter = 1
    openp = re.compile(openpat)
    closep = re.compile(closepat)
    firstmatch = openp.search(target)
    assert firstmatch, "Coudn't find an opening pattern!"
    curpos = firstmatch.end()
    while counter > 0:
        nextopenmatch = openp.search(target, curpos)
        nextopen = nextopenmatch.end() if nextopenmatch else len(target)

        nextclosematch = closep.search(target, curpos)
        nextclose = nextclosematch.end() if nextclosematch else len(target)
        if nextopen < nextclose:
            counter += 1
            assert nextopen + 1 > curpos, (target, curpos, nextopen)
            curpos = nextopen
        else:
            counter -= 1
            assert nextclose + 1 > curpos
            curpos = nextclose
    return target[:curpos], target[curpos:]

def multisplit_matching(openpat : str, closepat : str,
                        splitpat : str, target : str) \
                        -> List[str]:
    splits = []
    nextsplit = split_by_char_outside_matching(openpat, closepat, splitpat, target)
    rest = None
    while nextsplit:
        before, rest = nextsplit
        splits.append(before)
        nextsplit = split_by_char_outside_matching(openpat, closepat, splitpat, rest[1:])
    if rest:
        splits.append(rest[1:])
    else:
        splits.append(target)
    return splits


def split_by_char_outside_matching(openpat: str, closepat: str,
                                   splitpat: str, target: str) \
        -> Optional[Tuple[str, str]]:
    counter = 0
    curpos = 0
    with silent():
        openp = re.compile(openpat)
        closep = re.compile(closepat)
        splitp = re.compile(splitpat)

    def search_pat(pat: Pattern) -> Tuple[Optional[Match], int]:
        match = pat.search(target, curpos)
        return match, match.end() if match else len(target) + 1

    while curpos < len(target) + 1:
        _, nextopenpos = search_pat(openp)
        _, nextclosepos = search_pat(closep)
        nextsplitchar, nextsplitpos = search_pat(splitp)

        if nextopenpos < nextclosepos and nextopenpos < nextsplitpos:
            counter += 1
            assert nextopenpos > curpos
            curpos = nextopenpos
        elif nextclosepos < nextopenpos and \
                (nextclosepos < nextsplitpos or
                 (nextclosepos == nextsplitpos and counter > 0)):
            counter -= 1
            assert nextclosepos > curpos
            curpos = nextclosepos
        else:
            if counter <= 0:
                if nextsplitpos > len(target):
                    return None
                assert nextsplitchar
                return target[:nextsplitchar.start()], target[nextsplitchar.start():]
            else:
                assert nextsplitpos > curpos
                curpos = nextsplitpos
    return None


def unwrap(a: Optional[T]) -> T:
    assert a is not None
    return a
