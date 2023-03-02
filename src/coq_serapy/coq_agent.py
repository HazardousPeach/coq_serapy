#!/usr/bin/env python3

import re

from typing import Optional, List, Union, Iterable, Tuple, Callable
from dataclasses import dataclass

from .util import eprint, unwrap
from .coq_backend import CoqBackend
from .coq_util import (kill_comments, preprocess_command,
                       possibly_starting_proof, ending_proof,
                       lemmas_defined_by_stmt, update_sm_stack,
                       setup_opam_env, summarizeContext)
from .contexts import TacticContext, ProofContext

@dataclass
class FileState:
    in_proof: bool
    tactic_history: Optional['TacticHistory']

    local_lemmas: List[Tuple[str, bool]]
    local_lemmas_cache: Optional[List[str]]
    sm_stack: List[Tuple[str, bool]]
    module_changed: bool
    def __init__(self) -> None:
        self.in_proof = False
        self.tactic_history = None
        self.local_lemmas = []
        self.local_lemmas_cache = None
        self.sm_stack = []
        self.module_changed = True

    @property
    def module_stack(self) -> List[str]:
        return [entry for entry, is_section in self.sm_stack
                if not is_section]

    @property
    def section_stack(self) -> List[str]:
        return [entry for entry, is_section in self.sm_stack
                if is_section]
    @property
    def sm_prefix(self) -> str:
        return "".join([sm + "." for sm, is_sec in self.sm_stack])

    @property
    def module_prefix(self) -> str:
        return "".join([module + "." for module in self.module_stack])

    def add_potential_local_lemmas(self, cmd: str) -> None:
        lemmas = lemmas_defined_by_stmt(self.module_prefix, cmd)
        is_section = "Let" in cmd
        for lemma in lemmas:
            self.local_lemmas.append((lemma, is_section))
            if lemma.startswith(self.module_prefix):
                cached = lemma[len(self.module_prefix):].replace('\n', '')
            else:
                cached = lemma.replace("\n", "")
            if self.local_lemmas_cache is not None:
                self.local_lemmas_cache.append(cached)

    def cancel_potential_local_lemmas(self, cmd: str) -> None:
        lemmas = lemmas_defined_by_stmt(self.module_prefix, cmd)
        is_section = "Let" in cmd
        for lemma in lemmas:
            self.local_lemmas.remove((lemma, is_section))

    def remove_potential_local_lemmas(self, cmd: str) -> None:
        reset_match = re.match(r"Reset\s+(.*)\.", cmd)
        if reset_match:
            reseted_lemma_name = self.module_prefix + reset_match.group(1)
            for (lemma, is_section) in list(self.local_lemmas):
                if lemma == ":":
                    continue
                lemma_match = re.match(r"\s*([\w'\.]+)\s*:", lemma)
                assert lemma_match, f"{lemma} doesnt match!"
                lemma_name = lemma_match.group(1)
                if lemma_name == reseted_lemma_name:
                    self.local_lemmas.remove((lemma, is_section))
        abort_match = re.match(r"\s*Abort", cmd)
        if abort_match:
            self.local_lemmas.pop()

    def add_potential_smstack_cmd(self, cmd: str) -> None:
        new_stack = update_sm_stack(self.sm_stack, cmd)
        if len(self.sm_stack) > 0 and \
           self.sm_stack[-1][1] and \
           len(new_stack) < len(self.sm_stack):
            self.local_lemmas = \
                [(lemma, is_section) for (lemma, is_section)
                 in self.local_lemmas if not is_section]
        if len(new_stack) != len(self.sm_stack):
            self.module_changed = True
        self.sm_stack = new_stack

class CoqAgent:
    backend: CoqBackend
    _file_state: FileState
    verbosity: int

    def __init__(self, backend: CoqBackend,
                 root_dir: Optional[str] = None,
                 verbosity: int = 0) -> None:
        self.backend = backend
        self._file_state = FileState()
        self.verbosity = verbosity
        self.root_dir = root_dir
        if root_dir:
            self._exec_includes(root_dir)
        self.run_stmt("Unset Printing Notations.")

    # For backwards compatibility
    @property
    def verbose(self) -> int:
        return self.verbosity
    @verbose.setter
    def verbose(self, value: int) -> None:
        self.verbosity = value

    def __enter__(self) -> 'CoqAgent':
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        self.kill()

    def kill(self) -> None:
        self.backend.close()

    def update_state(self) -> None:
        self.backend.updateState()

    def run_stmt_noupdate(self, stmt: str) -> None:
        eprint(f"Running statement without update: {stmt.strip()}", guard=self.verbosity >= 2)
        self._run_stmt_with_f(stmt, self.backend.addStmt_noupdate)

    def run_stmt(self, stmt: str, timeout: Optional[int] = None,
                 force_update_nonfg_goals: bool = False) -> None:
        eprint(f"Running statement: {stmt.strip()}", guard=self.verbosity >= 2)
        self._run_stmt_with_f(
            stmt,
            lambda stmt: self.backend.addStmt(
                stmt, timeout=timeout,
                force_update_nonfg_goals=force_update_nonfg_goals))

    def _run_stmt_with_f(self, stmt: str, f: Callable) -> None:
        # Kill the comments early so we can recognize comments earlier
        stmt = kill_comments(stmt)
        # We need to escape some stuff so that it doesn't get stripped
        # too early.
        stmt = stmt.replace("\\", "\\\\")
        stmt = stmt.replace("\"", "\\\"")
        for stm in preprocess_command(stmt):
            f(stm)
            if not self._file_state.in_proof:
                self._file_state.add_potential_smstack_cmd(stm)
                self._file_state.add_potential_local_lemmas(stm)
                if possibly_starting_proof(stm) and self.backend.isInProof():
                    self._file_state.tactic_history = TacticHistory()
                    self._file_state.in_proof = True

            else:
                if ending_proof(stm):
                    self._file_state.in_proof = False
                    self._file_state.tactic_history = None
                self._file_state.remove_potential_local_lemmas(stm)
            # Track goal opening/closing
            is_goal_open = re.match(r"\s*(?:\d+\s*:)?\s*[{]\s*", stm)
            is_goal_close = re.match(r"\s*[}]\s*", stm)
            if self._file_state.in_proof:
                assert self._file_state.tactic_history
                assert self.proof_context
                if is_goal_open:
                    self._file_state.tactic_history.openSubgoal()
                elif is_goal_close:
                    self._file_state.tactic_history.closeSubgoal()
                else:
                    self._file_state.tactic_history.addTactic(stm)
                if self.verbosity >= 3:
                    eprint(
                        f"History is now {self.tactic_history.getFullHistory()}")
                    summarizeContext(self.proof_context)

    def cancel_last_noupdate(self) -> None:
        assert self._file_state.in_proof, "Can't cancel with no update outside proof"
        assert self._file_state.tactic_history
        assert len(self._file_state.tactic_history.getFullHistory()) > 1, \
            "Can't cancel out of a proof with a noupdate call"
        cancelled = self._file_state.tactic_history.getNextCancelled()
        eprint(f"Cancelling command without update: {cancelled}", guard=self.verbosity >= 2)
        self._file_state.tactic_history.removeLast()
        self._file_state.cancel_potential_local_lemmas(cancelled)
        self.backend.cancelLastStmt_noupdate(cancelled)
        if self._file_state.in_proof and possibly_starting_proof(cancelled):
            self._file_state.in_proof = False
            self._file_state.tactic_history = None

    def cancel_last(self) -> None:
        if self._file_state.in_proof:
            assert self._file_state.tactic_history
            cancelled = self._file_state.tactic_history.getNextCancelled()
            self._file_state.cancel_potential_local_lemmas(cancelled)
            eprint(f"Cancelling command {cancelled}", guard=self.verbosity >= 2)
            self._file_state.tactic_history.removeLast()
        else:
            # If we're cancelling vernac, we don't need to know what the command was.
            cancelled = ""
        self.backend.cancelLastStmt(cancelled)
        if self._file_state.in_proof and possibly_starting_proof(cancelled) and \
           not self.backend.isInProof():
            self._file_state.in_proof = False
            self._file_state.tactic_history = None
        elif not self._file_state.in_proof and ending_proof(cancelled):
            self._file_state.in_proof = True
            self._file_state.tactic_history = TacticHistory()
        if self._file_state.in_proof and self.verbosity >= 3:
            assert self.proof_context
            eprint(
                f"History is now {self.tactic_history.getFullHistory()}")
            summarizeContext(self.proof_context)

    def run_into_next_proof(self, commands: List[str]) \
            -> Tuple[List[str], List[str]]:
        assert not self.backend.isInProof(), "We're already in a proof"
        commands_iter = iter(commands)
        commands_run = []
        for command in commands_iter:
            self.run_stmt(command, timeout=120)
            commands_run.append(command)
            if self.backend.isInProof():
                return list(commands_iter), commands_run
        return [], commands_run
    def finish_proof(self, commands: List[str]) \
            -> Optional[Tuple[List[str], List[str]]]:
        assert self.backend.isInProof(), "We're already out of a proof"
        commands_iter = iter(commands)
        commands_run = []
        for command in commands_iter:
            self.run_stmt(command, timeout=60)
            commands_run.append(command)
            if not self.backend.isInProof():
                return list(commands_iter), commands_run
        return None
    def reset(self) -> None:
        self._file_state = FileState()
        self.run_stmt("Reset Initial.")
        if self.root_dir:
            self._exec_includes(self.root_dir)
        self.run_stmt("Unset Printing Notations.")
    @property
    def goals(self) -> str:
        proof_context = self.backend.getProofContext()
        if proof_context and proof_context.fg_goals:
            return proof_context.fg_goals[0].goal
        return ""

    @property
    def hypotheses(self) -> List[str]:
        proof_context = self.backend.getProofContext()
        if proof_context and proof_context.fg_goals:
            return proof_context.fg_goals[0].hypotheses
        return []

    @property
    def prev_tactics(self):
        return self._file_state.tactic_history.getCurrentHistory()

    @property
    def local_lemmas(self) -> List[str]:
        def generate() -> Iterable[str]:
            for (lemma, _is_section) in self._file_state.local_lemmas:
                if lemma.startswith(self._file_state.module_prefix):
                    yield lemma[len(self._file_state.module_prefix):].replace('\n', '')
                else:
                    yield lemma.replace('\n', '')
        if self._file_state.module_changed:
            self._file_state.local_lemmas_cache = list(generate())
            self._file_state.module_changed = False
        return unwrap(self._file_state.local_lemmas_cache)[:-1]

    @property
    def cur_lemma(self) -> str:
        return self.local_lemmas[-1]

    @property
    def cur_lemma_name(self) -> str:
        match = re.match(r"\s*([\w'\.]+)\s+:.*", self.cur_lemma)
        assert match, f"Can't match {self.cur_lemma}"
        return match.group(1)

    @property
    def proof_context(self) -> Optional[ProofContext]:
        return self.backend.getProofContext()

    @property
    def sm_prefix(self) -> str:
        return self._file_state.sm_prefix
    @property
    def tactic_history(self) -> 'TacticHistory':
        return self._file_state.tactic_history
    # For backwards compatibility
    @property
    def use_hammer(self) -> bool:
        return False

    def tactic_context(self, relevant_lemmas) -> TacticContext:
        return TacticContext(relevant_lemmas,
                             self.prev_tactics,
                             self.hypotheses,
                             self.goals)

    def count_fg_goals(self) -> int:
        if not self.proof_context:
            return 0
        return len(self.proof_context.fg_goals)

    def check_term(self, term: str) -> str:
        return self.backend.queryVernac(f"Check {term}.")[0]
    def locate_ident(self, ident: str) -> str:
        return "\n".join(self.backend.queryVernac(f"Locate {ident}."))
    def interrupt(self) -> None:
        self.backend.interrupt()
    def get_lemmas_about_head(self) -> List[str]:
        proof_context = self.proof_context
        assert proof_context, "Can't run get_lemmas_about_head when not in a proof!"
        head = proof_context.focused_goal.split()[0]
        return self.search_about(head)
    def search_about(self, symbol: str) -> List[str]:
        return self.backend.queryVernac(f"Search {symbol}.")

    def _exec_includes(self, root_dir: str) -> None:
        try:
            with open(root_dir + "/_CoqProject", 'r') as includesfile:
                includes_string = includesfile.read()
        except FileNotFoundError:
            try:
                with open(root_dir + "/Make", 'r') as includesfile:
                    includes_string = includesfile.read()
            except FileNotFoundError:
                eprint(f"Didn't find _CoqProject or Make for {root_dir}")
                includes_string = ""

        for includematch in re.finditer(r"-[QRI]\s*[^-]*", includes_string):
            q_match = re.fullmatch(r"-Q\s*(\S*)\s*(\S*)\s*", includematch.group(0))
            if q_match:
                if q_match.group(2) == "\"\"":
                    self.run_stmt(
                        f"Add LoadPath \"{q_match.group(1)}\".")
                else:
                    self.run_stmt(
                        f"Add LoadPath \"{q_match.group(1)}\" as {q_match.group(2)}.")
                continue
            r_match = re.match(r"-R\s*(\S*)\s*(\S*)\s*", includematch.group(0))
            if r_match:
                self.run_stmt(
                    f"Add Rec LoadPath \"{r_match.group(1)}\" as {r_match.group(2)}.")
                continue
            i_match = re.match(r"-I\s*(\S*)", includematch.group(0))
            if i_match:
                self.run_stmt(
                    f"Add ML Path \"{i_match.group(1)}\".")
                continue




@dataclass
class TacticTree:
    children: List[Union['TacticTree', str]]
    isClosed: bool

    def __repr__(self) -> str:
        result = "["
        for child in self.children:
            result += repr(child)
            result += ","
        result += "]"
        return result


class TacticHistory:
    __tree: TacticTree
    __cur_subgoal_depth: int

    def __init__(self) -> None:
        self.__tree = TacticTree([], False)
        self.__cur_subgoal_depth = 0

    def openSubgoal(self) -> None:
        curTree = self.__tree
        for _ in range(self.__cur_subgoal_depth):
            assert isinstance(curTree.children[-1], TacticTree)
            curTree = curTree.children[-1]
        curTree.children.append(TacticTree([], False))
        self.__cur_subgoal_depth += 1


    def closeSubgoal(self) -> None:
        curTree = self.__tree
        for _ in range(self.__cur_subgoal_depth):
            assert isinstance(curTree.children[-1], TacticTree)
            curTree = curTree.children[-1]
        curTree.isClosed = True
        assert self.__cur_subgoal_depth > 0
        self.__cur_subgoal_depth -= 1

    def curDepth(self) -> int:
        return self.__cur_subgoal_depth

    def addTactic(self, tactic: str) -> None:
        curTree = self.__tree
        for _ in range(self.__cur_subgoal_depth):
            assert isinstance(curTree.children[-1], TacticTree)
            curTree = curTree.children[-1]
        curTree.children.append(tactic)

    def removeLast(self) -> None:
        assert len(self.__tree.children) > 0, \
            "Tried to remove from an empty tactic history!"
        curTree = self.__tree
        for _ in range(self.__cur_subgoal_depth):
            assert isinstance(curTree.children[-1], TacticTree)
            curTree = curTree.children[-1]
        if len(curTree.children) == 0:
            parent = self.__tree
            for _ in range(self.__cur_subgoal_depth-1):
                assert isinstance(parent.children[-1], TacticTree)
                parent = parent.children[-1]
            parent.children.pop()
            self.__cur_subgoal_depth -= 1
        else:
            lastChild = curTree.children[-1]
            if isinstance(lastChild, str):
                curTree.children.pop()
            else:
                assert isinstance(lastChild, TacticTree)
                self.__cur_subgoal_depth += 1
                lastChild.isClosed = False

    def getCurrentHistory(self) -> List[str]:
        def generate() -> Iterable[str]:
            curTree = self.__tree
            for i in range(self.__cur_subgoal_depth+1):
                yield from (child for child in curTree.children
                            if isinstance(child, str))
                if i < self.__cur_subgoal_depth:
                    assert isinstance(curTree.children[-1], TacticTree)
                    curTree = curTree.children[-1]
        return list(generate())

    def getFullHistory(self) -> List[str]:
        def generate(tree: TacticTree) -> Iterable[str]:
            for child in tree.children:
                if isinstance(child, TacticTree):
                    yield "{"
                    yield from generate(child)
                    if child.isClosed:
                        yield "}"
                else:
                    yield child
        return list(generate(self.__tree))

    def getNextCancelled(self) -> str:
        curTree = self.__tree
        assert len(curTree.children) > 0, \
            "Tried to cancel from an empty history"
        for _ in range(self.__cur_subgoal_depth):
            assert isinstance(curTree.children[-1], TacticTree)
            curTree = curTree.children[-1]

        if len(curTree.children) == 0:
            return "{"
        if isinstance(curTree.children[-1], TacticTree):
            return "}"
        assert isinstance(curTree.children[-1], str), curTree.children[-1]
        return curTree.children[-1]

    def __str__(self) -> str:
        return f"depth {self.__cur_subgoal_depth}, {repr(self.__tree)}"
