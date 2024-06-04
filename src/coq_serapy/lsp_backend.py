#!/usr/bin/env python

import threading
import subprocess
import re
import os
from os import environ
import signal
import queue
import functools

from typing import Any, Dict, List, cast, Callable, Optional, Tuple, Union

import pylspclient

from .contexts import ProofContext, Obligation, SexpObligation
from .coq_backend import CoqBackend, UnrecognizedError, CoqException, CoqExn, CoqTimeoutError, CoqAnomaly
from .coq_util import setup_opam_env
from .util import eprint, unwrap

class QueuePipe(threading.Thread):

    def __init__(self, pipe):
        threading.Thread.__init__(self)
        self.pipe = pipe
        self.queue = queue.Queue()

    def run(self):
        line = self.pipe.readline().decode('utf-8')
        while line:
            eprint(f"Error line: {line}")
            self.queue.put(line)
            line = self.pipe.readline().decode('utf-8')
    def get(self) -> str:
        return self.queue.get()

def verbosePut(verbosity: int, queue: queue.Queue, queue_name: str, msg: str) -> None:
    if verbosity >= 3:
        eprint(queue_name, ":", msg)
    queue.put(msg)

class CoqLSPyInstance(CoqBackend):
    proc: Any
    stderr_queue: QueuePipe
    messageQueues: Dict[str, queue.Queue]
    endpoint: pylspclient.LspEndpoint
    lsp_client: pylspclient.LspClient

    open_doc: str
    doc_version: int
    doc_sentences: List[str]
    state_dirty: bool
    cached_context: Optional[ProofContext]
    verbosity: int


    def __init__(self, lsp_command: Union[str, List[str]],
                 root_dir: Optional[str] = None, concise: bool = True,
                 timeout: int = 30, set_env: bool = True, verbosity: int = 0,
                 initialFilename: str = "local1.v") -> None:
        if set_env:
            setup_opam_env()
        eprint("Using lsp backend")
        self.verbosity = verbosity
        self.concise = concise
        if isinstance(lsp_command, str):
            lsp_command = [lsp_command]

        self.version_string = subprocess.run(lsp_command + ["--version"],
                                             stdout=subprocess.PIPE,
                                             text=True, check=True).stdout

        full_command = lsp_command + ["--int_backend=Mp"] + (["-D", "0.001"] if self.concise else [])
        loc_string = subprocess.run(["which", "coq-lsp"], stdout=subprocess.PIPE,
                                    text=True, check=True).stdout
        eprint(f"Coq lsp is at {loc_string}")
        eprint(f"Running as {full_command}")
        self._proc = subprocess.Popen(full_command,
                                     stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.stderr_queue = QueuePipe(self._proc.stderr)
        self.stderr_queue.start()

        queuedMessages = ['window/logMessage', '$/logTrace',
                          'textDocument/publishDiagnostics']
        printedMessages: List[str] = []
        ignoredMessages = ['$/coq/fileProgress', '$/coq/filePerfData']
        self.messageQueues = {msg_type: queue.Queue() for
                              msg_type in queuedMessages}

        self.endpoint  = pylspclient.LspEndpoint(
            pylspclient.JsonRpcEndpoint(self._proc.stdin, self._proc.stdout),
            notify_callbacks={**{msg_type: cast(Callable[[Any], None],
                                                # functools.partial(queue.Queue.put,
                                                #                   msgqueue))
                                                functools.partial(verbosePut, verbosity,
                                                                  msgqueue, msg_type))
                                 for msg_type, msgqueue in self.messageQueues.items()},
                              **{msg_type: functools.partial(print, msg_type) for msg_type in printedMessages},
                              **{msg_type: lambda x: None for msg_type in ignoredMessages}},
            timeout=timeout)
        self.lsp_client = pylspclient.LspClient(self.endpoint)
        self.root_uri = (os.path.abspath(root_dir) or os.getcwd())
        workspace_folders = [{'name': 'coq-lsp', 'uri': self.root_uri}]
        capabilities: Dict[str, Any] = {}
        init_options = {"verbosity": 1} if self.concise else None
        self.lsp_client.initialize(self._proc.pid, self.root_uri, self.root_uri, init_options,
                                   capabilities,
                                   "off", workspace_folders)
        if not self.concise:
            self.verify_init_messages()
        self.lsp_client.initialized()
        if not self.concise:
            self.checkMessage("$/logTrace", '[process_queue]: Serving Request: initialized')
        self._checkError()

        self.state_dirty = True
        self.doc_sentences = []
        self.openDoc(initialFilename)

    def openDoc(self, filename: str) -> None:
        self.open_doc = filename
        docContents = ""

        self.doc_version = 1
        file_uri = os.path.join(self.root_uri, self.open_doc)
        self.lsp_client.didOpen({"uri": file_uri,
                                 "languageId": "Coq",
                                 "version": self.doc_version,
                                 "text": docContents})
        msgs = [
            r'\[process_queue\]: Serving Request: textDocument/didOpen',
            r'\[process_queue\]: resuming document checking',
            r'\[check\]: resuming(?: \[v: \d+\])?, from: \d+ l: \d+',
            r'\[check\]: done \[\d+\.\d+\]: document fully checked .*',
            r'\[cache\]: hashing: \d+.\d+ | parsing: \d+.\d+ | exec: \d+.\d+',
            r'\[cache\]: .*']
        if not self.concise:
            for msg in msgs:
                self.checkMessagePattern('$/logTrace', msg)
        self._checkError()

    def _checkError(self) -> None:
        severe_errors = []
        try:
            while True: # Keep getting messages until the queue is empty
                error = self.messageQueues['textDocument/publishDiagnostics'].get_nowait()
                if error['version'] < self.doc_version:
                    if len(error['diagnostics']) == 0:
                        continue
                    eprint("Skipping error from an old doc version", guard=self.verbosity >= 2)
                    eprint(f"Error was {error}", guard=self.verbosity >= 3)
                    continue
                for message in error['diagnostics']:
                    if message['severity'] < 2 and message not in severe_errors:
                        assert error["version"] == self.doc_version,\
                            (error["version"], self.doc_version)
                        severe_errors.append(message)
        except queue.Empty as e:
            if len(severe_errors) > 0:
                exceptions = [self._handleError(message)
                              for message in severe_errors]
                raise exceptions[0] from e
            return
    def _handleError(self, message_json: Dict[str, Any]) -> CoqException:
        sentence_num, sentence = self._sentence_at_line(
            message_json['range']['start']['line'])
        eprint("Problem running statement: ", sentence, guard=self.verbosity >= 2)
        if sentence_num < len(self.doc_sentences):
            eprint(f"Rolling back {len(self.doc_sentences) - sentence_num} sentence(s)",
                   guard=self.verbosity >= 2)
            self.doc_sentences = self.doc_sentences[:sentence_num]
        msg_text = message_json['message']
        eprint(msg_text, guard=self.verbosity >= 2)
        return CoqExn(msg_text)

    # Uses 0-based line numbering, so the first line is line 0, the second is
    # line 1, etc.
    def _sentence_at_line(self, line: int) -> Tuple[int, str]:
        cur_line = 0
        for idx, sentence in enumerate(self.doc_sentences):
            sentence_lines = len(sentence.split("\n"))
            cur_line += sentence_lines
            if line < cur_line:
                return (idx, sentence)
        assert False, "Line number is after all the statements we have!"

    def __enter__(self) -> 'CoqLSPyInstance':
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        self.close()

    def close(self) -> None:
        # self.lsp_client.shutdown()
        # self.lsp_client.exit()
        self._proc.terminate()

    def checkMessage(self, queue_name: str, message_text: str):
        message = self.messageQueues[queue_name].get()
        assert message['message'] == message_text, \
            f"Looking for message {repr(message_text)}, got message {repr(message['message'])}"

    def checkInMessage(self, queue_name: str, message_substring: str):
        message = self.messageQueues[queue_name].get()
        assert message_substring in message['message'],\
            f"Couldn't find substring {message_substring} in message {message['message']}"

    def checkMessagePattern(self, queue_name: str, message_pattern: str):
        message = self.messageQueues[queue_name].get()
        assert re.match(message_pattern, message['message']), \
            f"Message {message['message']} doesn't match pattern {message_pattern}"

    def verify_init_messages(self) -> None:
        self.checkInMessage('window/logMessage', "Initializing coq-lsp server") # v0.1.4
        self.checkMessage('window/logMessage', "Server initialized") # v0.1.4

        self.checkInMessage('window/logMessage', "Configuration loaded") # v0.1.4
        root_path = self.root_uri
        expected_msgs = ['[init]: custom client options:',
                         '[init]: [init]: {}',
                         '[client_version]: any',
                         f'[workspace]: initialized {root_path}'] # v0.1.4

        for expected_msg in expected_msgs:
            self.checkMessage("$/logTrace", expected_msg)

    def addStmt(self, stmt: str, timeout:Optional[int] = None,
                force_update_nonfg_goals: bool = False) -> None:
        del force_update_nonfg_goals
        self.addStmt_noupdate(stmt, timeout)
        self.getProofContext()

    def addStmt_noupdate(self, stmt: str, timeout:Optional[int] = None) -> None:
        self.doc_sentences.append(stmt.strip("\n"))
        self.state_dirty = True

    def cancelLastStmt(self, cancelled: str, force_update_nonfg_goals: bool = False) -> None:
        del force_update_nonfg_goals
        self.doc_sentences.pop()
        self.state_dirty = True
    def cancelLastStmt_noupdate(self, cancelled: str) -> None:
        self.cancelLastStmt(cancelled)

    def updateState(self) -> None:
        pass

    def sendNewDoc(self) -> None:
        doc = "\n".join(self.doc_sentences)
        file_uri = os.path.join(self.root_uri, self.open_doc)
        self.doc_version += 1
        self.lsp_client.didChange(
            {"uri": file_uri,
             "version": self.doc_version},
            [{"text": doc}])

    def expectDidChangeResponse(self, anomaly_on_timeout: bool = False) -> None:
        if not self.concise:
            file_uri = os.path.join(self.root_uri, self.open_doc)
            msgs = [
                r'\[process_queue\]: Serving Request: textDocument/didChange',
                fr'\[bump file\]: {file_uri} / version: {self.doc_version}',
                r'\[bump file took\]: \d+\.\d+',
                r'\[process_queue\]: resuming document checking',
                r'\[check\]: resuming(?: \[v: \d+\])?, from: \d+ l: \d+',
                r'\[check\]: done \[\d+\.\d+\]: document .*',
                r'\[cache\]: hashing: \d+.\d+ | parsing: \d+.\d+ | exec: \d+.\d+',
                r'\[cache\]: .*',
                ]
            optional_msgs = [
                r'\[resume\]: last node .*',
                r'\[prefix\]: common prefix offset found at \d+',
                r'\[prefix\]: resuming from .*',
            ]
            for expected_msg_pattern in msgs:
                while True:
                    try:
                        actual_message = self.messageQueues["$/logTrace"].get(timeout=10)['message']
                    except queue.Empty:
                        if anomaly_on_timeout:
                            raise CoqAnomaly("Timing out")
                        self._handle_timeout()
                    if any(re.match(optional_msg_pattern, actual_message)
                           for optional_msg_pattern in optional_msgs):
                        continue
                    else:
                        assert re.match(expected_msg_pattern, actual_message), f"Message {actual_message} didn't match pattern {expected_msg_pattern}"
                        break

    def _getContext(self, anomaly_on_timeout: bool = False) -> Optional[ProofContext]:
        file_uri = os.path.join(self.root_uri, self.open_doc)
        doc = "\n".join(self.doc_sentences)
        line = len(doc.split("\n")) - 1
        character = len(doc.split("\n")[-1]) if len(doc) > 0 else 0
        try:
            response = self.endpoint.call_method(
                "proof/goals", textDocument={"uri": file_uri},
                position={"line": line,
                          "character": character})
        except TimeoutError:
            if anomaly_on_timeout:
                raise CoqAnomaly("Timing out")
            self._handle_timeout()
        parsed_response = parseGoalResponse(response)
        if not self.concise:
            self.checkMessage("$/logTrace", "[process_queue]: Serving Request: proof/goals")
            self.checkMessagePattern("$/logTrace", "\[serving\]: .*")
        return parsed_response

    def getProofContext(self, anomaly_on_timeout: bool = False) -> Optional[ProofContext]:
        if not self.state_dirty:
            return self.cached_context
        self.sendNewDoc()
        self.expectDidChangeResponse(anomaly_on_timeout)
        parsed_response = self._getContext(anomaly_on_timeout)
        self._checkError()
        self.cached_context = parsed_response
        self.state_dirty = False
        return self.cached_context
    def getSexpProofContext(self) -> List[SexpObligation]:
        return [SexpObligation([], []) for _ in
                unwrap(self.getProofContext()).all_goals]

    def _handle_timeout(self) -> None:
        self._checkError()
        eprint("Rolling back 1 sentence for timeout",
               guard=self.verbosity >= 2)
        self.doc_sentences = self.doc_sentences[:-1]

        # self.sendNewDoc()
        # if not self.concise:
        #     msg_pats = [r"\[check\]: done \[\d+\.\d+\]: document stopped with pos .*",
        #                 r"\[cache\]: hashing: \d+.\d+ | parsing: \d+.\d+ | exec: \d+.\d+",
        #                 r'\[cache\]: .*']
        #     for msg_pat in msg_pats:
        #         self.checkMessagePattern("$/logTrace", msg_pat)
        # self.expectDidChangeResponse()
        # parsed_response = self._getContext()
        # self._checkError()
        # self.cached_context = parsed_response
        raise CoqTimeoutError("Timing out getting context")

    def isInProof(self) -> bool:
        return self.getProofContext() is not None

    def queryVernac(self, vernac: str) -> List[str]:
        raise NotImplementedError()
    def interrupt(self) -> None:
        raise NotImplementedError()
    def resetCommandState(self) -> None:
        self.doc_version += 1
        self.doc_sentences = []
        self.state_dirty = True
    def setFilename(self, filename: str) -> None:
        return
        # self.openDoc(filename)
    @property
    def cur_state(self) -> int:
        return len(self.doc_sentences)
    def backToState(self, state_num: int) -> None:
        self.doc_sentences = self.doc_sentences[:state_num]
        self.state_dirty = True
    def backToState_noupdate(self, state_num: int) -> None:
        self.backToState(state_num)
    def coq_minor_version(self) -> int:
        format_match = re.match("\d+\.\d+\.\d+-(.*)", self.version_string)
        assert format_match
        coq_version_string = format_match.group(1)
        if coq_version_string == "dev":
            return 20
        version_parts_match = re.match("\d+\.(\d+).*", coq_version_string)
        assert version_parts_match
        return int(version_parts_match.group(1))


def parseObligation(obl_obj: Dict[str, Any]) -> Obligation:
    return Obligation([
        ", ".join(hyp_obj["names"]) + " : " + hyp_obj["ty"]
        for hyp_obj in obl_obj["hyps"]],
                      obl_obj["ty"])

def parseGoalResponse(response: Dict[str, Any]) -> Optional[ProofContext]:
    if "goals" not in response or response["goals"] is None:
        return None
    goals = response["goals"]
    return ProofContext([parseObligation(obl_obj)
                         for obl_obj in goals["goals"]],
                        [parseObligation(obl_obj)
                         for stack in goals["stack"]
                         for substack in stack
                         for obl_obj in substack],
                        [parseObligation(obl_obj)
                         for obl_obj in goals["shelf"]],
                        [parseObligation(obl_obj)
                         for obl_obj in goals["given_up"]])

def main():

    with CoqLSPyInstance("cd $HOME/research/coq-lsp && dune exec -- coq-lsp") as coq:
        print(coq.getProofContext())
        coq.addStmt("Theorem nat_refl : forall n : nat, n= n.")
        coq.addStmt("Proof.")
        coq.addStmt("intro.")
        print(coq.getProofContext())
        coq.cancelLastStmt()
        print(coq.getProofContext())
        coq.addStmt("induction n.")
        coq.addStmt("{")
        print(coq.getProofContext())


# Run main if this module is being run standalone
if __name__ == "__main__":
    main()
