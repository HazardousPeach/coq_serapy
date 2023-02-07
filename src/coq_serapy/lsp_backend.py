#!/usr/bin/env python

import threading
import subprocess
import re
import os
import queue
import functools

from typing import Any, Dict, List, cast, Callable

import pylspclient

from .contexts import ProofContext, Obligation

class QueuePipe(threading.Thread):

    def __init__(self, pipe):
        threading.Thread.__init__(self)
        self.pipe = pipe
        self.queue = queue.Queue()

    def run(self):
        line = self.pipe.readline().decode('utf-8')
        while line:
            self.queue.put(line)
            line = self.pipe.readline().decode('utf-8')
    def get(self) -> str:
        return self.queue.get()

class CoqLSPyInstance:
    server_version: str
    proc: Any
    stderr_queue: QueuePipe
    messageQueues: Dict[str, queue.Queue]
    endpoint: pylspclient.LspEndpoint
    lsp_client: pylspclient.LspClient

    open_doc: str
    doc_version: int
    doc_sentences: List[str]
    state_dirty: bool
    cached_context: ProofContext


    def __init__(self, lsp_command: str, server_version: str) -> None:
        setup_opam_env()
        self.proc = subprocess.Popen(lsp_command, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     shell=True)
        self.stderr_queue = QueuePipe(self.proc.stderr)
        self.stderr_queue.start()
        self.server_version = server_version

        queuedMessages = ['window/logMessage', '$/logTrace']
        printedMessages: List[str] = []
        ignoredMessages = ['$/coq/fileProgress',
                            'textDocument/publishDiagnostics']
        self.messageQueues = {msg_type: queue.Queue() for
                              msg_type in queuedMessages}

        self.endpoint  = pylspclient.LspEndpoint(
            pylspclient.JsonRpcEndpoint(self.proc.stdin, self.proc.stdout),
            notify_callbacks={**{msg_type: cast(Callable[[Any], None],
                                                functools.partial(queue.Queue.put,
                                                                  msgqueue))
                                 for msg_type, msgqueue in self.messageQueues.items()},
                              **{msg_type: functools.partial(print, msg_type) for msg_type in printedMessages},
                              **{msg_type: lambda x: None for msg_type in ignoredMessages}})
        self.lsp_client = pylspclient.LspClient(self.endpoint)
        root_uri = '.'
        workspace_folders = [{'name': 'coq-lsp', 'uri': root_uri}]
        capabilities: Dict[str, Any] = {}
        self.lsp_client.initialize(self.proc.pid, '.', root_uri, None,
                                   capabilities,
                                   "off", workspace_folders)
        self.verify_init_messages()
        self.lsp_client.initialized()
        self.checkMessage("$/logTrace", '[process_queue]: Serving Request: initialized')

        self.state_dirty = True
        self.doc_sentences = []
        self._openEmptyDoc()

    def _openEmptyDoc(self) -> None:
        docContents = "\n".join(self.doc_sentences)
        self.open_doc = "local:1"


        self.doc_version = 1
        self.lsp_client.didOpen({"uri": self.open_doc,
                                 "languageId": "Coq",
                                 "version": self.doc_version,
                                 "text": docContents})
        msgs = [
            r'\[process_queue\]: Serving Request: textDocument/didOpen',
            r'\[process_queue\]: resuming document checking',
            r'\[check\]: resuming(?: \[v: \d+\])?, from: 0 l: \d+',
            r'\[check\]: done \[\d+\.\d+\]: document fully checked .*',
            r'\[cache\]: hashing: \d+.\d+ | parsing: \d+.\d+ | exec: \d+.\d+',
            r'\[cache\]: .*'] # v0.01
        for msg in msgs:
            self.checkMessagePattern('$/logTrace', msg)

    def __enter__(self) -> 'CoqLSPyInstance':
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        self.lsp_client.shutdown()
        self.lsp_client.exit()
        self.proc.terminate()

    def checkMessage(self, queue_name: str, message_text: str):
        message = self.messageQueues[queue_name].get()
        assert message['message'] == message_text, \
            f"Looking for message {message_text}, got message {message['message']}"

    def checkInMessage(self, queue_name: str, message_substring: str):
        message = self.messageQueues[queue_name].get()
        assert message_substring in message['message'],\
            f"Couldn't find substring {message_substring} in message {message['message']}"

    def checkMessagePattern(self, queue_name: str, message_pattern: str):
        message = self.messageQueues[queue_name].get()
        assert re.match(message_pattern, message['message']), \
            f"Message {message['message']} doesn't match pattern {message_pattern}"

    def verify_init_messages(self) -> None:
        if self.server_version == "0.01":
            self.checkMessage('window/logMessage', "Server started") # v0.01
            self.checkInMessage('window/logMessage', "Configuration loaded") # v0.01
            expected_msgs = ['[process_queue]: Serving Request: initialize',
                             '[init]: custom client options:',
                             '[init]: [init]: {}',
                             '[version]: any',
                             '[init]: client capabilities:',
                             '[init]: [init]: {}'] # v0.01
        else:
            assert self.server_version == "0.1.4"

            self.checkMessage('window/logMessage', "Initializing server") # v0.1.4
            self.checkMessage('window/logMessage', "Server initialized") # v0.1.4

            self.checkInMessage('window/logMessage', "Configuration loaded") # v0.1.4
            expected_msgs = ['[init]: custom client options:',
                             '[init]: [init]: {}',
                             '[client_version]: any',
                             '[workspace]: initialized'] # v0.1.4

        for expected_msg in expected_msgs:
            self.checkMessage("$/logTrace", expected_msg)

    def addStmt(self, stmt: str) -> None:
        self.doc_sentences.append(stmt.rstrip("\n"))
        self.state_dirty = True

    def cancelLastStmt(self) -> None:
        self.doc_sentences.pop()
        self.state_dirty = True

    def getProofContext(self) -> ProofContext:
        if not self.state_dirty:
            return self.cached_context

        doc = "\n".join(self.doc_sentences)
        self.doc_version += 1
        self.lsp_client.didChange(
            {"uri": self.open_doc,
             "version": self.doc_version},
            [{"text": doc}])
        response = self.endpoint.call_method(
            "proof/goals", textDocument={"uri": self.open_doc},
            position={"line": len(self.doc_sentences),
                      "character": len(self.doc_sentences[-1])})
        self.cached_context = self.parseGoalResponse(response)
        self.state_dirty = False
        return self.cached_context

    def parseObligation(self, obl_obj: Dict[str, Any]) -> Obligation:
        return Obligation([
            ", ".join(hyp_obj["names"]) + " : " + hyp_obj["ty"]
            for hyp_obj in obl_obj["hyps"]],
                          obl_obj["ty"])

    def parseGoalResponse(self, response: Dict[str, Any]) -> ProofContext:
        goals = response["goals"]
        return ProofContext([self.parseObligation(obl_obj)
                             for obl_obj in goals["goals"]],
                            [],
                            [self.parseObligation(obl_obj)
                             for obl_obj in goals["shelf"]],
                            [self.parseObligation(obl_obj)
                             for obl_obj in goals["given_up"]])

def setup_opam_env() -> None:
    env_string = subprocess.run(f"opam env", shell=True, stdout=subprocess.PIPE,
                                text=True, check=True).stdout
    _setup_opam_env_from_str(env_string)


def _setup_opam_env_from_str(env_string: str) -> None:
    for env_line in env_string.splitlines():
        linematch = re.fullmatch(r"(\w*)='([^;]*)'; export (\w*);", env_line)
        assert linematch, env_line
        envvar = linematch.group(1)
        assert envvar == linematch.group(3)
        envval = linematch.group(2)
        os.environ[envvar] = envval

def logTrace(message_queue, params):
    message_queue.put(params)
    pass

def main():

    with CoqLSPyInstance("cd $HOME/research/coq-lsp && dune exec -- coq-lsp",
                         "0.1.4") as coq:
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
