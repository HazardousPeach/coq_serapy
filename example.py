
import coq_serapy


# A main function demonstrating some of the features of the coq_serapy module

# To properly run this example, you need Coq installed (versions 8.9-8.12) and
# Coq Serapi installed. Then, copy this into the folder *above* the coq_serapy
# module.
def main():

    with coq_serapy.SerapiContext(
            # How you want the underlying sertop binary to be run. If not sure,
            # use this.
            ["sertop", "--implicit"],
            # A top level module for the code to reside in. Empty string or
            # None leaves in the default top module.
            "MyModule",
            # A prelude directory in which to start the binary
            ".") as coq:
        proof_commands = [
            "Theorem t: forall n: nat, 1 + n > n.",
            "Proof.",
            "intro.",
            "omega.",
            "Qed."]

        # Runs commands from a list until we enter a proof, then returns a
        # tuple of (commands-left-over, commands-that-were-run)
        cmds_left, cmds_run = coq.run_into_next_proof(
            proof_commands)
        assert cmds_run == ["Theorem t: forall n: nat, 1 + n > n."]
        assert cmds_left == [
            "Proof.",
            "intro.",
            "omega.",
            "Qed."], cmds_left

        # Print out the proof context
        print(coq.proof_context)

        # Setting this makes sure that coq doesn't print extra on failed
        # commands.
        coq.quiet = True

        try:
            _, _ = coq.finish_proof(cmds_left)
        except coq_serapy.CoqExn:
            # Oops! We forgot to import omega."
            # Back out of the proof and import it.
            while coq.proof_context:
                coq.cancel_last()
            coq.run_stmt("Require Import Omega.")
            cmds_left, cmds_run = coq.run_into_next_proof(proof_commands)
            # Now it should finish fine
            _, _ = coq.finish_proof(cmds_left)


# Run main if this module is being run standalone
if __name__ == "__main__":
    main()
