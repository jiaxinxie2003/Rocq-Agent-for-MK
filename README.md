
## Files Description

### `RocqAgent.py`

`RocqAgent.py` is the main implementation of the intelligent agent.

The agent provides the following capabilities:

- Automatic analysis of Rocq proof tasks
- Interaction with Rocq compilation tools
- Generation and modification of Rocq proof scripts
- Error feedback analysis and proof refinement
- Iterative proof search and verification

The agent adopts a verification-driven workflow: generated proofs are continuously checked by Rocq, and compilation errors are used as feedback for subsequent refinement.

### `mk_admit.v`

`mk_admit.v` is an MK axiomatic set theory formalization file completed with the assistance of RocqAgent.

Starting from incomplete proof states, the agent automatically generated and refined the corresponding Rocq proof scripts until all target theorems were successfully verified by the Rocq compiler.

This file demonstrates the capability of RocqAgent in handling large-scale formalization tasks in mathematical logic.

## Requirements

- Python 3.14
- Rocq Proof Assistant
- A compatible LLM API (OpenAI-compatible interface)

Recommended environment:

- Rocq 9.0.1
- VS Code with Rocq language support

## Usage

1. Install the required dependencies and configure the LLM API.

2. Run the intelligent agent:

```bash
python RocqAgent.py
