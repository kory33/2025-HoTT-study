#!/bin/bash
set -eux

# Create skills directory if it doesn't exist
mkdir -p "${HOME}/.claude/skills"

# Register pinned agda-stdlib in the user's Agda config.
bash /workspace/.devcontainer/register-agda-stdlib.sh /workspace/agda-toolchain.env "${HOME}/.agda"
