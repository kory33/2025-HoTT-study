#!/bin/bash
set -euo pipefail

# Register pinned agda-stdlib as 'standard-library' in Agda's package config.
#
# Usage:
#   register-agda-stdlib.sh [TOOLCHAIN_FILE] [AGDA_CONFIG_DIR]
#
# Defaults:
#   TOOLCHAIN_FILE=/workspace/agda-toolchain.env
#   AGDA_CONFIG_DIR=$HOME/.agda

TOOLCHAIN_FILE="${1:-/workspace/agda-toolchain.env}"
AGDA_CONFIG_DIR="${2:-${HOME}/.agda}"
AGDA_STDLIB_ROOT="${AGDA_STDLIB_ROOT:-/opt/agda-stdlib}"

if [[ ! -f "${TOOLCHAIN_FILE}" ]]; then
    echo "Toolchain file '${TOOLCHAIN_FILE}' not found." >&2
    exit 1
fi

# shellcheck source=/dev/null
source "${TOOLCHAIN_FILE}"
: "${AGDA_STDLIB_VERSION:?AGDA_STDLIB_VERSION is required in ${TOOLCHAIN_FILE}}"

STDLIB_SOURCE_DIR="${AGDA_STDLIB_ROOT%/}/agda-stdlib-${AGDA_STDLIB_VERSION}/src"
if [[ ! -d "${STDLIB_SOURCE_DIR}" ]]; then
    echo "Expected standard library source directory '${STDLIB_SOURCE_DIR}' not found." >&2
    exit 1
fi

STANDARD_LIBRARY_LIB="${AGDA_CONFIG_DIR}/standard-library.agda-lib"
mkdir -p "${AGDA_CONFIG_DIR}"

cat > "${STANDARD_LIBRARY_LIB}" <<EOF
name: standard-library
include: ${STDLIB_SOURCE_DIR}
EOF

touch "${AGDA_CONFIG_DIR}/libraries"
if ! grep -Fxq "${STANDARD_LIBRARY_LIB}" "${AGDA_CONFIG_DIR}/libraries"; then
    printf '%s\n' "${STANDARD_LIBRARY_LIB}" >> "${AGDA_CONFIG_DIR}/libraries"
fi

touch "${AGDA_CONFIG_DIR}/defaults"
if ! grep -Fxq "standard-library" "${AGDA_CONFIG_DIR}/defaults"; then
    printf '%s\n' "standard-library" >> "${AGDA_CONFIG_DIR}/defaults"
fi
