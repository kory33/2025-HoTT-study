#!/bin/bash
set -eux

# Create skills directory if it doesn't exist
mkdir -p "${HOME}/.claude/skills"

# Register the system-installed Agda standard library.
AGDA_CONFIG_DIR="${HOME}/.agda"
STANDARD_LIBRARY_LIB="${AGDA_CONFIG_DIR}/standard-library.agda-lib"
mkdir -p "${AGDA_CONFIG_DIR}"

cat > "${STANDARD_LIBRARY_LIB}" <<'EOF'
name: standard-library
include: /usr/share/agda-stdlib
EOF

touch "${AGDA_CONFIG_DIR}/libraries"
if ! grep -Fxq "${STANDARD_LIBRARY_LIB}" "${AGDA_CONFIG_DIR}/libraries"; then
    printf '%s\n' "${STANDARD_LIBRARY_LIB}" >> "${AGDA_CONFIG_DIR}/libraries"
fi

touch "${AGDA_CONFIG_DIR}/defaults"
if ! grep -Fxq "standard-library" "${AGDA_CONFIG_DIR}/defaults"; then
    printf '%s\n' "standard-library" >> "${AGDA_CONFIG_DIR}/defaults"
fi
