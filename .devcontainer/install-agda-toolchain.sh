#!/bin/bash
set -euo pipefail

# This script installs Agda and agda-stdlib from official release archives.
# After running this script, Agda and agda-stdlib will have been installed
#   at /opt/agda and /opt/agda-stdlib respectively, and the 'agda' executable will
#   be symlinked from /usr/local/bin. Permissions will be set so that the installed files
#   are writable by the current (or SUDO_USER if running with sudo) user.
# The script is intended to run as root (Docker build stage or sudo in CI).

TOOLCHAIN_FILE="${1:-/tmp/agda-toolchain.env}"
if [[ ! -f "${TOOLCHAIN_FILE}" ]]; then
    echo "Toolchain file '${TOOLCHAIN_FILE}' does not exist." >&2
    exit 1
fi

# shellcheck source=/dev/null
source "${TOOLCHAIN_FILE}"

: "${AGDA_VERSION:?AGDA_VERSION is required in ${TOOLCHAIN_FILE}}"
: "${AGDA_STDLIB_VERSION:?AGDA_STDLIB_VERSION is required in ${TOOLCHAIN_FILE}}"

if [[ "${EUID}" -ne 0 ]]; then
    echo "This script must be run as root (use sudo in CI)." >&2
    exit 1
fi

AGDA_INSTALL_ROOT="/opt/agda"
AGDA_STDLIB_ROOT="/opt/agda-stdlib"
AGDA_BIN_DIR="/usr/local/bin"

if [[ "$(uname -s)" != "Linux" ]]; then
    echo "Unsupported OS: $(uname -s). Only Linux is currently supported by this script." >&2
    exit 1
fi

case "$(uname -m)" in
    x86_64 | amd64)
        AGDA_RELEASE_ASSET_REGEX="^Agda-v?${AGDA_VERSION//./\\.}-linux.*\\.tar\\.xz$"
        ;;
    *)
        echo "Unsupported architecture: $(uname -m). Only x86_64/amd64 is currently supported." >&2
        exit 1
        ;;
esac

AGDA_DIST_URL="$(
    jq -r --arg pattern "${AGDA_RELEASE_ASSET_REGEX}" \
            '.assets[] | select(.name | test($pattern)) | .browser_download_url' \
            <<<"$(curl -fsSL "https://api.github.com/repos/agda/agda/releases/tags/v${AGDA_VERSION}")" \
        | head -n1
)"

if [[ -z "${AGDA_DIST_URL}" || "${AGDA_DIST_URL}" == "null" ]]; then
    echo "Could not find an official Linux binary asset for Agda v${AGDA_VERSION}." >&2
    echo "Expected regex: ${AGDA_RELEASE_ASSET_REGEX}" >&2
    exit 1
fi

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "${TMP_DIR}"' EXIT

AGDA_INSTALL_DIR="${AGDA_INSTALL_ROOT%/}/${AGDA_VERSION}"
rm -rf "${AGDA_INSTALL_DIR}"
mkdir -p "${AGDA_INSTALL_DIR}/bin"

curl -fsSL "${AGDA_DIST_URL}" -o "${TMP_DIR}/agda.tar.xz"
tar -xJf "${TMP_DIR}/agda.tar.xz" -C "${TMP_DIR}"

if [[ ! -f "${TMP_DIR}/agda" ]]; then
    echo "Unexpected Agda archive layout: expected a top-level 'agda' executable." >&2
    exit 1
fi

install -m 0755 "${TMP_DIR}/agda" "${AGDA_INSTALL_DIR}/bin/agda"

ln -sfn "${AGDA_INSTALL_DIR}/bin/agda" "${AGDA_BIN_DIR}/agda"

if ! "${AGDA_BIN_DIR}/agda" --version | head -n1 | grep -Fx "Agda version ${AGDA_VERSION}" >/dev/null; then
    echo "Installed Agda binary is not reporting version ${AGDA_VERSION}." >&2
    exit 1
fi

# Install the standard library

mkdir -p "${AGDA_STDLIB_ROOT}"
STDLIB_INSTALL_DIR="${AGDA_STDLIB_ROOT%/}/agda-stdlib-${AGDA_STDLIB_VERSION}"
rm -rf "${STDLIB_INSTALL_DIR}"

curl -fsSL "https://github.com/agda/agda-stdlib/archive/refs/tags/v${AGDA_STDLIB_VERSION}.tar.gz" \
    -o "${TMP_DIR}/stdlib.tar.gz"
tar -xzf "${TMP_DIR}/stdlib.tar.gz" -C "${AGDA_STDLIB_ROOT}"

if [[ ! -d "${STDLIB_INSTALL_DIR}/src" ]]; then
    echo "Expected standard library directory '${STDLIB_INSTALL_DIR}/src' is missing." >&2
    exit 1
fi

# Agda may create a '_build' directory under the stdlib root during typechecking.
# If the script is invoked with sudo, transfer stdlib ownership back to the caller.
if [[ -n "${SUDO_USER:-}" ]] && [[ "${SUDO_USER}" != "root" ]]; then
    if id "${SUDO_USER}" >/dev/null 2>&1; then
        chown -R "${SUDO_USER}:${SUDO_USER}" "${STDLIB_INSTALL_DIR}"
    fi
fi
