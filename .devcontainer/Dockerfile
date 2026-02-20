FROM mcr.microsoft.com/devcontainers/base:2-bookworm@sha256:23fa69fed758b7927c60061317d73baf7d66b9fca5c344e80bce3a940b229af0

ARG USERNAME=vscode

# Add keyring for GitHub CLI and install tools
RUN mkdir -p -m 755 /etc/apt/keyrings \
	&& out=$(mktemp) && wget -nv -O$out https://cli.github.com/packages/githubcli-archive-keyring.gpg \
	&& cat $out | tee /etc/apt/keyrings/githubcli-archive-keyring.gpg > /dev/null \
	&& chmod go+r /etc/apt/keyrings/githubcli-archive-keyring.gpg \
	&& mkdir -p -m 755 /etc/apt/sources.list.d \
	&& echo "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | sudo tee /etc/apt/sources.list.d/github-cli.list > /dev/null \
    && apt-get update && apt-get install -y --no-install-recommends \
         dos2unix \
         ripgrep \
         gh \
         agda-bin \
         agda-stdlib \
    && rm -rf /var/lib/apt/lists/*

# Install Codex
RUN wget https://github.com/openai/codex/releases/download/rust-v0.104.0/codex-x86_64-unknown-linux-musl.tar.gz -O /tmp/codex.tar.gz && \
  tar -xvf /tmp/codex.tar.gz -C /usr/local/bin/ && \
  rm /tmp/codex.tar.gz && \
  mv /usr/local/bin/codex-x86_64-unknown-linux-musl /usr/local/bin/codex && \
  chmod +x /usr/local/bin/codex

# Used to persist bash history as per https://code.visualstudio.com/remote/advancedcontainers/persist-bash-history
RUN SNIPPET="export PROMPT_COMMAND='history -a' && export HISTFILE=/commandhistory/.bash_history" \
    && mkdir /commandhistory \
    && touch /commandhistory/.bash_history \
    && chown -R $USERNAME /commandhistory \
    && echo "$SNIPPET" >> "/home/$USERNAME/.bashrc"

# Claude configuration files
RUN mkdir /home/$USERNAME/.claude && chown -R $USERNAME /home/$USERNAME/.claude
# Codex configuration files
RUN mkdir /home/$USERNAME/.codex && chown -R $USERNAME /home/$USERNAME/.codex

# Use with caution.
# The devcontainer may contain Claude credentials so this is not entirely safe.
RUN echo "alias claude-yolo='claude --dangerously-skip-permissions'" >> /etc/bash.bashrc
RUN echo "alias codex-yolo='codex --dangerously-bypass-approvals-and-sandbox'" >> /etc/bash.bashrc
