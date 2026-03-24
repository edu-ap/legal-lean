FROM ubuntu:24.04

LABEL maintainer="Eduardo Aguilar Pelaez <e.aguilar@imperial.ac.uk>"
LABEL description="Independent verification environment for LegalLean"

# Avoid interactive prompts during build
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      curl ca-certificates git && \
    rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
    sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Copy the project
WORKDIR /workspace
COPY . .

# Install the correct Lean toolchain (from lean-toolchain file)
RUN elan install $(cat lean-toolchain)

# Build and verify
RUN echo "=== BUILDING ===" && \
    lake build 2>&1 && \
    echo "" && \
    echo "=== VERIFICATION ===" && \
    echo "Modules compiled: $(find .lake/build -name '*.olean' | wc -l)" && \
    echo "" && \
    echo "Sorry stubs:" && \
    SORRY_COUNT=$(grep -r '\bsorry\b' LegalLean/ --include='*.lean' -l | wc -l) && \
    echo "  Files with sorry: $SORRY_COUNT" && \
    if [ "$SORRY_COUNT" -gt 0 ]; then \
      echo "  FAIL: Found sorry stubs:"; \
      grep -rn '\bsorry\b' LegalLean/ --include='*.lean'; \
      exit 1; \
    fi && \
    echo "  PASS: Zero sorry stubs" && \
    echo "" && \
    echo "Theorems proven:" && \
    grep -r '^theorem' LegalLean/ --include='*.lean' | wc -l && \
    echo "" && \
    echo "Open-texture axioms (intentional, not sorry):" && \
    grep -r '^axiom' LegalLean/ --include='*.lean' | wc -l && \
    echo "" && \
    echo "=== ALL CHECKS PASSED ==="

# Default command: re-run verification
CMD ["sh", "-c", "lake build && echo 'Build: PASS' && grep -r '\\bsorry\\b' LegalLean/ --include='*.lean' -l | wc -l | xargs -I{} sh -c 'if [ {} -gt 0 ]; then echo Sorry: FAIL; exit 1; else echo Sorry: PASS; fi' && echo 'Theorems:' && grep -r '^theorem' LegalLean/ --include='*.lean' | wc -l"]
