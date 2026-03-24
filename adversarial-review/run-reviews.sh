#!/usr/bin/env bash
# Run adversarial LLM reviews in parallel using tmux sessions.
#
# Usage:
#   ./adversarial-review/run-reviews.sh          # run both Gemini + Codex
#   ./adversarial-review/run-reviews.sh gemini    # run Gemini only
#   ./adversarial-review/run-reviews.sh codex     # run Codex only
#   ./adversarial-review/run-reviews.sh status    # check progress
#
# Reviews are saved to:
#   adversarial-review/gemini-review.md
#   adversarial-review/codex-review.md

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
PROMPT_FILE="$SCRIPT_DIR/prompt.md"
GEMINI_OUTPUT="$SCRIPT_DIR/gemini-review.md"
CODEX_OUTPUT="$SCRIPT_DIR/codex-review.md"
COMBINED_INPUT="$SCRIPT_DIR/.combined-input.md"

# Files to feed to the reviewers
FILES=(
  "LegalLean/Core.lean"
  "LegalLean/CaseStudies/IRC163h.lean"
  "LegalLean/CaseStudies/IRC163h/Theorems.lean"
  "LegalLean/CaseStudies/O1Visa.lean"
  "LegalLean/CaseStudies/TCPCode.lean"
  "monograph/verified-legal-reasoning.md"
)

SESSION_GEMINI="legallean-gemini-review"
SESSION_CODEX="legallean-codex-review"

# Build combined prompt + files into a single markdown file
build_combined_input() {
    {
        cat "$PROMPT_FILE"
        echo ""
        echo "---"
        echo ""
        echo "# SOURCE FILES"
        echo ""
        for f in "${FILES[@]}"; do
            echo "## File: $f"
            echo ""
            echo '```lean'
            cat "$REPO_DIR/$f"
            echo '```'
            echo ""
        done
    } > "$COMBINED_INPUT"
    echo "Combined input: $(wc -l < "$COMBINED_INPUT") lines, $(wc -c < "$COMBINED_INPUT" | tr -d ' ') bytes"
}

run_gemini() {
    echo "[$(date '+%H:%M:%S')] Starting Gemini review..."
    build_combined_input

    # Kill existing session if any
    tmux kill-session -t "$SESSION_GEMINI" 2>/dev/null || true

    # Gemini CLI: pipe combined input via stdin, use -p for headless mode
    tmux new-session -d -s "$SESSION_GEMINI" \
        "cd $REPO_DIR && echo '=== GEMINI ADVERSARIAL REVIEW ===' > $GEMINI_OUTPUT && echo 'Started: $(date)' >> $GEMINI_OUTPUT && echo '---' >> $GEMINI_OUTPUT && echo '' >> $GEMINI_OUTPUT && cat $COMBINED_INPUT | gemini -p 'Please review the following paper and code according to the instructions at the top of this document.' >> $GEMINI_OUTPUT 2>&1; echo '' >> $GEMINI_OUTPUT; echo '---' >> $GEMINI_OUTPUT; echo 'Completed: $(date)' >> $GEMINI_OUTPUT; echo '[DONE] Gemini review complete'"

    echo "  Session: tmux attach -t $SESSION_GEMINI"
    echo "  Output:  $GEMINI_OUTPUT"
}

run_codex() {
    echo "[$(date '+%H:%M:%S')] Starting Codex review..."
    build_combined_input

    # Kill existing session if any
    tmux kill-session -t "$SESSION_CODEX" 2>/dev/null || true

    # Codex CLI: use 'exec' subcommand, read prompt from stdin via '-'
    tmux new-session -d -s "$SESSION_CODEX" \
        "cd $REPO_DIR && echo '=== CODEX ADVERSARIAL REVIEW ===' > $CODEX_OUTPUT && echo 'Started: $(date)' >> $CODEX_OUTPUT && echo '---' >> $CODEX_OUTPUT && echo '' >> $CODEX_OUTPUT && cat $COMBINED_INPUT | codex exec - >> $CODEX_OUTPUT 2>&1; echo '' >> $CODEX_OUTPUT; echo '---' >> $CODEX_OUTPUT; echo 'Completed: $(date)' >> $CODEX_OUTPUT; echo '[DONE] Codex review complete'"

    echo "  Session: tmux attach -t $SESSION_CODEX"
    echo "  Output:  $CODEX_OUTPUT"
}

check_status() {
    echo "=== Adversarial Review Status ==="
    echo ""

    for name in gemini codex; do
        local session_var="SESSION_${name^^}"
        local output_var="${name^^}_OUTPUT"
        local session="${!session_var}"
        local output="${!output_var}"

        if tmux has-session -t "$session" 2>/dev/null; then
            local lines=0
            [ -f "$output" ] && lines=$(wc -l < "$output")
            echo "$name: RUNNING ($lines lines so far) -- tmux attach -t $session"
        elif [ -f "$output" ] && grep -q "Completed:" "$output" 2>/dev/null; then
            local lines
            lines=$(wc -l < "$output")
            echo "$name: COMPLETE ($lines lines)"
            # Show first substantive line as preview
            grep -m1 "^##\|^[0-9]\.\|Strong\|Accept\|Reject\|Borderline" "$output" 2>/dev/null | head -1 | sed 's/^/  Preview: /'
        elif [ -f "$output" ]; then
            local lines
            lines=$(wc -l < "$output")
            echo "$name: PARTIAL ($lines lines, may have errored)"
        else
            echo "$name: NOT STARTED"
        fi
    done
}

# Main
case "${1:-both}" in
    gemini)  run_gemini ;;
    codex)   run_codex ;;
    both)
        run_gemini
        echo ""
        run_codex
        echo ""
        echo "Both reviews running. Check: ./adversarial-review/run-reviews.sh status"
        ;;
    status)  check_status ;;
    *)
        echo "Usage: $0 [both|gemini|codex|status]"
        exit 1
        ;;
esac
