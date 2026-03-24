# Adversarial LLM Review Protocol

This directory contains instructions for running independent adversarial reviews of the LegalLean paper using frontier LLMs. Each reviewer runs independently and writes feedback to a separate file.

## Purpose

Layer 3 of the VERIFICATION.md protocol: reproducible peer review by AI systems. The reviews are NOT meant to replace human review but to surface weaknesses that the authors may have missed.

## How to Run

### Option 1: Gemini 3 via Vertex AI (recommended)

```bash
# From the legal-lean repo root
gemini -p "$(cat adversarial-review/prompt.md)" \
  -f LegalLean/Core.lean \
  -f LegalLean/CaseStudies/IRC163h.lean \
  -f LegalLean/CaseStudies/IRC163h/Theorems.lean \
  -f LegalLean/CaseStudies/O1Visa.lean \
  -f monograph/verified-legal-reasoning.md \
  > adversarial-review/gemini-review.md
```

### Option 2: OpenAI Codex CLI

```bash
codex -p "$(cat adversarial-review/prompt.md)" \
  --files LegalLean/Core.lean LegalLean/CaseStudies/IRC163h.lean \
  LegalLean/CaseStudies/IRC163h/Theorems.lean \
  LegalLean/CaseStudies/O1Visa.lean \
  monograph/verified-legal-reasoning.md \
  > adversarial-review/codex-review.md
```

### Option 3: Claude Code (this environment)

```bash
# Already available in this environment
cat adversarial-review/prompt.md
# Then paste to a new Claude session with the files attached
```

### Option 4: Manual (any frontier LLM web interface)

1. Open the LLM of your choice
2. Paste the contents of `adversarial-review/prompt.md`
3. Attach or paste the 4 Lean files and the paper markdown
4. Save the response to `adversarial-review/<model>-review.md`

## Interpreting Results

A genuine adversarial review should identify at least 3-5 weaknesses. If a review finds no weaknesses, it is likely being sycophantic rather than critical. The most valuable feedback will be:

1. Theorems that are trivially true by construction (not genuine properties of law)
2. Missing comparisons to prior work we have not cited
3. Logical gaps in the FormalisationBoundary novelty claim
4. Honest assessment of whether this advances the field or just translates known ideas into Lean 4
