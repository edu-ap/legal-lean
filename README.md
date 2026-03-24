# LegalLean — Verified Legal Reasoning in Lean 4

[![Verify](https://github.com/edu-ap/legal-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/edu-ap/legal-lean/actions/workflows/verify.yml)

**Monograph:** *Verified Legal Reasoning: From Natural Language to Formal Proof*

## Architecture

Three-layer architecture where the process of writing the monograph validates its own thesis:

```
Layer 1: Lean 4 (LegalLean/)     — Verified types and proofs (invariant verifier)
Layer 2: JSON (arguments/)        — Claim-evidence graph with defeat relations (Legal IR)
Layer 3: Prose (monograph/)       — Published monograph (generated from both layers)
```

**Core thesis:** Legal reasoning can be partially formalised in dependent type theory, and the boundary between formalisable and non-formalisable elements can itself be encoded within the type system (`FormalisationBoundary`).

**Signature framing (Gemini):** LLMs are heuristic transducers; Lean 4 is the invariant verifier.

## Key Types

| Type | Purpose |
|------|---------|
| `Deontic` | Permitted / prohibited / obligatory |
| `LegalRule` | Rule with defeasibility metadata |
| `EvidenceFor` | Propositions-as-types for legal evidence |
| `DefeasiblyHolds` | Non-monotonic entailment (holds unless defeated) |
| `FormalisationBoundary` | Hart's open texture as a first-class type |
| `RequiresHumanDetermination` | Typeclass marking where formal verification yields to human judgment |
| `Vague` | Core/penumbra distinction (subclass of RequiresHumanDetermination) |
| `Discretionary` | Authority discretion (subclass of RequiresHumanDetermination) |

## Case Studies

1. **IRC §163(h)** — Mortgage interest deduction (Lawsky's gold standard). COMPLETE.
2. **O-1 Visa** — "3 of 8" criteria as dependent types. Stub + research.
3. **Australian TCP Code** — Regulatory compliance (Governatori comparison). Stub + research.

## Automated Pipeline

### Research (Perplexity)

Extracts `sorry`/TODO stubs from Lean 4 files, generates structured prompts shaped to match LegalLean types, and calls Perplexity API with model council.

```bash
# Dry run (preview prompts)
python3 scripts/research_pipeline.py --all --dry-run

# Research specific case study
python3 scripts/research_pipeline.py --file IRC163h --models sonar-pro

# Model council (multiple models)
python3 scripts/research_pipeline.py --all --models sonar sonar-pro sonar-reasoning

# 8-dimension comparison table
python3 scripts/research_pipeline.py --comparisons --models sonar-pro
```

**Prompt engineering:** Questions are shaped so answers map to LegalLean types:
- Conditions -> `LegalRule.conclusion`
- Exceptions -> `Defeats`
- Vague terms -> `FormalisationBoundary` / `Vague`
- Authorities -> `Discretionary`
- Case law -> `EvidenceFor` sources

### Theorem Proving (Aristotle by Harmonic)

Automated sorry-stub resolution using Aristotle (aristotle.harmonic.fun). IMO gold-medal-level engine that fills `sorry` stubs with verified Lean 4 proofs.

```bash
# List sorry stubs (no API call)
python3 scripts/aristotle_prover.py --all --dry-run

# Prove sorries in specific file
python3 scripts/aristotle_prover.py --file LegalLean/CaseStudies/IRC163h.lean

# Prove all files (parallel, max 5 concurrent)
python3 scripts/aristotle_prover.py --all

# Sequential mode (if hitting rate limits)
python3 scripts/aristotle_prover.py --all --sequential --timeout 20
```

**Architecture:** Monte Carlo Graph Search with 200B+ parameter transformer. Every solution verified by Lean 4 type checker before delivery (hallucination-free by design).

**SDK:** `pip install aristotlelib`

**API key:** `ARISTOTLE_HARMONIC_API_KEY` in `.env` (mapped to `ARISTOTLE_API_KEY` for SDK).

### Full Pipeline

```
sorry in Lean 4
    |
    v
research_pipeline.py (Perplexity) --> structured legal knowledge (JSON)
    |
    v
Human translates to Lean 4 types + sorry stubs
    |
    v
aristotle_prover.py (Harmonic) --> verified proofs replacing sorry
    |
    v
Lean 4 type checker confirms (deterministic, hallucination-free)
    |
    v
Human reviews proof for legal correctness
    |
    v
arguments/thesis.json updated with verified claims
    |
    v
monograph/ prose generated from verified claims
```

## Comparison Table (7 dimensions)

Scores from Perplexity research (note: may reflect prompt bias for LegalLean):

| Dimension | DDL | Catala | L4L | LegalLean | LegalRuleML |
|-----------|-----|--------|-----|-----------|-------------|
| Compositional semantics | 4 | 4 | 3 | 5 | 2 |
| Deontic modalities | 5 | 2 | 4 | 5 | 4 |
| Dependent types | 1 | 1 | 5 | 5 | 1 |
| Machine-checkable guarantees | 3 | 4 | 3 | 5 | 1 |
| Open texture encoding | 4 | 2 | 3 | 5 | 2 |
| Provenance tracking | 4 | 3 | 5 | 5 | 4 |
| Temporal reasoning | 4 | 3 | 3 | 5 | 4 |
| **Total** | **25** | **19** | **26** | **35** | **18** |

## Target Audience

**Tier 1 (must impress):** Sarah Lawsky, Monica Palmirani, Jeremy Avigad, Leonardo de Moura, Guido Governatori, Zhe Hou.

**Tier 2 (should engage):** Henry Prakken, Trevor Bench-Capon, Daniel Martin Katz, Scott Shapiro.

**Target venue:** JURIX 2026 or ICAIL 2027.

## Dependencies

- Lean 4 v4.16.0+
- Python 3.12+ (for research and proving scripts)
- `aristotlelib` (Aristotle SDK)
- `requests` (Perplexity API)
- API keys: `PERPLEXITY_API_KEY`, `ARISTOTLE_HARMONIC_API_KEY`

## Key References

- Lawsky, "A Logic for Statutes", Florida Tax Review (2017)
- Hart, *The Concept of Law* (1961) — open texture
- Governatori, "Computing Contracts with Defeasible Deontic Logic"
- Merigoux et al., "Catala: A Programming Language for the Law"
- Hou et al., "L4L: Towards Trustworthy Legal AI through LLM Agents and Formal Reasoning"
- Palmirani et al., "LegalRuleML Core Specification v1.0"
