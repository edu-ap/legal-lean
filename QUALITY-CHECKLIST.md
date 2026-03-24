# Quality Checklist for Outstanding Conference Submission

This checklist defines the bar for an outstanding submission to JURIX / RuleML+RR. Every item must be satisfied before submission. Items marked with an asterisk (*) are stretch goals that would elevate the paper from "good" to "excellent."

## Code Quality

- [x] All modules compile under Lean 4.24.0 (`lake build` passes, zero errors)
- [x] Zero `sorry` stubs across all source files
- [x] Zero warnings (or only lint-level warnings documented and justified)
- [x] Each open-texture axiom has a corresponding `Vague` or `Discretionary` instance with documented core/penumbra
- [x] Each case study has at least 3 proven theorems
- [x] At least one theorem per case study is substantive (not just definition unfolding)
- [x] The monotonicity break theorem is proven and universally quantified
- [x] Each criterion in O-1 Visa maps to its own distinct axiom (per-criterion resolution)
- [ ] Independent verification passes in Docker container (`docker build .`)
- [ ] Independent verification passes on a separate machine (not the development environment)
- [ ] * Mathlib integration for `Finset` (replaces custom `AllDistinct`)

## Paper Quality

- [x] Abstract states thesis, approach, case studies, and headline result in under 250 words
- [x] Introduction motivates the gap with concrete example (compliance system that cannot distinguish formal from boundary)
- [x] Background covers Hart, Lawsky, Curry-Howard without overclaiming
- [x] Framework section includes real Lean 4 code snippets (not pseudocode)
- [x] All 3 case studies presented with enough detail for reproducibility
- [x] Comparison table positions against DDL, Catala, L4L, LegalRuleML with honest scoring caveat
- [x] Limitations section is genuinely honest (not performative humility)
- [x] Sorry-bypass gap discussed
- [x] Normative risk of formalisation acknowledged (Lessig critique)
- [x] Axiom justification: why axioms for open-texture propositions are honest, not holes
- [x] Universality of monotonicity break proof explained (not trivially encoded)
- [x] Concrete Catala vs LegalLean example (qualified residence)
- [x] Related work is fair to all compared systems (especially DDL and Catala)
- [ ] LaTeX version synced with all markdown peer review improvements
- [ ] References are complete and correctly formatted in BibTeX
- [ ] Paper fits within page limit (15pp for RuleML+RR, 10pp for JURIX)
- [ ] * Conference-specific template verified (correct cls file, correct bst file)

## Verification and Reproducibility

- [x] `VERIFICATION.md` with 3-layer protocol (Lean type checker, Aristotle, adversarial LLM)
- [x] `README.md` with architecture, pipeline, and comparison table
- [x] `arguments/thesis.json` with claim-evidence graph
- [x] `arguments/comparison_summary.json` with 7-dimension scores
- [x] MIT LICENSE
- [ ] Dockerfile for independent verification
- [ ] * GitHub Actions CI (needs PAT with workflow scope)
- [ ] Adversarial LLM review completed (Layer 3 of VERIFICATION.md)

## Peer Review

- [x] Passed 9/9 AI reviewer personas (simulated, not real endorsements): Shear, Torvalds, Singh, Tao, Buzzard, Lessig, Lawsky, Governatori, Merigoux
- [ ] Prior art search confirms FormalisationBoundary novelty (confidence target: >= 0.75)
- [ ] * External review by Kevin Buzzard or other Lean 4 expert
- [ ] * Adversarial review by at least one frontier LLM (Gemini/Codex)

## Submission Logistics

- [ ] Venue decided (RuleML+RR 15 May or JURIX ~4 Sep)
- [ ] Title/abstract registered (RuleML+RR: 8 May)
- [ ] Paper compiled in correct template
- [ ] Repository made public (after submission)
- [ ] All co-authors (if any) have reviewed and approved
