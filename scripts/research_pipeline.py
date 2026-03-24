#!/usr/bin/env python3
"""
Research pipeline for LegalLean monograph.

Extracts sorry/TODO stubs from Lean 4 files, generates structured research
questions shaped to match LegalLean types, calls Perplexity API with multiple
models (simulated model council), and saves structured results to arguments/.

Architecture: This script IS the "heuristic transducer" — it converts
natural language legal knowledge into structured form for the "invariant
verifier" (Lean 4) to check.

Usage:
    # Research all sorry stubs
    python3 scripts/research_pipeline.py --all

    # Research a specific case study
    python3 scripts/research_pipeline.py --file LegalLean/CaseStudies/IRC163h.lean

    # Dry run (show prompts without calling API)
    python3 scripts/research_pipeline.py --all --dry-run

    # Use specific models
    python3 scripts/research_pipeline.py --all --models sonar sonar-pro sonar-reasoning
"""

import os
import sys
import json
import re
import time
import argparse
from pathlib import Path
from typing import List, Dict, Optional
from dataclasses import dataclass, asdict

# Add Perplexity client to path (set to your local module path)
# sys.path.insert(0, 'path/to/perplexity/integration')  # Set to your local Perplexity module path
from perplexity_search import PerplexitySearch


@dataclass
class ResearchStub:
    """A sorry/TODO extracted from a Lean 4 file."""
    file: str
    line: int
    context: str          # surrounding code/comments
    namespace: str        # Lean 4 namespace
    description: str      # what needs to be researched
    case_study: Optional[str]  # which case study this belongs to
    target_types: List[str]    # which LegalLean types the answer should map to


# --- Prompt templates shaped to match LegalLean types ---

SYSTEM_PROMPT = """You are a legal research assistant specialising in formal methods
applied to law. Your answers must be structured to support formalisation in Lean 4
dependent type theory. You are helping build a library called LegalLean that encodes
legal reasoning with machine-checkable guarantees.

CRITICAL: Structure your response as JSON with the following schema. Do NOT return
prose — return structured data that maps to type definitions.

Be exhaustive about conditions, exceptions, and vagueness. Legal formalisation
requires knowing EVERY rule, exception, and point of interpretive discretion."""

LEGAL_RULE_PROMPT = """Analyse the following legal provision and return a JSON object
with this exact structure:

{{
  "provision": {{
    "id": "string — official citation",
    "title": "string — short name",
    "jurisdiction": "string",
    "source_url": "string — authoritative source URL"
  }},
  "rules": [
    {{
      "id": "string — unique rule identifier",
      "description": "string — what this rule establishes",
      "modality": "permitted | prohibited | obligatory",
      "conditions": [
        {{
          "id": "string",
          "description": "string — natural language condition",
          "formalisable": true/false,
          "if_not_formalisable": "string — why (vague term? discretionary?)"
        }}
      ],
      "exceptions": [
        {{
          "id": "string",
          "description": "string — what defeats this rule",
          "priority": "string — why this exception wins (lex specialis, lex posterior, etc.)",
          "source": "string — statutory reference for the exception"
        }}
      ],
      "definitions": [
        {{
          "term": "string — defined term",
          "definition": "string — statutory definition",
          "has_open_texture": true/false,
          "core_meaning": "string — settled, uncontested meaning",
          "penumbra": "string — contested, unclear boundary cases"
        }}
      ]
    }}
  ],
  "defeat_relations": [
    {{
      "defeater_rule": "string — rule ID that defeats",
      "defeated_rule": "string — rule ID that is defeated",
      "reason": "string — why (lex specialis, lex posterior, lex superior, etc.)",
      "strict": true/false
    }}
  ],
  "discretionary_checkpoints": [
    {{
      "id": "string",
      "authority": "string — who decides",
      "decision": "string — what they decide",
      "constraints": ["string — limits on their discretion"],
      "gated_rule": "string — which rule this gates"
    }}
  ],
  "open_texture_terms": [
    {{
      "term": "string",
      "type": "vague | discretionary",
      "core": "string — clear cases",
      "penumbra": "string — unclear cases",
      "authority": "string — who resolves ambiguity",
      "case_law": ["string — key cases interpreting this term"]
    }}
  ],
  "key_references": [
    {{
      "author": "string",
      "title": "string",
      "year": "number",
      "relevance": "string",
      "url": "string"
    }}
  ]
}}

Legal provision to analyse:
{provision}

Additional context:
{context}"""

COMPARISON_PROMPT = """Compare how the following legal formalisation systems handle
{dimension}. Return a JSON object:

{{
  "dimension": "{dimension}",
  "systems": [
    {{
      "name": "string — system name",
      "approach": "string — how it handles this dimension",
      "strengths": ["string"],
      "limitations": ["string"],
      "key_paper": "string — citation",
      "expressiveness_score": "1-5 (1=absent, 5=fully native)"
    }}
  ],
  "legallean_advantage": "string — where dependent types in Lean 4 add value",
  "legallean_limitation": "string — honest assessment of gaps"
}}

Systems to compare: DDL (Governatori), Catala (Merigoux), L4L (Hou et al.),
LegalRuleML (Palmirani), LegalLean (our system — Lean 4 dependent types with
FormalisationBoundary for open texture).

Dimension: {dimension}
Context: {context}"""


# --- Stub extraction ---

def extract_stubs(lean_dir: Path) -> List[ResearchStub]:
    """Extract sorry/TODO stubs from all Lean 4 files."""
    stubs = []
    for lean_file in lean_dir.rglob("*.lean"):
        content = lean_file.read_text()
        lines = content.split('\n')
        rel_path = str(lean_file.relative_to(lean_dir.parent))

        # Find namespace
        namespace = "LegalLean"
        for line in lines:
            ns_match = re.match(r'namespace\s+([\w.]+)', line)
            if ns_match:
                namespace = ns_match.group(1)

        # Determine case study
        case_study = None
        if 'IRC163h' in rel_path:
            case_study = 'IRC §163(h) Mortgage Interest Deduction'
        elif 'O1Visa' in rel_path:
            case_study = 'O-1 Visa Extraordinary Ability Criteria'
        elif 'TCPCode' in rel_path:
            case_study = 'Australian Telecommunications Consumer Protections Code'

        # Find sorry and TODO markers
        for i, line in enumerate(lines):
            if 'sorry' in line or 'TODO' in line:
                # Gather context: comments above and code around
                context_start = max(0, i - 10)
                context_end = min(len(lines), i + 5)
                context = '\n'.join(lines[context_start:context_end])

                # Extract description from TODO comment or surrounding comments
                desc = line.strip()
                if 'TODO' in line:
                    desc = line.split('TODO')[-1].strip().lstrip(':').strip()
                    if not desc:
                        # Check next line
                        if i + 1 < len(lines):
                            desc = lines[i + 1].strip().lstrip('--').strip()

                # Determine target types from context
                target_types = []
                if 'Deontic' in context or 'modality' in context:
                    target_types.append('Deontic')
                if 'LegalRule' in context or 'rule' in context.lower():
                    target_types.append('LegalRule')
                if 'defeasib' in context.lower() or 'defeat' in context.lower():
                    target_types.append('DefeasiblyHolds')
                if 'FormalisationBoundary' in context or 'open texture' in context.lower():
                    target_types.append('FormalisationBoundary')
                if 'EvidenceFor' in context or 'evidence' in context.lower():
                    target_types.append('EvidenceFor')
                if not target_types:
                    target_types = ['LegalRule', 'FormalisationBoundary']

                stubs.append(ResearchStub(
                    file=rel_path,
                    line=i + 1,
                    context=context,
                    namespace=namespace,
                    description=desc,
                    case_study=case_study,
                    target_types=target_types
                ))

    return stubs


def generate_prompt(stub: ResearchStub) -> tuple[str, str]:
    """Generate a structured research prompt for a stub.
    Returns (system_prompt, user_prompt)."""

    if stub.case_study:
        # Case study stub: ask for full legal analysis
        provision = stub.case_study
        context = (
            f"This is for the LegalLean monograph. We need to formalise this "
            f"provision in Lean 4 dependent type theory.\n\n"
            f"The stub is in {stub.file} at line {stub.line}.\n"
            f"Target LegalLean types: {', '.join(stub.target_types)}.\n\n"
            f"Code context:\n{stub.context}\n\n"
            f"Be especially thorough about:\n"
            f"1. Every condition and sub-condition for the rule to apply\n"
            f"2. Every exception that can defeat the rule\n"
            f"3. Every term with open texture (vagueness or discretion)\n"
            f"4. The defeat priority ordering between rules\n"
            f"5. Who has discretion and what constrains it"
        )
        return SYSTEM_PROMPT, LEGAL_RULE_PROMPT.format(
            provision=provision, context=context
        )
    else:
        # Non-case-study stub: generate appropriate prompt
        context = (
            f"Stub in {stub.file} at line {stub.line}.\n"
            f"Description: {stub.description}\n"
            f"Target types: {', '.join(stub.target_types)}.\n"
            f"Code context:\n{stub.context}"
        )
        return SYSTEM_PROMPT, LEGAL_RULE_PROMPT.format(
            provision=stub.description, context=context
        )


def generate_comparison_prompts() -> List[tuple[str, str, str]]:
    """Generate prompts for the 8-dimension comparison table.
    Returns list of (dimension, system_prompt, user_prompt)."""

    dimensions = [
        ("defeasibility (non-monotonic reasoning)",
         "How each system handles rules that can be defeated by exceptions or "
         "higher-priority rules. Include: default logic, priorities, burden of proof."),
        ("open texture encoding",
         "How each system handles vague legal terms (e.g. 'reasonable', "
         "'extraordinary'). Include: Hart's core/penumbra distinction."),
        ("dependent types (evidence-as-inhabitants)",
         "Whether the system can express that evidence INHABITS a type "
         "(propositions-as-types / Curry-Howard). Include: proof witnesses."),
        ("deontic modalities",
         "How each system represents permitted/prohibited/obligatory. "
         "Include: conflict resolution between modalities."),
        ("temporal reasoning",
         "How each system handles time-dependent rules: effective dates, "
         "retroactivity, expiry, and temporal defeat."),
        ("provenance tracking",
         "How each system traces conclusions back to source rules and evidence. "
         "Include: citation, audit trail, explainability."),
        ("compositional semantics",
         "Whether the system supports compositional [modular, bottom-up] "
         "construction of complex rules from simpler ones. Include: functorial "
         "composition, rule combination."),
        ("machine-checkable guarantees",
         "What formal guarantees the system provides. Include: type safety, "
         "decidability, soundness, completeness, and what is NOT guaranteed.")
    ]

    prompts = []
    for dim, context in dimensions:
        prompts.append((
            dim,
            SYSTEM_PROMPT,
            COMPARISON_PROMPT.format(dimension=dim, context=context)
        ))
    return prompts


# --- API calls with model council ---

def call_perplexity(
    client: PerplexitySearch,
    system_prompt: str,
    user_prompt: str,
    model: str = "sonar-pro",
    max_tokens: int = 4000
) -> Dict:
    """Call Perplexity API with structured prompt."""

    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt}
        ],
        "max_tokens": max_tokens,
        "temperature": 0.1,  # Low temperature for factual accuracy
        "return_citations": True
    }

    try:
        import requests
        response = requests.post(
            f"{client.base_url}/chat/completions",
            headers=client.headers,
            json=payload,
            timeout=120
        )
        response.raise_for_status()
        result = response.json()

        answer = result['choices'][0]['message']['content']
        citations = result.get('citations', [])

        # Try to parse answer as JSON
        parsed = None
        try:
            # Strip markdown code fences if present
            clean = answer.strip()
            if clean.startswith('```'):
                clean = re.sub(r'^```\w*\n', '', clean)
                clean = re.sub(r'\n```.*$', '', clean, flags=re.DOTALL)
            parsed = json.loads(clean)
        except json.JSONDecodeError:
            pass  # Keep raw text if not valid JSON

        return {
            "model": model,
            "answer_raw": answer,
            "answer_parsed": parsed,
            "citations": citations,
            "usage": result.get('usage', {})
        }

    except Exception as e:
        return {
            "model": model,
            "error": str(e),
            "answer_raw": None,
            "answer_parsed": None,
            "citations": [],
            "usage": {}
        }


def model_council(
    client: PerplexitySearch,
    system_prompt: str,
    user_prompt: str,
    models: List[str] = None,
    delay: float = 2.0
) -> Dict:
    """Call multiple Perplexity models and return all responses.
    Simulates the model council feature from Perplexity Pages."""

    if models is None:
        models = ["sonar", "sonar-pro", "sonar-reasoning"]

    results = []
    for model in models:
        print(f"  Querying {model}...", file=sys.stderr)
        result = call_perplexity(client, system_prompt, user_prompt, model=model)
        results.append(result)
        if model != models[-1]:
            time.sleep(delay)  # Rate limiting

    return {
        "models_queried": models,
        "responses": results,
        "consensus": _find_consensus(results)
    }


def _find_consensus(responses: List[Dict]) -> Dict:
    """Identify convergence and divergence across model responses."""
    parsed = [r['answer_parsed'] for r in responses if r.get('answer_parsed')]
    all_citations = []
    for r in responses:
        all_citations.extend(r.get('citations', []))

    return {
        "models_with_valid_json": len(parsed),
        "total_models": len(responses),
        "all_citations": list(set(all_citations)),
        "note": "Manual review needed to synthesise responses into final argument"
    }


# --- Main pipeline ---

def run_pipeline(
    lean_dir: Path,
    output_dir: Path,
    models: List[str] = None,
    dry_run: bool = False,
    specific_file: Optional[str] = None,
    include_comparisons: bool = False
):
    """Run the full research pipeline."""

    # Extract stubs
    stubs = extract_stubs(lean_dir)
    if specific_file:
        stubs = [s for s in stubs if specific_file in s.file]

    print(f"Found {len(stubs)} research stubs", file=sys.stderr)

    if not stubs and not include_comparisons:
        print("No stubs found. Nothing to research.", file=sys.stderr)
        return

    output_dir.mkdir(parents=True, exist_ok=True)

    if dry_run:
        # Just show prompts
        for stub in stubs:
            sys_prompt, user_prompt = generate_prompt(stub)
            print(f"\n{'='*80}")
            print(f"STUB: {stub.file}:{stub.line}")
            print(f"CASE STUDY: {stub.case_study or 'N/A'}")
            print(f"TARGET TYPES: {', '.join(stub.target_types)}")
            print(f"{'='*80}")
            print(f"\nSYSTEM PROMPT:\n{sys_prompt[:200]}...")
            print(f"\nUSER PROMPT:\n{user_prompt[:500]}...")

        if include_comparisons:
            comparison_prompts = generate_comparison_prompts()
            for dim, sys_p, user_p in comparison_prompts:
                print(f"\n{'='*80}")
                print(f"COMPARISON: {dim}")
                print(f"{'='*80}")
                print(f"\nPROMPT:\n{user_p[:500]}...")

        return

    # Initialise Perplexity client
    client = PerplexitySearch()

    # Research each stub
    for i, stub in enumerate(stubs):
        print(f"\n[{i+1}/{len(stubs)}] Researching: {stub.file}:{stub.line}",
              file=sys.stderr)
        print(f"  Case study: {stub.case_study or 'N/A'}", file=sys.stderr)

        sys_prompt, user_prompt = generate_prompt(stub)

        result = model_council(client, sys_prompt, user_prompt, models=models)

        # Save result
        slug = re.sub(r'[^a-z0-9]+', '_', stub.file.lower()).strip('_')
        output_file = output_dir / f"research_{slug}_line{stub.line}.json"

        output = {
            "stub": asdict(stub),
            "prompt": {
                "system": sys_prompt,
                "user": user_prompt
            },
            "results": result,
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        }

        output_file.write_text(json.dumps(output, indent=2, ensure_ascii=False))
        print(f"  Saved to {output_file}", file=sys.stderr)

        time.sleep(3)  # Rate limiting between stubs

    # Run comparison table research if requested
    if include_comparisons:
        print(f"\nResearching comparison dimensions...", file=sys.stderr)
        comparison_prompts = generate_comparison_prompts()

        for dim, sys_prompt, user_prompt in comparison_prompts:
            print(f"\n  Dimension: {dim}", file=sys.stderr)
            result = model_council(client, sys_prompt, user_prompt, models=models)

            slug = re.sub(r'[^a-z0-9]+', '_', dim).strip('_')
            output_file = output_dir / f"comparison_{slug}.json"

            output = {
                "dimension": dim,
                "prompt": {
                    "system": sys_prompt,
                    "user": user_prompt
                },
                "results": result,
                "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            }

            output_file.write_text(json.dumps(output, indent=2, ensure_ascii=False))
            print(f"  Saved to {output_file}", file=sys.stderr)

            time.sleep(3)

    print(f"\nResearch complete. Results in {output_dir}/", file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(
        description="Research pipeline for LegalLean monograph"
    )
    parser.add_argument(
        '--all', action='store_true',
        help='Research all sorry/TODO stubs'
    )
    parser.add_argument(
        '--file', type=str,
        help='Research stubs in a specific Lean file'
    )
    parser.add_argument(
        '--comparisons', action='store_true',
        help='Also research the 8-dimension comparison table'
    )
    parser.add_argument(
        '--models', nargs='+',
        default=['sonar-pro'],
        help='Perplexity models to query (default: sonar-pro). '
             'Use multiple for model council: --models sonar sonar-pro sonar-reasoning'
    )
    parser.add_argument(
        '--dry-run', action='store_true',
        help='Show prompts without calling API'
    )
    parser.add_argument(
        '--lean-dir', type=str,
        default='LegalLean',
        help='Path to LegalLean source directory'
    )
    parser.add_argument(
        '--output-dir', type=str,
        default='arguments/research',
        help='Output directory for research results'
    )

    args = parser.parse_args()

    if not args.all and not args.file and not args.comparisons:
        parser.error("Must specify --all, --file, or --comparisons")

    lean_dir = Path(args.lean_dir)
    output_dir = Path(args.output_dir)

    if not lean_dir.exists():
        print(f"Error: {lean_dir} not found. Run from legal-lean repo root.",
              file=sys.stderr)
        sys.exit(1)

    run_pipeline(
        lean_dir=lean_dir,
        output_dir=output_dir,
        models=args.models,
        dry_run=args.dry_run,
        specific_file=args.file,
        include_comparisons=args.comparisons
    )


if __name__ == '__main__':
    main()
