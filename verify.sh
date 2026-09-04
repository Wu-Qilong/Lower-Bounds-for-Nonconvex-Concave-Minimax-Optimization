#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 static_check.py
python3 check_no_placeholders.py
lake build
lake env lean NCCLowerBound/AxiomAudit.lean
echo "Verification passed: source hygiene, root coverage, lake build, and axiom audit succeeded."
