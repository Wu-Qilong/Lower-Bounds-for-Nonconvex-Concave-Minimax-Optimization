$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot

if ($null -eq (Get-Command lake -ErrorAction SilentlyContinue)) {
    throw 'lake was not found. Install Elan/Lean 4.34.0-rc2 or add lake to PATH.'
}
if ($null -eq (Get-Command python -ErrorAction SilentlyContinue)) {
    throw 'python was not found on PATH.'
}

python static_check.py
if ($LASTEXITCODE -ne 0) { throw "static_check.py failed with exit code $LASTEXITCODE" }
python check_no_placeholders.py
if ($LASTEXITCODE -ne 0) { throw "check_no_placeholders.py failed with exit code $LASTEXITCODE" }

lake build
if ($LASTEXITCODE -ne 0) { throw "lake build failed with exit code $LASTEXITCODE" }

lake env lean NCCLowerBound/AxiomAudit.lean
if ($LASTEXITCODE -ne 0) { throw "axiom audit failed with exit code $LASTEXITCODE" }

Write-Host 'Verification passed: source hygiene, root coverage, lake build, and axiom audit succeeded.'
