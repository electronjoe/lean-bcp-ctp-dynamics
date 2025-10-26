# Repository Context

## Environment
- Lean toolchain: `leanprover/lean4:v4.25.0-rc2` (from `lean-toolchain`).
- Lake project `lean_bcp_dynamic_vs_ctp` targeting library `LeanBcpDynamicVsCtp` (see `lakefile.toml`).
- External packages pinned via `lake-manifest.json`, primary dependency `mathlib` at `8dc6b85141811b975cfff8d40db18424dad4a14e`; additional inherited tooling packages (`plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets` v0.0.77, `aesop`, `Qq`, `batteries`, `Cli`).
- Lake options enable unicode pretty-printing, strict implicit handling, mathlib style linting hints, and limit synthesis depth to 3.

## Project Structure
- `LeanBcpDynamicVsCtp.lean`: top-level Lean file; currently only imports `LeanBcpDynamicVsCtp.Basic`.
- `LeanBcpDynamicVsCtp/Basic.lean`: only implemented Lean module; presently defines the placeholder constant `def hello := "world"`.
- `README.md`: default GitHub setup instructions; no project-specific documentation yet.

## Current Lean Code
```lean
-- LeanBcpDynamicVsCtp.lean
import LeanBcpDynamicVsCtp.Basic

-- LeanBcpDynamicVsCtp/Basic.lean
def hello := "world"
```

## Editing Notes for GPT-5 Pro
- The repository is effectively empty aside from the placeholder `hello` definition; new proofs/definitions should extend files under `LeanBcpDynamicVsCtp/`.
- If additional modules are created, add them to `LeanBcpDynamicVsCtp.lean` or reorganize the import tree as needed.
- Consider updating `README.md` once substantive content exists.
