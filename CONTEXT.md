# Repository Context

## Environment
- Lean toolchain: `leanprover/lean4:v4.25.0-rc2` (from `lean-toolchain`).
- Lake project `lean_bcp_dynamic_vs_ctp` targeting library `LeanBcpDynamicVsCtp` (see `lakefile.toml`).
- External packages pinned via `lake-manifest.json`, primary dependency `mathlib` at `8dc6b85141811b975cfff8d40db18424dad4a14e`; additional inherited tooling packages (`plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets` v0.0.77, `aesop`, `Qq`, `batteries`, `Cli`).
- Lake options enable unicode pretty-printing, strict implicit handling, mathlib style linting hints, and limit synthesis depth to 3.

## Project Structure
- `LeanBcpDynamicVsCtp.lean`: top-level file importing the project modules:
  - `LeanBcpDynamicVsCtp.Basic`
  - `LeanBcpDynamicVsCtp.Drift`
  - `LeanBcpDynamicVsCtp.ExpectationSupermartingale`
  - `LeanBcpDynamicVsCtp.IonescuTulcea`
- `LeanBcpDynamicVsCtp/Basic.lean`: simple placeholder definition `def hello := "world"`.
- `LeanBcpDynamicVsCtp/Drift.lean`: Lemma A (deterministic telescoping drift)
  - `lemmaA_unscaled`: bound on `∑_{t < T} y t` from one-step drift inequalities.
  - `lemmaA_average`: averaged version for `T > 0`.
- `LeanBcpDynamicVsCtp/ExpectationSupermartingale.lean`: Lemma B (expectation form)
  - Defines `E μ f := ∫ f dμ` and proves expected-process monotonicity under an unconditional drift.
- `LeanBcpDynamicVsCtp/IonescuTulcea.lean`: Lemma C (path-space measure)
  - Exposes a construction using mathlib’s `ProbabilityTheory.Kernel.traj` to build a path measure from an initial law and a homogeneous Markov kernel; provides `coord` and its measurability.
- `README.md`: now documents how to use the drift and expectation lemmas and the path-measure helper.

## Current Lean Code
```lean
-- LeanBcpDynamicVsCtp.lean
import LeanBcpDynamicVsCtp.Basic
import LeanBcpDynamicVsCtp.Drift
import LeanBcpDynamicVsCtp.ExpectationSupermartingale
import LeanBcpDynamicVsCtp.IonescuTulcea

-- LeanBcpDynamicVsCtp/Basic.lean
def hello := "world"
```

## Build Status (Green)
- Deterministic build succeeds on the pinned toolchain and mathlib:
  - Command: `lake build` (toolchain from `lean-toolchain`: `leanprover/lean4:v4.25.0-rc2`).
  - All targets in this package build successfully.
- Remaining non-blocking lints (informational):
  - A few "try `simp` instead of `simpa`" nudges in `LeanBcpDynamicVsCtp/Drift.lean` and `LeanBcpDynamicVsCtp/IonescuTulcea.lean` where `simpa using …` is intentional for clarity.
- Key normalization choices (stabilized):
  - Keep drift RHS in the canonical form `(-η) * (∑ y)` (avoid reintroducing `-(η * ∑ y)`).
  - In `lemmaA_average`, scale once by `(1/T)` and normalize each term via small pinned equalities (`h1–h3'`).

## Mathlib APIs used
- Kernel framework: `ProbabilityTheory.Kernel` and composition/bind `∘ₘ` under `Mathlib/Probability/Kernel/Composition`.
- Ionescu–Tulcea: `ProbabilityTheory.Kernel.traj` and related partial trajectory lemmas in `Mathlib/Probability/Kernel/IonescuTulcea`.
- Finite sums and algebra: `Finset.range`/`BigOperators`.

## Next Steps
- Optional lint pass: convert a couple of `simpa using …` to direct `simp` where it reads well, or leave as-is for readability.
- Optional examples: add tiny shape-guard examples in `Drift.lean` to catch regressions early (see PLAN.md Phase 5).
- Possible extension: strengthen Lemma B to a conditional supermartingale using `condExp` and a user-provided filtration.
