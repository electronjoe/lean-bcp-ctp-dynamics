# lean_bcp_dynamic_vs_ctp

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

## Build

- Toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.25.0-rc2`).
- Install dependencies and build:
  - `lake build`
- Status: all targets compile successfully against the pinned mathlib from `lake-manifest.json`.

## Drift lemmas and expectation supermartingale

See `LeanBcpDynamicVsCtp/Drift.lean`:
- `lemmaA_unscaled` and `lemmaA_average` provide deterministic telescoping drift bounds.
  - Normal form convention: keep the drift RHS as `(-η) * (∑ t ∈ range T, y t)`.
  - The averaged form scales by `(1 / T)` and then normalizes each term via small pinned equalities to avoid brittle simp search.

See `LeanBcpDynamicVsCtp/ExpectationSupermartingale.lean`:
- `lemmaB_expectation_supermartingale` turns an unconditional drift inequality into a
  nonincreasing expected process (requires integrability of the terms).

## Path-space measure (Ionescu–Tulcea)

See `LeanBcpDynamicVsCtp/IonescuTulcea.lean`:
- `pathMeasure μ0 κ` constructs a measure on paths `Π n, α` from an initial law `μ0` and
  a homogeneous Markov kernel `κ` using mathlib’s `Kernel.traj` construction.
- `coord t` is the coordinate process and `measurable_coord` records its measurability.

## Notes

- Some linter suggestions ("try `simp` instead of `simpa`") remain where `simpa using …` is deliberate for clarity. These do not affect correctness or the build.
- For the shape invariants used by the drift lemmas (e.g., `(-η) * ∑ y`), see PLAN.md for rationale and maintenance tips.
