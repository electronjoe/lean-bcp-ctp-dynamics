# lean_bcp_dynamic_vs_ctp

Formalization of **Lyapunov Drift Bounds and Path-Space Construction**  
for comparison of **Backpressure (BP)** vs **Collection Tree Protocol (CTP)** style routing.

---

## ✅ Build & Environment

- **Toolchain:** `leanprover/lean4:v4.25.0-rc2`
- **Dependencies:** pinned to mathlib commit `8dc6b85141811b975cfff8d40db18424dad4a14e`
- **Build:**  
```bash
  lake build
````

* **Status:** all targets compile cleanly under the pinned mathlib version.

---

## 📘 Proven Theorems (Completed Work)

### A. Deterministic Drift Bounds — *Lemma A*

File: `LeanBcpDynamicVsCtp/Drift.lean`

1. **Telescoping and Sum Lemmas**

   * `sum_range_telescope`:
     $$\sum_{t=0}^{T-1} (L_{t+1} - L_t) = L_T - L_0.$$
   * `sum_const_range_real`:
     $$\sum_{t=0}^{T-1} B = T , B.$$
   * `sum_scale`, `neg_eta_sum`: scalar manipulation of finite sums.

2. **Lemma A (Unscaled Form):**
   Deterministic telescoping drift bound.
   Given $$( \eta>0 ), ( L_t \ge 0 )$$, and
   $$L_{t+1} - L_t \le B - \eta y_t + p_t,$$
   then
   $$\sum_{t=0}^{T-1} y_t \le \frac{L_0}{\eta} + \frac{T B}{\eta} + \frac{1}{\eta}\sum_{t=0}^{T-1} p_t.$$

3. **Lemma A (Average Form):**
   For (T>0),
   $$\frac{1}{T}\sum_{t=0}^{T-1} y_t
   \le \frac{L_0}{\eta T} + \frac{B}{\eta} + \frac{1}{\eta T}\sum_{t=0}^{T-1} p_t.$$

👉 *Implements the deterministic “Lemma A” planned in our theoretical framework.*

---

### B. Expectation-Level Supermartingale Monotonicity — *Lemma B (Expectation Form)*

File: `LeanBcpDynamicVsCtp/ExpectationSupermartingale.lean`

* **Setup:** measure space ((\Omega,\mu)), integrable processes (L_t, Y_t, P_t).
* **Assumption:**
  $$\mathbb{E}[L_{t+1} - L_t] \le B - \eta,\mathbb{E}[Y_t] + \mathbb{E}[P_t].$$
* **Conclusion:**
  Define $$( \alpha_t = B - \eta,\mathbb{E}[Y_t] + \mathbb{E}[P_t] )$$.
  Then the sequence
  $$S_t = \mathbb{E}[L_t] - \sum_{k < t} \alpha_k$$
  is nonincreasing:
  $$S_{t+1} \le S_t.$$

👉 *Provides an expectation-level supermartingale result; conditional (filtration) version remains open.*

---

### C. Path-Space Measure Construction — *Lemma C (Ionescu–Tulcea)*

File: `LeanBcpDynamicVsCtp/IonescuTulcea.lean`

Implements the canonical path-space construction for Markov processes:

1. `liftHomKernel` and `κdep`: lift a homogeneous Markov kernel to the prefix-dependent family needed by `Kernel.traj`.
2. `μprefix0`: initial measure on the zero-length prefix.
3. **`pathMeasure μ0 κ`:** constructs
   $$\mathbb{P} = \texttt{Kernel.traj}(κ) \circ \mu_0,$$
   a probability measure on the trajectory space ((\mathbb{N} \to \alpha)).
4. `coord` and `measurable_coord`: coordinate process and its measurability.

👉 *Implements the “path measure exists” step used to define expectations over trajectories.*

---

## 🚧 Open / Planned Work

| Area                                         | Description                                                                                                         | Status                                    |
| -------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- | ----------------------------------------- |
| **Conditional Supermartingale (Filtration)** | Extend Lemma B to conditional expectations with filtrations and optional sampling.                                  | ⏳ Not implemented                         |
| **Foster–Lyapunov Stability / Recurrence**   | Formalize positive recurrence (Foster–Lyapunov criterion) for Markov chains.                                        | ⏳ Not implemented                         |
| **Drift-Plus-Penalty (DPP) Theorem**         | Add (O(1/V))–(O(V)) trade-off result using Lemma A + B.                                                             | ⏳ Not implemented                         |
| **Finite-Buffer Backpressure (FBP)**         | Model shadow vs. real queues and prove exponential (O(e^{-cB})) drop bound.                                         | ⏳ Not implemented                         |
| **Queue-Blind Tree (CTP-like) Policy Class** | Define class (\mathcal{G}) and formalize periodic-cut overflow lemmas.                                              | ⏳ Not implemented                         |
| **Separation Theorem (FBP vs CTP)**          | Prove existence of dynamics yielding bounded-away-from-zero drop rate for (\mathcal{G}) vs. vanishing drop for FBP. | ⏳ Not implemented                         |
| **Markov Property Restatements**             | Restate / prove that `pathMeasure` yields a Markov process with kernel κ and initial law μ₀.                        | ⏳ Not yet restated (available in mathlib) |

---

## 📁 File Overview

| File                                                  | Contents                                             |
| ----------------------------------------------------- | ---------------------------------------------------- |
| `LeanBcpDynamicVsCtp/Drift.lean`                      | Deterministic telescoping drift lemmas (Lemma A).    |
| `LeanBcpDynamicVsCtp/ExpectationSupermartingale.lean` | Expectation-level supermartingale lemma (Lemma B).   |
| `LeanBcpDynamicVsCtp/IonescuTulcea.lean`              | Path-space measure construction (Lemma C).           |
| `LeanBcpDynamicVsCtp/Basic.lean`                      | Placeholder / hello world.                           |
| `PLAN.md`                                             | Notes and shape invariants for the algebraic lemmas. |

---

## ✏️ Notes on Math in Markdown

GitHub supports math display in fenced code blocks or inline form depending on the viewer:

* Inline math: `$a^2 + b^2 = c^2$`
* Display math (requires MathJax/Katex-enabled viewer):

  ```latex
  $$\sum_{t=0}^{T-1} (L_{t+1} - L_t) = L_T - L_0$$
  ```

By default, GitHub renders these as plain text unless math rendering is enabled via browser extension or Actions.

---

## 🧩 Next Steps

1. **Add `ConditionalSupermartingale.lean`:** implement filtration-level Lemma B using mathlib’s martingale API.
2. **Add `CutMassBalance.lean`:** deterministic overflow bounds for queue-blind class (\mathcal{G}).
3. **Add `DPP_FiniteBuffer.lean`:** specialize Lemma A + B to DPP and prove exponential-in-B reliability of FBP.
4. **Integrate into test suite** once mathlib’s probabilistic stability layer (Markov kernels, optional sampling) is updated.
