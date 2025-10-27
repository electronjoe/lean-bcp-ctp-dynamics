import Mathlib

open scoped BigOperators
open Finset

namespace LeanBcpDynamicVsCtp

variable {Ω : Type*} [MeasurableSpace Ω]

open MeasureTheory

noncomputable def E (μ : Measure Ω) (f : Ω → ℝ) : ℝ := ∫ ω, f ω ∂μ

/-- Lemma B (expectation form, with an explicit measure `μ`). -/
theorem lemmaB_expectation_supermartingale
    (μ : Measure Ω) (L Y P : ℕ → Ω → ℝ) (B η : ℝ)
    (hL : ∀ t, Integrable (L t) μ)
    (_hY : ∀ t, Integrable (Y t) μ)
    (_hP : ∀ t, Integrable (P t) μ)
    (h : ∀ t : ℕ,
      E μ (fun ω => L (t+1) ω - L t ω)
        ≤ B - η * E μ (Y t) + E μ (P t)) :
    ∀ t : ℕ,
      (E μ (L (t+1)) - Finset.sum (Finset.range (t+1)) (fun k => (B - η * E μ (Y k) + E μ (P k))))
        ≤ (E μ (L t) - Finset.sum (Finset.range t) (fun k => (B - η * E μ (Y k) + E μ (P k)))) := by
  classical
  intro t
  set α : ℕ → ℝ := fun k => (B - η * E μ (Y k) + E μ (P k)) with hα
  have hs :
      Finset.sum (Finset.range (t+1)) α
        = (Finset.sum (Finset.range t) α) + α t := by
    simp [hα, Finset.sum_range_succ, add_comm, add_assoc]
  -- E of a pointwise difference is difference of Es
  have hlin : E μ (fun ω => L (t+1) ω - L t ω) = E μ (L (t+1)) - E μ (L t) := by
    simpa [E] using (MeasureTheory.integral_sub (hL (t+1)) (hL t))
  -- Move `α t` to the left and shift by `E μ (L t) - S_t`
  have hdiff : (E μ (L (t+1)) - E μ (L t)) - α t ≤ 0 := by
    have hAt : E μ (fun ω => L (t+1) ω - L t ω) ≤ α t := by
      simpa [hα] using h t
    simpa [hlin] using (sub_nonpos.mpr hAt)
  -- Use a calc chain to align the target shape
  have hS :
      E μ (L (t+1)) - Finset.sum (Finset.range (t+1)) α
        = ((E μ (L (t+1)) - E μ (L t)) - α t)
          + (E μ (L t) - Finset.sum (Finset.range t) α) := by
    simp [hs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hS' :
      ((E μ (L (t+1)) - E μ (L t)) - α t)
          + (E μ (L t) - Finset.sum (Finset.range t) α)
        ≤ 0 + (E μ (L t) - Finset.sum (Finset.range t) α) :=
    add_le_add_right hdiff _
  have hS'' : 0 + (E μ (L t) - Finset.sum (Finset.range t) α) =
      (E μ (L t) - Finset.sum (Finset.range t) α) := by simp
  calc
    E μ (L (t+1)) - Finset.sum (Finset.range (t+1)) α
        = ((E μ (L (t+1)) - E μ (L t)) - α t)
          + (E μ (L t) - Finset.sum (Finset.range t) α) := hS
    _ ≤ 0 + (E μ (L t) - Finset.sum (Finset.range t) α) := hS'
    _ = (E μ (L t) - Finset.sum (Finset.range t) α) := hS''

end LeanBcpDynamicVsCtp
