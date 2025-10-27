import Mathlib

-- set_option diagnostics true -- noisy; uncomment locally when debugging

open scoped BigOperators
open Finset

namespace LeanBcpDynamicVsCtp

/-- (1) Standard telescope for differences over `range T`. -/
lemma sum_range_telescope (L : ℕ → ℝ) (T : ℕ) :
  (Finset.sum (Finset.range T) (fun t => (L (t + 1) - L t))) = L T - L 0 := by
  simpa [sub_eq_add_neg] using (sum_range_sub (fun t => L t) T)

/-- (2) Sum of a constant over `range T`. -/
lemma sum_const_range_real (B : ℝ) (T : ℕ) :
  (Finset.sum (Finset.range T) (fun _ => B)) = (T : ℝ) * B := by
  simpa [card_range, nsmul_eq_mul, mul_comm] using (sum_const (B) (s := range T))

/-- (3) Pull scalar out of a finite sum. -/
lemma sum_scale {η : ℝ} (y : ℕ → ℝ) (T : ℕ) :
  (Finset.sum (Finset.range T) (fun t => ((-η) * y t)))
    = (-η) * (Finset.sum (Finset.range T) (fun t => y t)) := by
  simpa [mul_sum]

lemma neg_eta_sum (η : ℝ) (y : ℕ → ℝ) (T : ℕ) :
    -(η * (Finset.sum (Finset.range T) (fun t => y t)))
      = (-η) * (Finset.sum (Finset.range T) (fun t => y t)) := by
  simpa using (neg_mul η (Finset.sum (Finset.range T) (fun t => y t)))

/-- (4) From `L T - L 0 ≤ (T*B) + (-η) * Σ y + Σ p` deduce a bound on `η * Σ y`. -/
lemma isolate_eta_sum
  {L : ℕ → ℝ} {B η : ℝ} {y p : ℕ → ℝ} {T : ℕ}
  (h : L T - L 0 ≤ (T : ℝ) * B
        + (-η) * (Finset.sum (Finset.range T) (fun t => y t))
        + (Finset.sum (Finset.range T) (fun t => p t))) :
  η * (Finset.sum (Finset.range T) (fun t => y t))
      ≤ L 0 - L T + (T : ℝ) * B + (Finset.sum (Finset.range T) (fun t => p t)) := by
  linarith

/-- (5) If `0 ≤ L T`, then `L 0 - L T ≤ L 0`. -/
lemma drop_nonpos_term {L : ℕ → ℝ} (hLT : 0 ≤ L T) :
  L 0 - L T ≤ L 0 := by
  linarith

/-- (6) Scale a `≤` by `(1/η)` for `η>0` and normalize divisions. -/
lemma scale_by_inv_pos {η : ℝ} (hηpos : 0 < η)
  {a b : ℝ} (h : a ≤ b) :
  (1 / η) * a ≤ (1 / η) * b := by
  have : 0 ≤ (1 / η) := by simpa [one_div] using inv_nonneg.mpr (le_of_lt hηpos)
  exact mul_le_mul_of_nonneg_left h this

/-- Lemma A (unscaled): deterministic telescoping drift bound on partial sums. -/
theorem lemmaA_unscaled
    (L y p : ℕ → ℝ) (B η : ℝ) (T : ℕ)
    (hηpos : 0 < η)
    (hLnonneg : ∀ t, 0 ≤ L t)
    (hstep : ∀ t < T, L (t + 1) - L t ≤ B - η * y t + p t) :
    (Finset.sum (Finset.range T) (fun t => y t))
      ≤ L 0 / η + ((T : ℝ) * B) / η + (1 / η) * (Finset.sum (Finset.range T) (fun t => p t)) := by
  classical
  -- Sum one-step inequalities
  have hsum :
    (Finset.sum (Finset.range T) (fun t => (L (t + 1) - L t)))
      ≤ (Finset.sum (Finset.range T) (fun t => (B - η * y t + p t))) :=
    sum_le_sum (by intro t ht; exact hstep t (mem_range.mp ht))
  -- Normalize both sides
  have hL : (Finset.sum (Finset.range T) (fun t => (L (t + 1) - L t))) = L T - L 0 :=
    sum_range_telescope L T
  have hB : (Finset.sum (Finset.range T) (fun _ => B)) = (T : ℝ) * B :=
    sum_const_range_real B T
  have hy :
      (Finset.sum (Finset.range T) (fun t => (-η) * y t))
        = (-η) * (Finset.sum (Finset.range T) (fun t => y t)) :=
    sum_scale y T
  -- Alternative shape: `-∑ η*y` instead of `(-η) * ∑ y`
  have hy_neg :
      (Finset.sum (Finset.range T) (fun t => (-η) * y t))
        = - (Finset.sum (Finset.range T) (fun t => η * y t)) := by
    classical
    -- sum_neg_distrib: ∑ (-f) = -∑ f
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using
      (sum_neg_distrib (s := Finset.range T) (f := fun t => η * y t))
  -- And factor the positive scalar inside the sum
  have hy_pos :
      (Finset.sum (Finset.range T) (fun t => η * y t))
        = η * (Finset.sum (Finset.range T) (fun t => y t)) := by
    simpa [mul_sum]
  -- Combine to the exact target shape: `- (η * ∑ y)`
  have hy_alt :
      (Finset.sum (Finset.range T) (fun t => (-η) * y t))
        = - (η * (Finset.sum (Finset.range T) (fun t => y t))) := by
    simpa [hy_pos]
      using hy_neg
  -- Split the RHS sum and rewrite both sides
  have hsplit :
      (Finset.sum (Finset.range T) (fun t => (B - η * y t + p t)))
        = (Finset.sum (Finset.range T) (fun _ => B))
          + (Finset.sum (Finset.range T) (fun t => (-η) * y t))
          + (Finset.sum (Finset.range T) (fun t => p t)) := by
    classical
    -- Distribute the sum across additions
    have :
        (Finset.sum (Finset.range T) (fun t => (B - η * y t + p t)))
          = (Finset.sum (Finset.range T) (fun t => (B + ((-η) * y t + p t)))) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm]
    calc
      (Finset.sum (Finset.range T) (fun t => (B - η * y t + p t)))
          = (Finset.sum (Finset.range T) (fun t => (B + ((-η) * y t + p t)))) := this
      _ = (Finset.sum (Finset.range T) (fun _ => B))
            + (Finset.sum (Finset.range T) (fun t => ((-η) * y t + p t))) := by
              simpa [sum_add_distrib]
      _ = (Finset.sum (Finset.range T) (fun _ => B))
            + ((Finset.sum (Finset.range T) (fun t => (-η) * y t))
              + (Finset.sum (Finset.range T) (fun t => p t))) := by
              simpa [sum_add_distrib]
      _ = (Finset.sum (Finset.range T) (fun _ => B))
            + (Finset.sum (Finset.range T) (fun t => (-η) * y t))
            + (Finset.sum (Finset.range T) (fun t => p t)) := by
              ac_rfl
  -- Convert `hsum` into the shape used by `isolate_eta_sum` in two steps
  have hsum_split_raw :
    L T - L 0 ≤ (Finset.sum (Finset.range T) (fun _ => B))
        + (Finset.sum (Finset.range T) (fun t => (-η) * y t))
        + (Finset.sum (Finset.range T) (fun t => p t)) := by
    simpa [hL, hsplit] using hsum
  have hsum_split :
    L T - L 0 ≤ (Finset.sum (Finset.range T) (fun _ => B))
        + ((-η) * (Finset.sum (Finset.range T) (fun t => y t)))
        + (Finset.sum (Finset.range T) (fun t => p t)) := by
    simpa only [hy_neg, hy_pos, neg_eta_sum η y T] using hsum_split_raw
  have hcore_mul :
    L T - L 0 ≤ (T : ℝ) * B
      + ((-η) * (Finset.sum (Finset.range T) (fun t => y t)))
      + (Finset.sum (Finset.range T) (fun t => p t)) := by
    simpa only [hB] using hsum_split
  -- Isolate eta * (sum y)
  have hEtaSum := isolate_eta_sum (L:=L) (B:=B) (η:=η) (y:=y) (p:=p) (T:=T) hcore_mul
  -- Drop the negative term using L T ≥ 0
  have hEtaSum' :
      η * (Finset.sum (Finset.range T) (fun t => y t))
        ≤ L 0 + (T : ℝ) * B + (Finset.sum (Finset.range T) (fun t => p t)) := by
    exact le_trans hEtaSum (by
      have hLT := hLnonneg T
      have := drop_nonpos_term (L:=L) (T:=T) hLT
      linarith)
  -- Divide by η > 0
  have hscaled := scale_by_inv_pos hηpos hEtaSum'
  -- Normalize divisions and cancel η
  have hηne : η ≠ 0 := ne_of_gt hηpos
  -- `(1/η) * (η * S) = S`
  have : (1 / η) * (η * (Finset.sum (Finset.range T) (fun t => y t)))
      = (Finset.sum (Finset.range T) (fun t => y t)) := by
    field_simp [one_div, hηne, mul_comm, mul_left_comm, mul_assoc]
  -- Apply this to the scaled inequality (use symmetry to match `le_of_eq_of_le`)
  have := (le_of_eq_of_le this.symm hscaled)
  -- Normalize RHS and allow reassociation/commutation
  simpa [one_div, div_eq_inv_mul, mul_add, mul_assoc, mul_comm, mul_left_comm,
        add_comm, add_left_comm, add_assoc]
    using this

/-- Lemma A (average form): divide the unscaled bound by `T` (with `T > 0`). -/
theorem lemmaA_average
    (L y p : ℕ → ℝ) (B η : ℝ) (T : ℕ)
    (hTpos : 0 < T)
    (hηpos : 0 < η)
    (hLnonneg : ∀ t, 0 ≤ L t)
    (hstep : ∀ t < T, L (t + 1) - L t ≤ B - η * y t + p t) :
    (1 / (T : ℝ)) * (Finset.sum (Finset.range T) (fun t => y t))
      ≤ (L 0) / (η * (T : ℝ)) + (B / η)
        + (1 / (η * (T : ℝ))) * (Finset.sum (Finset.range T) (fun t => p t)) := by
  classical
  have U := lemmaA_unscaled L y p B η T hηpos hLnonneg hstep
  have hTposR : 0 < (T : ℝ) := by exact_mod_cast hTpos
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTposR
  have hmul := (scale_by_inv_pos (η:= (T : ℝ)) hTposR U)
  -- Normalize RHS terms (into exactly the target shapes).
  have hηne : η ≠ 0 := ne_of_gt hηpos
  have h1 :
      (1 / (T : ℝ)) * (((T : ℝ) * B) / η) = B / η := by
    have : (1 / (T : ℝ)) * ((T : ℝ) * B) = B := by
      field_simp [one_div, hTne]
    simpa [mul_div_assoc] using congrArg (fun x => x / η) this
  have h2 :
      (1 / (T : ℝ)) * (L 0 / η) = L 0 / (η * (T : ℝ)) := by
    field_simp [one_div, hTne, hηne, mul_comm, mul_left_comm, mul_assoc]
  have h3' :
      (1 / (T : ℝ)) * (1 / η) = 1 / (η * (T : ℝ)) := by
    field_simp [one_div, hTne, hηne, mul_comm, mul_left_comm, mul_assoc]
  have h3 :
      (1 / (T : ℝ)) * ((1 / η) * (Finset.sum (Finset.range T) (fun t => p t)))
        = (1 / (η * (T : ℝ))) * (Finset.sum (Finset.range T) (fun t => p t)) := by
    simpa [h3', mul_comm, mul_left_comm, mul_assoc]
  have hmul_inv :
      (Finset.sum (Finset.range T) (fun t => y t)) * (↑T)⁻¹
        ≤ (Finset.sum (Finset.range T) (fun t => p t)) * (η⁻¹ * (↑T)⁻¹)
          + (B * ↑T / η * (↑T)⁻¹ + (↑T)⁻¹ * (L 0 / η)) := by
    simpa [one_div, mul_add, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] using hmul
  have hBterm :
      B * (T : ℝ) / η * (T : ℝ)⁻¹ = B / η := by
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using h1
  have hLterm :
      (T : ℝ)⁻¹ * (L 0 / η) = L 0 / (η * (T : ℝ)) := by
    simpa [one_div] using h2
  have hmul'' :
      (Finset.sum (Finset.range T) (fun t => y t)) * (↑T)⁻¹
        ≤ B / η + ((Finset.sum (Finset.range T) (fun t => p t)) * (η⁻¹ * (↑T)⁻¹)
          + L 0 / (η * ↑T)) := by
    simpa [hBterm, hLterm, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] using hmul_inv
  have hmul_final :
      (1 / (T : ℝ)) * (Finset.sum (Finset.range T) (fun t => y t))
        ≤ B / η + ((Finset.sum (Finset.range T) (fun t => p t)) * (η⁻¹ * (↑T)⁻¹)
          + L 0 / (η * ↑T)) := by
    simpa [one_div, mul_comm, mul_left_comm] using hmul''
  -- Finish by normalizing and reordering terms
  have :
      (1 / (T : ℝ)) * (Finset.sum (Finset.range T) (fun t => y t))
        ≤ L 0 / (η * (T : ℝ)) + B / η
          + (1 / (η * (T : ℝ))) * (Finset.sum (Finset.range T) (fun t => p t)) := by
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc,
          add_comm, add_left_comm, add_assoc] using hmul_final
  simpa using this

end LeanBcpDynamicVsCtp
