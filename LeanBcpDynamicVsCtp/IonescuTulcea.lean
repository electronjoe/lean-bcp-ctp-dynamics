import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.CompNotation

-- set_option diagnostics true -- noisy; uncomment locally when debugging

open MeasureTheory
open scoped ProbabilityTheory

namespace LeanBcpDynamicVsCtp

variable {α : Type*} [MeasurableSpace α]

abbrev Kernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :=
  ProbabilityTheory.Kernel α β

/-- (1) Evaluate the last coordinate on `Finset.Iic n` index subtype. -/
def lastCoord (n : ℕ) (x : (i : ↥(Finset.Iic n)) → α) : α :=
  x ⟨n, by simpa using (Finset.mem_Iic.mpr (Nat.le_refl n))⟩

lemma measurable_lastCoord (n : ℕ) : Measurable (lastCoord (α := α) n) := by
  -- Name the distinguished index to help type inference
  let i0 : ↥(Finset.Iic n) := ⟨n, by simpa using (Finset.mem_Iic.mpr (Nat.le_refl n))⟩
  simpa [lastCoord, i0] using
    (measurable_pi_apply i0 :
      Measurable (fun f : (i : ↥(Finset.Iic n)) → α => f i0))

/-- Lift a homogeneous kernel on `α` to the dependent family required by `traj`. -/
noncomputable def liftHomKernel (κ : Kernel α α)
    (n : ℕ) : Kernel ((i : ↥(Finset.Iic n)) → α) α :=
  ProbabilityTheory.Kernel.comap κ (lastCoord (α := α) n) (measurable_lastCoord (α := α) n)

instance instIsMarkovKernel_liftHomKernel
    (κ : Kernel α α) [ProbabilityTheory.IsMarkovKernel κ] (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (liftHomKernel (α := α) κ n) := by
  -- Use the Markov property stability under `comap`
  simpa [liftHomKernel] using
    (inferInstance : ProbabilityTheory.IsMarkovKernel
      (ProbabilityTheory.Kernel.comap κ (lastCoord (α := α) n)
        (measurable_lastCoord (α := α) n)))

/-- (3) Dependent kernel family expected by `traj`. -/
noncomputable def κdep (κ : Kernel α α) (n : ℕ) : Kernel ((i : ↥(Finset.Iic n)) → α) α :=
  liftHomKernel (α := α) κ n

/-- (4) Initial measure on the (trivial) zero prefix. -/
noncomputable def μprefix0 (μ0 : Measure α) : Measure ((i : ↥(Finset.Iic 0)) → α) :=
  Measure.pi (fun _ : ↥(Finset.Iic 0) => μ0)

/-- The canonical path measure on trajectories `Π n, α` built from an initial law `μ0`
and a homogeneous Markov kernel `κ` via Ionescu–Tulcea. -/
noncomputable def pathMeasure
    (μ0 : Measure α) [IsProbabilityMeasure μ0]
    (κ : Kernel α α) [ProbabilityTheory.IsMarkovKernel κ] :
    Measure (ℕ → α) := by
  classical
  let κ' : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → α) α :=
    fun n => κdep (α := α) κ n
  haveI : ∀ n, ProbabilityTheory.IsMarkovKernel (κ' n) := by
    intro n
    -- inherited from the Markov property of `κ` via `comap`
    simpa [κ', κdep, liftHomKernel] using
      (instIsMarkovKernel_liftHomKernel (α := α) (κ := κ) (n := n))
  -- Make the result type explicit to aid inference
  have Ktraj : ProbabilityTheory.Kernel ((i : ↥(Finset.Iic 0)) → α) (ℕ → α) :=
    ProbabilityTheory.Kernel.traj (X := fun _ => α) (κ := κ') (a := 0)
  exact Ktraj ∘ₘ μprefix0 μ0

/-- Coordinate process on the path space. -/
def coord (t : ℕ) (ω : (ℕ → α)) : α := ω t

lemma measurable_coord (t : ℕ) : Measurable (coord (α := α) t) := by
  simpa [coord] using (measurable_pi_apply t : Measurable (fun ω : (ℕ → α) => ω t))

end LeanBcpDynamicVsCtp
