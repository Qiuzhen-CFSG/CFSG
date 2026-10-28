module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Linear

/-!
# Shared witnesses for the Case IV finite exclusion

The witnesses concern the literal Case IV matrices in `AutomizerData`, in
the ordered basis z₁,z₃,a,d. A singular tuple carries a nonzero kernel vector;
an invertible tuple carries a word fixing the first vector outside the eight
local matrices. The accompanying scripts generate data only: every assertion
below is checked by Lean's kernel, with no external computation axiom.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, printed pp.2–3,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour.FiniteRigidity

@[expose] public def witnesses : Fin 78 → List (Fin 4) :=
  ![
    [3, 0, 3],
    [3, 3],
    [3, 0, 2, 3],
    [3, 2, 3],
    [3, 3, 3],
    [3, 0, 3, 3],
    [3, 1, 3, 3],
    [3, 3, 2, 3],
    [3, 0, 3, 3, 3],
    [3, 3, 0, 3, 3],
    [3, 1, 3, 3, 3],
    [3, 0, 1, 3, 3, 3],
    [3, 2, 3, 3, 3],
    [3, 0, 2, 3, 3, 3],
    [3, 1, 3, 3, 3, 3],
    [3, 1, 2, 3, 3, 3],
    [3, 1, 3, 3, 2, 3],
    [3, 3, 3, 2, 3],
    [3, 2, 3, 1, 3, 3],
    [3, 3, 1, 3, 3],
    [3, 0, 3, 3, 2, 3],
    [3, 1, 3, 0, 3, 3],
    [3, 3, 0, 1, 3, 3],
    [3, 0, 3, 3, 3, 3],
    [3, 3, 2, 3, 3],
    [3, 3, 1, 3, 3, 3],
    [3, 3, 0, 3],
    [3, 2, 3, 3],
    [3, 0, 2, 3, 3],
    [3, 0, 1, 3, 3],
    [3, 1, 2, 3, 3],
    [3, 3, 3, 0, 3],
    [3, 0, 3, 2, 3, 3],
    [3, 1, 3, 2, 3, 3],
    [3, 0, 1, 2, 3, 3],
    [3, 2, 3, 2, 3],
    [3, 3, 1, 3],
    [3, 2, 3, 0, 3, 3],
    [3, 2, 3, 3, 1, 3],
    [3, 3, 0, 2, 3, 3],
    [3, 3, 3, 1, 3],
    [3, 3, 2, 3, 3, 3],
    [3, 0, 1, 3],
    [3, 1, 3],
    [3, 1, 3, 1, 3],
    [3, 2, 3, 3, 3, 3],
    [3, 0, 3, 3, 1, 3],
    [3, 0, 3, 1, 3, 3],
    [3, 1, 3, 1, 3, 3],
    [3, 1, 3, 3, 1, 3],
    [3, 3, 0, 3, 1, 3],
    [3, 2, 3, 2, 3, 3],
    [3, 0, 3, 1, 3],
    [3, 3, 1, 3, 0, 3],
    [3, 2, 3, 3, 0, 3],
    [3, 0, 2, 3, 2, 3],
    [3, 3, 0, 2, 3],
    [3, 3, 1, 2, 3],
    [3, 2, 3, 3, 2, 3],
    [3, 0, 1, 3, 1, 3],
    [3, 3, 0, 1, 3],
    [3, 0, 1, 3, 0, 1, 3],
    [3, 0, 1, 2, 3],
    [3, 1, 2, 3],
    [3, 0, 3, 0, 3],
    [3, 2, 3, 1, 3],
    [3, 1, 3, 2, 3],
    [3, 0, 1, 3, 0, 3],
    [3, 3, 2, 3, 0, 3],
    [3, 1, 3, 3, 0, 3],
    [3, 0, 3, 1, 2, 3],
    [3, 0, 2, 3, 1, 3],
    [3, 0, 2, 3, 0, 3],
    [3, 1, 3, 0, 1, 3],
    [3, 0, 3, 2, 3],
    [3, 0, 3, 3, 0, 3],
    [3, 2, 3, 0, 2, 3],
    [3, 0, 1, 3, 2, 3]]

/-- Check either a nonzero kernel vector or a forbidden stabilizer word. -/
@[expose] public def Check (m : Mat) : Fin 16 ⊕ Fin 78 → Prop
  | .inl v => v ≠ 0 ∧ act m v = 0
  | .inr n => (evalMat m (witnesses n)) 0 = 1 ∧
      ∀ j : Fin 8, evalMat m (witnesses n) ≠ localTable j

public instance (m : Mat) (c : Fin 16 ⊕ Fin 78) : Decidable (Check m c) := by
  cases c <;> unfold Check <;> infer_instance

/-- An actual automorphism cannot satisfy the singular half of a certificate. -/
public theorem checked_witness (m : Mat) (c : Fin 16 ⊕ Fin 78)
    (hc : Check m c) (hinj : ∀ i : Fin 16, act m i = 0 → i = 0) :
    ∃ w : List (Fin 4), (evalMat m w) 0 = 1 ∧
      ∀ j : Fin 8, evalMat m w ≠ localTable j := by
  cases c with
  | inl v => exact False.elim (hc.1 (hinj v hc.2))
  | inr n => exact ⟨witnesses n, hc⟩

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour.FiniteRigidity
