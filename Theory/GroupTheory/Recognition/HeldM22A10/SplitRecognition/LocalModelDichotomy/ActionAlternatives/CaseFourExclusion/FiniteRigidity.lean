module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.AutomizerData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Certificate

/-!
# Rigidity of the Case IV binary automizer

An overgroup of the exact local automizer whose first-vector stabilizer is
local cannot move that vector. Indeed, multiplication by a local element
reduces any moved image to one of four vectors. The checked binary column
certificates then give a word in the overgroup which fixes the first vector
but is outside the local automizer, a contradiction.

This supplies the finite exclusion used in the Case IV elementary-normalizer
argument. It uses the literal three actions in `AutomizerData`; no identification
of GL(4,2) with A₈ or subgroup catalogue is assumed. The ambient centralizer
argument is a separate consumer of this theorem.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, printed pp.2–3,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour

/-- The exact Case IV local group admits no proper overgroup with the same
    stabilizer of the distinguished first vector. -/
public theorem automizer_rigidity (X : Subgroup (MulAut BinaryFour))
    (hlocal : localAutomizer ≤ X)
    (hstab : ∀ f : MulAut BinaryFour, f ∈ X →
      f automizerPoint = automizerPoint → f ∈ localAutomizer) :
    X = localAutomizer := by
  apply le_antisymm _ hlocal
  intro f hf
  by_cases hfix : f automizerPoint = automizerPoint
  · exact hstab f hf hfix
  obtain ⟨j, k, hk⟩ := FiniteRigidity.normalize_first f hfix
  let g := FiniteRigidity.localAut j * f
  have hg : g ∈ X := X.mul_mem (hlocal (FiniteRigidity.localAut_mem j)) hf
  obtain ⟨w, hwfix, hwout⟩ := FiniteRigidity.matrix_certificate
    (FiniteRigidity.matrix g) k hk (FiniteRigidity.matrix_nonsingular g)
  have hwmem := FiniteRigidity.evalAut_mem X hlocal g hg w
  have hwpoint : FiniteRigidity.evalAut g w automizerPoint = automizerPoint := by
    apply (FiniteRigidity.fixes_point_iff _).mpr
    rw [FiniteRigidity.matrix_evalAut]
    exact hwfix
  obtain ⟨l, hl⟩ := FiniteRigidity.matrix_of_mem_local _ (hstab _ hwmem hwpoint)
  rw [FiniteRigidity.matrix_evalAut] at hl
  exact False.elim (hwout l hl)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
