module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Data

/-!
# Direct access to the normalized input equations

Read the 987 original rows, normalization, and its 125 variable products by
cases. `inputRows_get_direct` proves agreement with the concatenated shared
vector. Small Gaussian certificates use this lookup to avoid repeatedly
reducing the concatenation while checking numerical identities in the kernel.
The equation order is the one in `../source/witnesses.json`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.Elimination
open Janko4.GeneratorCertificates

noncomputable def directInput (i : Fin 1113) : ℕ :=
  if h : i.val < 987 then equationRows[i.val]
  else if h : i.val = 987 then normalizationRow
  else normalizationProducts[i.val - 988]'(by omega)
theorem inputRows_get_direct (i : Fin 1113) : inputRows.get i = directInput i := by
  change ((equationRows ++ (⟨#[normalizationRow], rfl⟩ : Vector ℕ 1)) ++
    normalizationProducts)[i.val] = _
  rw [Vector.getElem_append]
  by_cases he : i.val < 987
  · have hn : i.val < 987 + 1 := by omega
    rw [dif_pos hn, Vector.getElem_append, dif_pos he]
    simp [directInput, he]
  · by_cases hn : i.val = 987
    · have hp : i.val < 987 + 1 := by omega
      rw [dif_pos hp, Vector.getElem_append, dif_neg he]
      simp [directInput, hn]
    · have hp : ¬ i.val < 987 + 1 := by omega
      rw [dif_neg hp]
      simp [directInput, he, hn]

theorem eval_zero_of_direct_xor (indices : List (Fin 1113)) (target : ℕ)
    (hcert : xorList (indices.map directInput) = target)
    (x : Coefficients) (hinputs : ∀ i, eval (inputRows.get i) x = 0) :
    eval target x = 0 := by
  apply eval_zero_of_xor inputRows indices target _ x hinputs
  rw [show inputRows.get = directInput from funext inputRows_get_direct]
  exact hcert

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.Elimination
