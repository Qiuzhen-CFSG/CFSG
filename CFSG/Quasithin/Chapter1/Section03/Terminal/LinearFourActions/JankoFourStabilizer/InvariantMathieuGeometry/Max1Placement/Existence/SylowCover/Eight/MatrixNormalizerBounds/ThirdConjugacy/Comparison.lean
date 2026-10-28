module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Evaluation

/-!
# Ambient conjugacy to the explicit kernel-mask eight

The seven checked equations e * g = g * t give left conjugation by g⁻¹.
Both containments are proved for the literal subgroup maps, using the eight-word
carrier of max4 and the three generators of the kernel-mask subgroup.

Source context: Kleidman–Wilson (1988), pp.484–510, and Aschbacher–Smith
A.3.12. The actual finite witness is recorded in source/README.md.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Subgroup Janko4 Janko4.GeneratorCertificates

theorem conjugator_element (i : Fin 8) :
    MulAut.conj conjugator (Janko4.LocalStructure.SymmetricLinear.NormalEight.element i : Model) =
      targetElement (imageIndex i) := by
  fin_cases i
  · change MulAut.conj conjugator 1 = kernelMask 0
    rw [map_one, kernelMask_zero]
  · simp only [MulAut.conj_apply, conjugator, inv_inv]
    apply toMatrix_injective
    change toMatrix (rightConjugator⁻¹ * (Janko4.LocalStructure.SymmetricLinear.NormalEight.seed : Model) * rightConjugator) =
      toMatrix (kernelMask 1453)
    rw [matrix_mask1453]
    exact Janko4.Cardinality.KernelCount.Relations.eval_conj toMatrix Janko4.LocalStructure.SymmetricLinear.NormalEight.matrix_seed
      matrix_rightConjugator (by
        rw [← decode_packedMul, check_compare1Left,
          ← check_compare1Right, decode_packedMul])
  · simp only [MulAut.conj_apply, conjugator, inv_inv]
    apply toMatrix_injective
    change toMatrix (rightConjugator⁻¹ * (Janko4.LocalStructure.SymmetricLinear.NormalEight.e2 : Model) * rightConjugator) =
      toMatrix (kernelMask 1387)
    rw [matrix_mask1387]
    exact Janko4.Cardinality.KernelCount.Relations.eval_conj toMatrix Janko4.LocalStructure.SymmetricLinear.NormalEight.matrix_e2
      matrix_rightConjugator (by
        rw [← decode_packedMul, check_compare2Left,
          ← check_compare2Right, decode_packedMul])
  · simp only [MulAut.conj_apply, conjugator, inv_inv]
    apply toMatrix_injective
    change toMatrix (rightConjugator⁻¹ * (Janko4.LocalStructure.SymmetricLinear.NormalEight.e3 : Model) * rightConjugator) =
      toMatrix (kernelMask 1872)
    rw [matrix_mask1872]
    exact Janko4.Cardinality.KernelCount.Relations.eval_conj toMatrix Janko4.LocalStructure.SymmetricLinear.NormalEight.matrix_e3
      matrix_rightConjugator (by
        rw [← decode_packedMul, check_compare3Left,
          ← check_compare3Right, decode_packedMul])
  · simp only [MulAut.conj_apply, conjugator, inv_inv]
    apply toMatrix_injective
    change toMatrix (rightConjugator⁻¹ * (Janko4.LocalStructure.SymmetricLinear.NormalEight.e4 : Model) * rightConjugator) =
      toMatrix (kernelMask 765)
    rw [matrix_mask765]
    exact Janko4.Cardinality.KernelCount.Relations.eval_conj toMatrix Janko4.LocalStructure.SymmetricLinear.NormalEight.matrix_e4
      matrix_rightConjugator (by
        rw [← decode_packedMul, check_compare4Left,
          ← check_compare4Right, decode_packedMul])
  · simp only [MulAut.conj_apply, conjugator, inv_inv]
    apply toMatrix_injective
    change toMatrix (rightConjugator⁻¹ * (Janko4.LocalStructure.SymmetricLinear.NormalEight.e5 : Model) * rightConjugator) =
      toMatrix (kernelMask 198)
    rw [matrix_mask198]
    exact Janko4.Cardinality.KernelCount.Relations.eval_conj toMatrix Janko4.LocalStructure.SymmetricLinear.NormalEight.matrix_e5
      matrix_rightConjugator (by
        rw [← decode_packedMul, check_compare5Left,
          ← check_compare5Right, decode_packedMul])
  · simp only [MulAut.conj_apply, conjugator, inv_inv]
    apply toMatrix_injective
    change toMatrix (rightConjugator⁻¹ * (Janko4.LocalStructure.SymmetricLinear.NormalEight.e6 : Model) * rightConjugator) =
      toMatrix (kernelMask 571)
    rw [matrix_mask571]
    exact Janko4.Cardinality.KernelCount.Relations.eval_conj toMatrix Janko4.LocalStructure.SymmetricLinear.NormalEight.matrix_e6
      matrix_rightConjugator (by
        rw [← decode_packedMul, check_compare6Left,
          ← check_compare6Right, decode_packedMul])
  · simp only [MulAut.conj_apply, conjugator, inv_inv]
    apply toMatrix_injective
    change toMatrix (rightConjugator⁻¹ * (Janko4.LocalStructure.SymmetricLinear.NormalEight.e7 : Model) * rightConjugator) =
      toMatrix (kernelMask 1942)
    rw [matrix_mask1942]
    exact Janko4.Cardinality.KernelCount.Relations.eval_conj toMatrix Janko4.LocalStructure.SymmetricLinear.NormalEight.matrix_e7
      matrix_rightConjugator (by
        rw [← decode_packedMul, check_compare7Left,
          ← check_compare7Right, decode_packedMul])

/-- An unconditional conjugacy of two subgroups of the actual matrix carrier. -/
theorem map_max4Eight_eq_targetEight :
    max4Eight.map (MulAut.conj conjugator).toMonoidHom = targetEight := by
  apply le_antisymm
  · intro g hg
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    change ∃ i : Fin 8, Janko4.LocalStructure.SymmetricLinear.NormalEight.element i = w at hw
    obtain ⟨i, rfl⟩ := hw
    change MulAut.conj conjugator (Janko4.LocalStructure.SymmetricLinear.NormalEight.element i : Model) ∈ targetEight
    rw [conjugator_element]
    exact targetElement_mem _
  · apply (Subgroup.closure_le _).mpr
    have he (i : Fin 8) : targetElement (imageIndex i) ∈
        max4Eight.map (MulAut.conj conjugator).toMonoidHom := by
      rw [← conjugator_element]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _
        (show Janko4.LocalStructure.SymmetricLinear.NormalEight.element i ∈ Janko4.LocalStructure.SymmetricLinear.NormalEight.eight from ⟨i, rfl⟩))
    intro g hg
    rcases (show g = kernelMask 571 ∨ g = kernelMask 1387 ∨ g = kernelMask 198 from hg)
      with rfl | rfl | rfl
    · exact he 6
    · exact he 2
    · exact he 5

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
