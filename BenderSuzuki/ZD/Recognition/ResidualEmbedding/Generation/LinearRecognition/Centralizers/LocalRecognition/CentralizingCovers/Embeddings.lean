module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import Theory.SpecificGroups.Suzuki.SameParameterEmbeddings

/-!
# Comparing the two local groups in Lemma 12.3

Given actual models at the same field exponent and an inclusion `L ≤ F`,
equal models have equal orders and hence give equality. The four intrinsic
matrix-group embedding exclusions leave only PSL₂ properly contained in
one of the two actual unitary covers.

Source: GLS4, Chapter 2, Lemma 12.3, using Chapter 4, Lemma 3.9(a).
-/

noncomputable section
namespace BenderSuzuki.ZD.CentralizingCovers
open Subgroup _root_.BenderSuzuki.MatrixGroups

/-- With the exact common field exponent, a proper containment between
recognized models is necessarily the PSL₂-to-unitary case. This is the
consumer of all four explicit matrix-group embedding exclusions above. -/
public theorem eq_or_unitary_of_models
    {G : Type*} [Group G] [Finite G] {L F : Subgroup G} (hLF : L ≤ F)
    {n : ℕ}
    (hL : Nonempty (L ≃* PSL2BinaryMatrixGroup n) ∨
      ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧ Nonempty (L ≃* SuzukiMatrixGroup m))
    (hF : (Nonempty (F ≃* PSL2BinaryMatrixGroup n) ∨
      ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧ Nonempty (F ≃* SuzukiMatrixGroup m)) ∨
      IsUnitaryCentralizerCoverAt n F) :
    F = L ∨ (Nonempty (L ≃* PSL2BinaryMatrixGroup n) ∧ L < F ∧
      IsUnitaryCentralizerCoverAt n F) := by
  by_cases he : F = L
  · exact Or.inl he
  have hlt : L < F := lt_of_le_of_ne hLF (Ne.symm he)
  rcases hL with ⟨⟨eL⟩⟩ | ⟨m, hm, rfl, ⟨eL⟩⟩
  · rcases hF with (⟨⟨eF⟩⟩ | ⟨m, hm, hnm, ⟨eF⟩⟩) | hU
    · exact Or.inl (eq_of_le_of_card_ge hLF
        ((Nat.card_congr eF.toEquiv).trans (Nat.card_congr eL.toEquiv).symm).le).symm
    · subst n
      let f := eF.toMonoidHom.comp ((inclusion hLF).comp eL.symm.toMonoidHom)
      exact False.elim (psl_not_injective_suzuki m hm f
        (eF.injective.comp ((inclusion_injective hLF).comp eL.symm.injective)))
    · exact Or.inr ⟨⟨eL⟩, hlt, hU⟩
  · rcases hF with (⟨⟨eF⟩⟩ | ⟨k, hk, hmk, ⟨eF⟩⟩) | hU
    · let f := eF.toMonoidHom.comp ((inclusion hLF).comp eL.symm.toMonoidHom)
      exact False.elim (suzuki_not_injective_psl m hm f
        (eF.injective.comp ((inclusion_injective hLF).comp eL.symm.injective)))
    · have hk : k = m := by omega
      subst k
      exact Or.inl (eq_of_le_of_card_ge hLF
        ((Nat.card_congr eF.toEquiv).trans (Nat.card_congr eL.toEquiv).symm).le).symm
    · obtain ⟨E, hfield, hfinite, J, hJ, hc, hfixed, hU⟩ := hU
      let : Field E := hfield
      let : Finite E := hfinite
      rcases hU with ⟨⟨eF⟩⟩ | ⟨⟨eF⟩⟩
      · let f := eF.toMonoidHom.comp ((inclusion hLF).comp eL.symm.toMonoidHom)
        exact False.elim (suzuki_not_injective_projective_unitary m hm J hc hfixed f
          (eF.injective.comp ((inclusion_injective hLF).comp eL.symm.injective)))
      · let f := eF.toMonoidHom.comp ((inclusion hLF).comp eL.symm.toMonoidHom)
        exact False.elim (suzuki_not_injective_special_unitary m hm J hc hfixed f
          (eF.injective.comp ((inclusion_injective hLF).comp eL.symm.injective)))

end BenderSuzuki.ZD.CentralizingCovers
