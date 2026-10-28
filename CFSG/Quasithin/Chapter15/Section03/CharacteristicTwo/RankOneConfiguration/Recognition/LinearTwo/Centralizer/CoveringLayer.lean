module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.CoveringLayer.BorelAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.CoveringLayer.ResidualImage

/-!
# The full natural block layer lies in the Borel residual

Let L be a perfect short group with its actual block module marked as the
natural SL₂-module over the four-element field. Conjugation on U(L) is a binary
cover of that module. The dual-cover argument gives [U(L),B] = U(L), including
the fixed central layer C_U(L). The intrinsic prime-to-three residual of the
full Borel preimage surjects onto the matrix Borel and is normalized by U(L). Consequently
its commutators with U(L) exhaust U(L), proving the required containment.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.30,
printed pp.1131–1132; block definitions C.1.7–13, pp.123–125; covering-module
argument I.1.5 and I.2.3, pp.408 and 413. The proof uses a direct duality and
cocycle calculation, so no earlier source implication remains as a premise.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo
open CoveringLayer
variable {L F : Type*} [Group L] [Field F]

/-- Full action of a matrix subgroup puts the whole block layer into any
normalized subgroup with that matrix image. -/
private theorem blockU_le_of_full_image [IsElementaryAbelian 2 (ChapterC.blockU L)]
    (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (K : Subgroup L) (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hnorm : ChapterC.blockU L ≤ normalizer K)
    (himage : K.map (blockLinearMap model) = H)
    (hfull : Coinvariants.ker ((blockCoverAction hshort model).comp H.subtype) = ⊤) :
    ChapterC.blockU L ≤ K := by
  let D : Submodule (ZMod 2) (Additive (ChapterC.blockU L)) :=
    AddSubgroup.toZModSubmodule 2 (K.subgroupOf (ChapterC.blockU L)).toAddSubgroup
  have hD : Coinvariants.ker ((blockCoverAction hshort model).comp H.subtype) ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨h,u⟩,rfl⟩
    have hh : (h : Matrix.SpecialLinearGroup (Fin 2) F) ∈ K.map (blockLinearMap model) := by
      rw [himage]
      exact h.property
    obtain ⟨k,hk,he⟩ := hh
    change blockCoverAction hshort model (h : Matrix.SpecialLinearGroup (Fin 2) F) u - u ∈ D
    rw [← he, blockCoverAction_apply, blockBinaryAction_apply]
    change (ChapterC.blockConjugate L k u.toMul / u.toMul : ChapterC.blockU L).val ∈ K
    simp only [div_eq_mul_inv]
    have hc := le_normalizer_iff_commutator_le_right.mp hnorm
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator hk u.toMul.property)
  rw [hfull] at hD
  intro u hu
  exact hD (show Additive.ofMul (⟨u,hu⟩ : ChapterC.blockU L) ∈ (⊤ : Submodule (ZMod 2) _) from trivial)

private theorem blockU_le_blockBorel
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    ChapterC.blockU L ≤ blockBorel model := by
  intro u hu
  have hk : u ∈ (blockLinearMap model).ker := by
    rw [blockLinearMap_ker]
    exact ChapterC.blockU_le_core hu
  change blockLinearMap model u ∈ Matrix.SpecialLinearGroup.rankOneBorel F
  rw [MonoidHom.mem_ker.mp hk]
  exact one_mem _

private theorem blockU_normalizes_blockBorelResidual
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    ChapterC.blockU L ≤ normalizer (blockBorelResidual model) := by
  apply (blockU_le_blockBorel model).trans
  have hn := (primeToResidual 3 (blockBorel model)).le_normalizer_map (blockBorel model).subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, blockBorelResidual] using hn


/-- The entire elementary block layer, including C_U(L), is contained in the
intrinsic prime-to-three residual of the full matrix-Borel preimage. -/
theorem blockU_le_blockBorelResidual [Group.IsPerfect L] [Finite F] [CharP F 2]
    (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (hF : Nat.card F = 4) : ChapterC.blockU L ≤ blockBorelResidual model := by
  let := hshort.finite
  let := hshort.elementary
  exact blockU_le_of_full_image hshort model _ _
    (blockU_normalizes_blockBorelResidual model)
    (blockBorelResidual_image model hF) (blockCoverAction_borel_full hshort model hF)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
