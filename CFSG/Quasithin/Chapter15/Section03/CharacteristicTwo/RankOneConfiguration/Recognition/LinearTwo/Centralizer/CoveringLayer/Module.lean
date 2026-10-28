module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.BlockAction
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The actual binary covering module of a natural block

For a perfect short group L, the Three-Subgroup Lemma gives [U(L),L] = U(L).
Conjugation on the elementary abelian group U(L) therefore gives a full binary
representation. Its action factors through L/O₂(L), since O₂(L) centralizes U(L).
The marked block model identifies that actor with SL₂(F) and identifies the
quotient by the fixed central layer with the natural module. Thus the literal
projection U(L) → U(L)/C_U(L) is a cover in the sense of I.1.5.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
printed pp.123–125, and I.1.5, p.408. This constructs the cover used in the
L₂ case of 15.3.30, pp.1131–1132, without discarding C_U(L).
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.CoveringLayer
variable {L F : Type*} [Group L] [Field F]

theorem blockU_full_commutator [Group.IsPerfect L] :
    ⁅ChapterC.blockU L, (⊤ : Subgroup L)⁆ = ChapterC.blockU L := by
  let D := ⁅ChapterC.blockU L, (⊤ : Subgroup L)⁆
  let q := QuotientGroup.mk' D
  have ht : (⊤ : Subgroup L).map q = ⊤ := map_top_of_surjective q (QuotientGroup.mk'_surjective D)
  have hd : D.map q = ⊥ := by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hdouble : ⁅⁅(pCore 2 L).map q, (⊤ : Subgroup (L ⧸ D))⁆, (⊤ : Subgroup (L ⧸ D))⁆ = ⊥ := by
    rw [← ht, ← map_commutator, ← map_commutator]
    exact hd
  have hp : ⁅(⊤ : Subgroup (L ⧸ D)), (⊤ : Subgroup (L ⧸ D))⁆ = ⊤ := by
    rw [← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  have hz : ⁅⁅(⊤ : Subgroup (L ⧸ D)), (⊤ : Subgroup (L ⧸ D))⁆, (pCore 2 L).map q⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (by simpa only [commutator_comm] using hdouble) hdouble
  rw [hp, commutator_comm] at hz
  have hu : (ChapterC.blockU L).map q = ⊥ := by
    change (⁅pCore 2 L, (⊤ : Subgroup L)⁆).map q = ⊥
    rw [map_commutator, ht]
    exact hz
  exact le_antisymm (commutator_le_left _ _) (by
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hu)

variable [IsElementaryAbelian 2 (ChapterC.blockU L)]

noncomputable def blockBinaryAction : Representation (ZMod 2) L (Additive (ChapterC.blockU L)) where
  toFun l := (MulAut.conjNormal (H := ChapterC.blockU L) l).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by apply LinearMap.ext; intro u; change Additive.ofMul ((MulAut.conjNormal (H := ChapterC.blockU L) 1) u.toMul) = u; rw [map_one]; rfl
  map_mul' a b := by apply LinearMap.ext; intro u; change Additive.ofMul ((MulAut.conjNormal (H := ChapterC.blockU L) (a*b)) u.toMul) = _; rw [map_mul]; rfl

theorem blockBinaryAction_apply (l : L) (u : Additive (ChapterC.blockU L)) :
    blockBinaryAction l u = Additive.ofMul (ChapterC.blockConjugate L l u.toMul) := rfl

theorem blockBinaryAction_full [Group.IsPerfect L] :
    Coinvariants.ker (blockBinaryAction (L := L)) = ⊤ := by
  let C := Coinvariants.ker (blockBinaryAction (L := L))
  let D : Subgroup (ChapterC.blockU L) := C.toAddSubgroup.toSubgroup'
  have hUD : ChapterC.blockU L ≤ D.map (ChapterC.blockU L).subtype := by
    apply (blockU_full_commutator (L := L)).symm.le.trans
    apply commutator_le.mpr
    intro u hu l _
    let v : ChapterC.blockU L := ⟨u, hu⟩
    have hc := Coinvariants.sub_mem_ker (ρ := blockBinaryAction (L := L)) l (Additive.ofMul v⁻¹)
    let w := (blockBinaryAction l (Additive.ofMul v⁻¹) - Additive.ofMul v⁻¹).toMul
    refine ⟨w, hc, ?_⟩
    simp only [w, sub_eq_add_neg]
    change l * u⁻¹ * l⁻¹ * (u⁻¹)⁻¹ = ⁅u, l⁆
    rw [inv_inv]
    have he := congrArg Subtype.val (mul_comm (ChapterC.blockConjugate L l v⁻¹) v)
    simpa only [ChapterC.blockConjugate, v, coe_mul, coe_inv, commutatorElement_def, mul_assoc] using he
  apply top_unique
  intro u _
  obtain ⟨v, hv, he⟩ := hUD u.toMul.property
  have he' : v = u.toMul := Subtype.ext he
  change u.toMul ∈ D
  exact he' ▸ hv

omit [IsElementaryAbelian 2 (ChapterC.blockU L)] in
theorem blockLinearMap_ker_le_conjugation
    (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    (blockLinearMap model).ker ≤ (MulAut.conjNormal : L →* MulAut (ChapterC.blockU L)).ker := by
  rw [blockLinearMap_ker]
  intro l hl
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  change l * (u : L) * l⁻¹ = u
  rw [← hshort.core_centralizes_blockU hl u u.property, mul_inv_cancel_right]

noncomputable def blockCoverAut (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (ChapterC.blockU L) :=
  (blockLinearMap model).liftOfSurjective (blockLinearMap_surjective model)
    ⟨MulAut.conjNormal, blockLinearMap_ker_le_conjugation hshort model⟩

omit [IsElementaryAbelian 2 (ChapterC.blockU L)] in
theorem blockCoverAut_apply (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) (l : L)
    (u : ChapterC.blockU L) :
    blockCoverAut hshort model (blockLinearMap model l) u = ChapterC.blockConjugate L l u := by
  unfold blockCoverAut
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

noncomputable def blockCoverAction (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) (Additive (ChapterC.blockU L)) where
  toFun g := (blockCoverAut hshort model g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by apply LinearMap.ext; intro u; change Additive.ofMul ((blockCoverAut hshort model 1) u.toMul) = u; rw [map_one]; rfl
  map_mul' a b := by apply LinearMap.ext; intro u; change Additive.ofMul ((blockCoverAut hshort model (a*b)) u.toMul) = _; rw [map_mul]; rfl

theorem blockCoverAction_apply (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) (l : L)
    (u : Additive (ChapterC.blockU L)) :
    blockCoverAction hshort model (blockLinearMap model l) u = blockBinaryAction l u :=
  congrArg Additive.ofMul (blockCoverAut_apply hshort model l u.toMul)

theorem blockCoverAction_full [Group.IsPerfect L] (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Coinvariants.ker (blockCoverAction hshort model) = ⊤ := by
  apply top_unique
  rw [← blockBinaryAction_full (L := L)]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨l,u⟩,rfl⟩
  change blockBinaryAction l u - u ∈ Coinvariants.ker (blockCoverAction hshort model)
  rw [← blockCoverAction_apply hshort model]
  exact Coinvariants.sub_mem_ker _ _

variable [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

abbrev blockNaturalBinary : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) (Fin 2 → F) :=
  Representation.restrictScalars (Representation.specialLinearNatural 2)

noncomputable def blockCoverMap
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Additive (ChapterC.blockU L) →ₗ[ZMod 2] (Fin 2 → F) :=
  (model.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (ChapterC.blockFixed L))).toAdditiveLeft.toZModLinearMap 2

theorem blockCoverMap_surjective
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Function.Surjective (blockCoverMap model) := by
  intro v
  obtain ⟨q,hq⟩ := model.moduleIso.surjective (Multiplicative.ofAdd v)
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (ChapterC.blockFixed L) q
  exact ⟨Additive.ofMul u, congrArg Multiplicative.toAdd hq⟩

theorem blockCoverMap_intertwining (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (u : Additive (ChapterC.blockU L)) :
    blockCoverMap model (blockCoverAction hshort model g u) =
      blockNaturalBinary g (blockCoverMap model u) := by
  obtain ⟨l,rfl⟩ := blockLinearMap_surjective model g
  rw [blockCoverAction_apply, blockBinaryAction_apply]
  exact congrArg Multiplicative.toAdd (model.intertwining l u.toMul)

noncomputable def blockCoverProjection (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    (blockCoverAction hshort model).IntertwiningMap (blockNaturalBinary (F := F)) :=
  (blockCoverMap model).intertwiningMap_of_isIntertwiningMap _ _
    (blockCoverMap_intertwining hshort model)

theorem blockCoverMap_ker (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (u : Additive (ChapterC.blockU L)) :
    u ∈ (blockCoverMap model).ker ↔ u.toMul ∈ ChapterC.blockFixed L := by
  change Multiplicative.toAdd (model.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u.toMul)) = 0 ↔ _
  change model.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u.toMul) = 1 ↔ _
  rw [map_eq_one_iff _ model.moduleIso.injective]
  exact QuotientGroup.eq_one_iff u.toMul

theorem blockCoverMap_ker_le_fixed (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    (blockCoverMap model).ker ≤ Representation.OneCohomology.fixed (blockCoverAction hshort model) := by
  intro u hu g
  obtain ⟨l,rfl⟩ := blockLinearMap_surjective model g
  rw [blockCoverAction_apply, blockBinaryAction_apply]
  apply Additive.ofMul.injective
  apply Subtype.ext
  change l * (u.toMul : L) * l⁻¹ = (u.toMul : L)
  have hz : (u.toMul : L) ∈ center L := (blockCoverMap_ker model u).mp hu
  rw [mem_center_iff.mp hz l, mul_inv_cancel_right]

theorem blockCoverProjection_isCover [Group.IsPerfect L] (hshort : ChapterC.IsShort L)
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Representation.OneCohomology.IsCover (blockCoverProjection hshort model) :=
  ⟨blockCoverMap_surjective model, blockCoverMap_ker_le_fixed hshort model, blockCoverAction_full hshort model⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.CoveringLayer

end
