module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSixCoverCoordinates

/-!
# The two possible orders of an alternating-six block module

The original central module projection is a perfect cover of the natural
A₆ module. The universal augmentation core surjects onto this cover, while
the cover surjects onto the natural module. Their dimensions bound the
full block module between four and five, giving orders 16 and 32.

Source: Aschbacher–Smith B.3, C.1.7 and I.1.5–6; used in 14.6.10(5), p.1029.
-/

public section
@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.AlternatingSixCoverOrder
open ExceptionalRestrictions
variable {L : Type*} [Group L]
variable (h : IsShort L)
variable [IsElementaryAbelian 2 (blockU L)] [IsElementaryAbelian 2 (BlockModule L)]
variable (m : BlockModuleModel L AlternatingSixCover.action)

private abbrev coverAction : Representation (ZMod 2) (alternatingGroup (Fin 6)) (Additive (blockU L)) := (uRepresentation h).comp m.quotientIso.symm.toMonoidHom
private def moduleCoordinates : Additive (BlockModule L) ≃ₗ[ZMod 2] natural (Fin 6) :=
  { m.moduleIso.toAdditiveLeft with map_smul' := fun a v => ZMod.map_smul m.moduleIso.toAdditiveLeft a v }
private def coverMap : Additive (blockU L) →ₗ[ZMod 2] natural (Fin 6) :=
  (moduleCoordinates m).toLinearMap.comp moduleProjection
private theorem coverMap_intertwining (g : alternatingGroup (Fin 6)) (v : Additive (blockU L)) :
    coverMap m (coverAction h m g v) = naturalRepresentation (Fin 6) g.val (coverMap m v) := by
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (m.quotientIso.symm g)
  have hq : m.quotientIso (QuotientGroup.mk' (pCore 2 L) l) = g := by
    rw [hl,m.quotientIso.apply_symm_apply]
  change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _
    ((uRepresentation h (m.quotientIso.symm g) v).toMul))) = _
  rw [←hl]
  change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _ (blockConjugate L l v.toMul))) = _
  rw [m.intertwining,hq]
  rfl
private def coverProjection : (coverAction h m).IntertwiningMap (alternatingNaturalRepresentation (Fin 6)) :=
  (coverMap m).intertwiningMap_of_isIntertwiningMap _ _ (coverMap_intertwining h m)
private theorem coverMap_ker (v : Additive (blockU L)) :
    v ∈ (coverMap m).ker ↔ v.toMul ∈ blockFixed L := by
  change m.moduleIso (QuotientGroup.mk' (blockFixed L) v.toMul) = 1 ↔ _
  rw [m.moduleIso.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff _
private theorem coverProjection_isCover : IsCover (coverProjection h m) := by
  refine ⟨(moduleCoordinates m).surjective.comp moduleProjection_surjective,?_,?_⟩
  · intro v hv g
    exact (uRepresentation_fixed h v).mpr ((coverMap_ker m v).mp hv) _
  · apply top_unique
    rw [←uRepresentation_moved h]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    have he : coverAction h m (m.quotientIso g) v = uRepresentation h g v := by
      change uRepresentation h (m.quotientIso.symm (m.quotientIso g)) v = _
      rw [m.quotientIso.symm_apply_apply]
    change uRepresentation h g v - v ∈ Coinvariants.ker (coverAction h m)
    rw [←he]
    exact Coinvariants.sub_mem_ker _ _

include h m in
private theorem cover_card [Finite L] : Nat.card (blockU L) = 16 ∨ Nat.card (blockU L) = 32 := by
  obtain ⟨f,hf,_,_⟩ := SixCover.core_quotient_of_alternating_cover
    (coverAction h m) (coverProjection h m) (coverProjection_isCover h m)
  have hhi := LinearMap.finrank_le_finrank_of_surjective hf
  have hlo := LinearMap.finrank_le_finrank_of_surjective (coverProjection_isCover h m).1
  rw [finrank_core] at hhi
  rw [finrank_natural_even (Fin 6) (by decide)] at hlo
  norm_num only [Fintype.card_fin] at hhi hlo
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (blockU L))
  rw [Nat.card_zmod] at hc
  change Nat.card (blockU L) = _ at hc
  have hn : Module.finrank (ZMod 2) (Additive (blockU L)) = 4 ∨
      Module.finrank (ZMod 2) (Additive (blockU L)) = 5 := by omega
  rcases hn with hn | hn
  · left
    norm_num [hn] at hc
    exact hc
  · right
    norm_num [hn] at hc
    exact hc
end CFSG.Quasithin.ChapterC.AlternatingSixCoverOrder
namespace CFSG.Quasithin.ChapterC
open AlternatingSixCoverOrder
variable {L : Type*} [Group L]
/-- The full commutator module of an alternating-six block has order 16 or 32. -/
theorem IsAlternatingBlock.six_module_card (hL : IsAlternatingBlock L 6) :
    Nat.card (blockU L) = 16 ∨ Nat.card (blockU L) = 32 := by
  let := hL.2.1.finite
  let := hL.2.1.elementary
  let := hL.2.1.module_elementary
  obtain ⟨rho,⟨m⟩,he⟩ := hL.2.2
  have hr : rho = AlternatingSixCover.action := by
    ext a v : 2
    exact Multiplicative.toAdd.injective (he a v)
  subst rho
  exact cover_card hL.2.1 m
end CFSG.Quasithin.ChapterC
