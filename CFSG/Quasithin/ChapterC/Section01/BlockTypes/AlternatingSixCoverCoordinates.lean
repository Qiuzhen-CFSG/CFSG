module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import Theory.Representation.BinaryPermutationSixCover.Recognition
public import Theory.Representation.BinaryPermutationMulAction

/-!
# Full coordinates for an alternating-six block of order 32

The short-group commutator identity makes the actual map
U(K) → U(K)/C_U(K) a perfect central cover. The binary alternating-six
universal cover identifies its full order-32 module with the augmentation
core. Both the original quotient marking and the original module projection
are retained; no splitting of K is required.

Source: Aschbacher–Smith, B.3.1–3, C.1.7, I.1.5–6; the rank-five
branch of 14.6.10(5), printed pp.1029–1030.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.AlternatingSixCover
open ExceptionalRestrictions
abbrev action := (naturalMulAction (Fin 6)).comp (alternatingGroup (Fin 6)).subtype
variable {L : Type*} [Group L]
variable (h : IsShort L)
variable [IsElementaryAbelian 2 (blockU L)] [IsElementaryAbelian 2 (BlockModule L)]
variable (m : BlockModuleModel L action)

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

include h in
/-- Full augmentation coordinates above the specified natural-module model. -/
theorem exists_core_coordinates [Finite L] (hc : Nat.card (blockU L) = 32) :
    ∃ E : blockU L ≃* Multiplicative (core (Fin 6)),
      (∀ l u, (E (blockConjugate L l u)).toAdd =
        coreRepresentation (Fin 6) (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)).val (E u).toAdd) ∧
      (∀ u, coreToNatural (Fin 6) (E u).toAdd =
        (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd) := by
  obtain ⟨E,hE,hq,_⟩ := SixCover.core_equiv_of_card_thirtyTwo
    (coverAction h m) (coverProjection h m) (coverProjection_isCover h m) hc
  refine ⟨E.toAddEquiv.toMultiplicativeRight,?_,fun u => hq (Additive.ofMul u)⟩
  intro l u
  have he := hE (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (Additive.ofMul u)
  change E (uRepresentation h (m.quotientIso.symm (m.quotientIso _)) _) = _ at he
  rw [m.quotientIso.symm_apply_apply] at he
  exact he
end CFSG.Quasithin.ChapterC.AlternatingSixCover
namespace CFSG.Quasithin.ChapterC
open AlternatingSixCover
variable {L : Type*} [Group L]
/-- The full order-32 module of an alternating-six block is the augmentation
core, retaining the original natural-quotient map and alternating marking. -/
theorem IsAlternatingBlock.six_core_coordinates (hL : IsAlternatingBlock L 6)
    (hc : Nat.card (blockU L) = 32) :
    ∃ m : BlockModuleModel L action,
    ∃ E : blockU L ≃* Multiplicative (core (Fin 6)),
      (∀ l u, (E (blockConjugate L l u)).toAdd =
        coreRepresentation (Fin 6) (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)).val (E u).toAdd) ∧
      (∀ u, coreToNatural (Fin 6) (E u).toAdd =
        (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd) := by
  let := hL.2.1.finite
  let := hL.2.1.elementary
  let := hL.2.1.module_elementary
  obtain ⟨rho,⟨m⟩,he⟩ := hL.2.2
  have hr : rho = action := by
    ext a v : 2
    exact Multiplicative.toAdd.injective (he a v)
  subst rho
  exact ⟨m,exists_core_coordinates hL.2.1 m hc⟩
end CFSG.Quasithin.ChapterC
