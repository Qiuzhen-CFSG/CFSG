module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.FullImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.LineImage

/-!
# The actual replacement has line or full point-core image

The original point parabolic normalizes the Baumann subgroup and hence every
characteristic replacement. Its alternating four-letter subgroup cycles the
three mixed planes in the binary point radical. A maximum elementary offender
supplies the point transposition, so the replacement image is either that line
or the full eight-group. In the line case C.1.24(c) already gives the original
alternating block. All projections and subgroup inclusions are the specified
original maps, before and after characteristic replacement.

Source: Aschbacher--Smith C.1.37, pp.142--143; MS93 Section 7, pp.932--933.
This reduction removes mixed-plane radicals from the actual symplectic source;
it does not assert a critical-distance bound for the full point-core case.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

/-- The actual radical contains the marked transposition in canonical point coordinates. -/
theorem radical_image_contains_swap_of_le (g : Model.S)
    (hR : (R.map s.projection).map (MulAut.conj g).toMonoidHom ≤ Model.E) :
    ChapterB.Offenders.pairSwap 6 2 ∈
      (R.map s.projection).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨E,hE,hne,ho⟩ := s.exists_maxElementary_offender
  let A := (E.map s.projection).map (MulAut.conj g).toMonoidHom
  have hA : A ≤ Model.E := (map_mono (map_mono hE.1)).trans hR
  have hao : IsOffender Model.rho A := ⟨ho.1.map_conj g,by
    dsimp only [A]
    rw [fixedCodim_map_conj,rank_map_conj]
    exact ho.2⟩
  have hbest : IsBestOffender Model.rho A :=
    (ChapterB.Offenders.Six.isBestOffender_natural_iff _).mpr
      ((ChapterB.Offenders.Six.isOffender_natural_iff _).mp hao)
  exact (map_mono (map_mono hE.1)) (Model.best_contains_swap hA hbest)
end Source

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  let b : MulAut A := e.trans (a.trans e.symm)
  refine ⟨b y,(characteristic_iff_le_comap.mp inferInstance b) hy,?_⟩
  exact e.apply_symm_apply _

namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

noncomputable abbrev replacementAmbient
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) : Subgroup K :=
  c.ambient.map (L ⊔ d.B : Subgroup K).subtype

omit [Finite K] in
theorem normalizes_replacement
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    d.P ≤ normalizer (replacementAmbient d c : Set K) := by
  let BJ := d.B.subgroupOf (L ⊔ d.B)
  let e : BJ ≃* d.B := subgroupOfEquivOfLe (show d.B ≤ L ⊔ d.B from le_sup_right)
  let D := c.subgroup.map e.toMonoidHom
  let := c.characteristic
  let : D.Characteristic := characteristic_map_equiv e c.subgroup
  have he : D.map d.B.subtype = replacementAmbient d c := by
    rw [map_map]
    change c.subgroup.map (d.B.subtype.comp e.toMonoidHom) =
      (c.subgroup.map BJ.subtype).map (L ⊔ d.B : Subgroup K).subtype
    rw [map_map]
    rfl
  rw [← he]
  exact d.normalizes_B.trans (normalizer_le_normalizer_characteristic_image d.B D)

omit [Finite K] in
theorem replacement_image_normalized
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 ≤
      normalizer ((replacementAmbient d c).map d.q0 : Set Model.S) := by
  have hp : d.P.map d.q0 = Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 := by
    rw [d.P_eq_comap,map_comap_eq_self_of_surjective d.q0_onto]
  rw [← hp]
  exact (map_mono (normalizes_replacement d c)).trans (le_normalizer_map d.q0)

theorem replacement_image_le_pointCore
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    (replacementAmbient d c).map d.q0 ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore := by
  rw [Model.pointCore_eq_exceptional]
  apply map_le_iff_le_comap.mpr
  rw [← d.R_eq_comap]
  apply (show replacementAmbient d c ≤ d.B from ?_).trans inf_le_left
  rw [replacementAmbient, map_map]
  rintro _ ⟨x,hx,rfl⟩
  exact x.property

theorem replacement_image_eq_reduced
    (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    (replacementAmbient d c).map d.q0 =
      (c.radical.map ((originalSource d h).reduce c).projection).map
        (MulAut.conj d.relabeler.val).toMonoidHom := by
  rw [Source.reduce_projection, originalSource_projection]
  rw [← map_map, map_subgroupOf_eq_of_le
    (show c.ambient ≤ c.overgroup from le_sup_right), map_map, map_map, map_map]
  change _ = (c.subgroup.map _).map _
  rw [map_map]
  rfl

theorem replacement_image_contains_swap
    (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45 ∈
      (replacementAmbient d c).map d.q0 := by
  rw [replacement_image_eq_reduced d h c]
  apply Source.radical_image_contains_swap_of_le _ d.relabeler.val
  rw [← replacement_image_eq_reduced d h c, ← Model.pointCore_eq_exceptional]
  exact replacement_image_le_pointCore d c

theorem replacement_image_line_or_full
    (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    (replacementAmbient d c).map d.q0 =
      zpowers Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45 ∨
    (replacementAmbient d c).map d.q0 =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore := by
  classical
  by_cases hline : (replacementAmbient d c).map d.q0 ≤
      zpowers Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45
  · exact Or.inl (le_antisymm hline (zpowers_le.mpr (replacement_image_contains_swap d h c)))
  · apply Or.inr
    apply Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal.eq_core
      _ (replacement_image_le_pointCore d c)
      (Theory.SpecificGroups.SymmetricSix.BinaryFlags.K_le_H1.trans (replacement_image_normalized d c))
      (replacement_image_contains_swap d h c) hline

/-- Every actual characteristic replacement either already gives the desired
alternating block or retains the full marked point radical. -/
theorem reducedSource_block_or_full_point_image
    (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    IsAlternatingBlock L 6 ∨
    c.radical.map ((originalSource d h).reduce c).projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
  let g := d.relabeler.val
  let r := (MulAut.conj g⁻¹) Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45
  have hr : r.IsSwap := by
    change (g⁻¹ * Equiv.swap (4 : Fin 6) 5 * (g⁻¹)⁻¹).IsSwap
    rw [← Equiv.swap_apply_apply]
    exact ⟨_,_,g.symm.injective.ne (by decide),rfl⟩
  rcases replacement_image_line_or_full d h c with hline | hfull
  · apply Or.inl
    apply reducedSource_alternatingBlock_of_radical_image_swap d h c r hr
    apply (map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
    rw [← replacement_image_eq_reduced d h c, hline, MonoidHom.map_zpowers]
    have he : (MulAut.conj g) r = Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45 := by
      simp [r,MulAut.conj_apply,mul_assoc]
    exact congrArg zpowers he.symm
  · apply Or.inr
    apply (map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
    rw [← replacement_image_eq_reduced d h c, hfull, map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id Model.S := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
