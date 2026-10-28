module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.AlternatingOffenders


/-!
# Full S6 image on the actual characteristic replacement

The original Baumann group lies over a point radical in its specified natural
coordinates. Restricting the projection to a characteristic replacement keeps
that containment. The alternating offender calculation then excludes image A6,
so the replacement still maps onto S6. This eliminates the alternating branch
of the MS93 reduction for the actual C.1.37 source without a radius argument.

Source: Aschbacher--Smith C.1.37 and MS93 Section 7, pp.932--933. The original
projection and its same-coordinate restrictions are retained throughout.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal]
namespace Source
variable (s : Source L R W)

/-- The replacement radical has image inside the original radical image,
under the same projection. -/
theorem reduce_radical_image_le (c : CharacteristicReduction L R) :
    c.radical.map (s.reduce c).projection ≤ R.map s.projection := by
  rw [s.reduce_projection, ← map_map,
    map_subgroupOf_eq_of_le (show c.ambient ≤ c.overgroup from le_sup_right)]
  exact map_mono (map_subtype_le c.subgroup)

/-- Invariant finite-image constraints survive characteristic replacement. -/
theorem reduce_radical_image_le_of_le (c : CharacteristicReduction L R)
    (A : Subgroup (Equiv.Perm (Fin 6))) (hA : R.map s.projection ≤ A) :
    c.radical.map (s.reduce c).projection ≤ A :=
  (s.reduce_radical_image_le c).trans hA
end Source

namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

/-- The literal original Baumann group acts inside the conjugate point
radical marked by the original natural coordinates. -/
theorem originalSource_radical_image_le (h : IntrinsicMSPair d) :
    (d.B.subgroupOf (L ⊔ d.B)).map (originalSource d h).projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
  rw [originalSource_projection, ← map_map,
    map_subgroupOf_eq_of_le (show d.B ≤ L ⊔ d.B from le_sup_right)]
  intro x hx
  obtain ⟨b,hb,rfl⟩ := hx
  have hbR : b ∈ d.R := (show d.B ≤ d.R from inf_le_left) hb
  have hbE : d.q0 b ∈ Model.E := by
    rw [d.R_eq_comap] at hbR
    exact hbR
  apply mem_map.mpr
  refine ⟨d.q0 b, ?_, ?_⟩
  · rwa [Model.pointCore_eq_exceptional]
  · change d.relabeler.val⁻¹ * (d.relabeler.val * d.q b * d.relabeler.val⁻¹) *
      (d.relabeler.val⁻¹)⁻¹ = d.q b
    group

/-- The actual characteristic replacement retains the same marked point-core
constraint. No size or Sylow assumption is added to the reduced radical. -/
theorem reducedSource_radical_image_le (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    c.radical.map ((originalSource d h).reduce c).projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj d.relabeler.val⁻¹).toMonoidHom :=
  (originalSource d h).reduce_radical_image_le_of_le c _
    (originalSource_radical_image_le d h)

/-- Every actual characteristic replacement has full S6 image. The A6
alternative is eliminated using its inherited point-radical placement. -/
theorem reducedSource_projection_surjective (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    Function.Surjective ((originalSource d h).reduce c).projection := by
  apply Source.projection_surjective_of_radical_image_le_conjugate _ d.relabeler.val⁻¹
  simpa only [Model.pointCore_eq_exceptional] using
    reducedSource_radical_image_le d h c

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
