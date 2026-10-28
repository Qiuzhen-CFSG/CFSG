module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module.Transport.NaturalPlane

/-!
# Transport of a line in the split natural section

Orient the genuine natural marking by the seed's residual nonfixation, and
lift a line-parabolic matrix actor moving its coordinate line to the opposite
point-fixed line. Displacement in the moving summand upgrades coordinate
fixation to fixation modulo N, even for a seed with a nonzero fixed component.
The index-two quotient identifies the transported seed with the actual seed
of the natural-plane construction, giving its precise local closure, residual
actor, centralizer denominator, and equivariant two-dimensional coordinates.

This proves the generic representation transport from `SplitLineData`.
The source seed and the separate nonzero fixed subgroup are assembled by the
parent module; neither is assumed or asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(2), printed p.906;
split-section notation on p.881 and the pairing (1.7), pp.847--848.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
open RankOnePairing
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
namespace SplitLineData
variable {G : Type*} [Group G] [Finite G] {π : G →* SL} {flag : SL} {j : Bool}
  {H N X : Subgroup G} (d : SplitLineData π flag j H N X)

/-- Transport the actual seed to an opposite-parabolic fixed line and obtain
its natural rank-one factor, retaining the literal residual, local closure,
and global fixed preimage. No orientation assumption is imposed on the marking. -/
theorem transport :
    letI := d.sectionData.normal_kernel
    ∃ g : G,
      ⁅X.map (MulAut.conj g).toMonoidHom, localResidual (parabolic π flag (!j))⁆ ≤ N ∧
      Nonempty (RankOneFactor (localResidual (parabolic π flag j))
        (localGenerated (parabolic π flag j) (X.map (MulAut.conj g).toMonoidHom))
        (centralizerModulo H ⊤ N)) := by
  let := d.sectionData.normal_kernel
  let := d.sectionData.normal_group
  obtain ⟨g, k, _, hq, hx⟩ := d.transported_line
  let Y := X.map (MulAut.conj g).toMonoidHom
  have hNmap : N.map (MulAut.conj g).toMonoidHom = N := Normal.map_conj_eq N g
  have hNY : N ≤ Y := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) d.denominator_le_seed
    rwa [hNmap] at hh
  have hYH : Y ≤ H :=
    (map_mono d.seed_le_group).trans_eq (Normal.map_conj_eq H g)
  have hYker : Y ≤ π.ker :=
    (map_mono d.seed_le_kernel).trans_eq (Normal.map_conj_eq π.ker g)
  have hindex : N.relIndex Y = 2 := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      N X (MulAut.conj g).injective
    rwa [hNmap, d.line_index] at hh
  have hne : d.image Y ≠ ⊥ := by
    change d.image (X.map (MulAut.conj g).toMonoidHom) ≠ ⊥
    rw [d.image_conjugate X d.seed_le_group g]
    intro he
    exact d.image_seed_ne_bot ((Subgroup.map_eq_bot_iff_of_injective (d.image X)
      (f := (vectorAction (d.coordinates.marking (π g))).toMonoidHom)
      (vectorAction _).injective).mp he)
  have hfix : ⁅Y, parabolic π flag (!j)⁆ ≤ N := by
    apply (d.image_fixed_iff _ _ hYH).mp
    rw [d.parabolic_image,
      show ((modelParabolic flag (!j)).map d.coordinates.marking.toMonoidHom) =
        markedParabolic d.coordinates.marking flag (!j) from rfl,
      hq, fixedSpace_conj]
    change d.image (X.map (MulAut.conj g).toMonoidHom) ≤ _
    rw [hx]
    exact map_mono line_fixed_by_point
  exact ⟨g, (commutator_mono le_rfl (map_subtype_le _)).trans hfix,
    d.rankOneFactor_of_fixed Y hNY hYH hYker hindex hne hfix⟩

end SplitLineData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
