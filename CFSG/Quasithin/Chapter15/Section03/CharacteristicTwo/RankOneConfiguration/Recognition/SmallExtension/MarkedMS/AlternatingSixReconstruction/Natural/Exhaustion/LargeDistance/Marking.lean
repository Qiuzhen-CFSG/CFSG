module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Inputs

/-!
# Literal kernel and component of the full symmetric marking

A full symmetric action on the natural central quotient has kernel exactly
the replacement two-core. Its component map agrees with the previously
chosen natural marking, so the component image is exactly A₆. The projection
from the entire moved cover is equivariant for this same S₆ marking.

These consequences feed the Section 5 source contract without adding a
splitting, Sylow-radical, or point-radical-image assumption.
Source: MS93 (3.8) and (5.0), pp.877--879 and913.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    {h : SmallMSPair κ L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

namespace FullSymmetricAction

theorem projection_kernel : s.projection.ker = pCore 2 d.overgroup := by
  have he : (BinaryPermutation.naturalRepresentation (Fin 6)).comp s.projection =
      replacementAction h e hz hn d := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact (s.action g v).symm
  rw [← replacementAction_kernel h e hz hn d, ← he,
    MonoidHom.ker_comp_of_injective _ _
      (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide))]

/-- Both markings agree on the literal residual component. -/
theorem projection_component (k : replacementComponent d) :
    s.projection k = (componentMap h e hz hn d k : Equiv.Perm (Fin 6)) := by
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact (s.action k v).symm.trans (replacementAction_component h e hz hn d k v)

/-- The actual component image is the alternating subgroup of the same six letters. -/
theorem component_image : (replacementComponent d).map s.projection =
    alternatingGroup (Fin 6) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [s.projection_component ⟨k, hk⟩]
    exact (componentMap h e hz hn d ⟨k, hk⟩).property
  · intro hg
    obtain ⟨k, hk⟩ := componentMap_surjective h e hz hn d ⟨g, hg⟩
    refine ⟨k, k.property, ?_⟩
    rw [s.projection_component, hk]

/-- The full central cover, not only its abstract quotient, carries this action. -/
theorem cover_conjugate (g : d.overgroup) (v w : replacementMoved d)
    (hw : (w : d.overgroup) = g * (v : d.overgroup) * g⁻¹) :
    (coverProjection h e hz hn d w).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (s.projection g)
        (coverProjection h e hz hn d v).toAdd :=
  (coverProjection_conjugate h e hz hn d g v w hw).trans (s.action g _)

end FullSymmetricAction
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

