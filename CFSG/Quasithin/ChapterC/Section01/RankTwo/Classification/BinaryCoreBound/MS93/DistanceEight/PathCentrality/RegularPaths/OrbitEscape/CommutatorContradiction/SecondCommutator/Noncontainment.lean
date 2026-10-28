module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator.Noncontainment.NaturalExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator.Noncontainment.SmallDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator.Noncontainment.Recognition

/-!
# The two sides of the remaining R₂ representation argument

The failed forward span excludes the full natural section of V_a/Z_a,
and genuine conjugation gives the same exclusion at delta. Conversely,
containment of R₂ in Z_delta D_delta and the index-two hypothesis produce
an actual critical involution with displacement at most two modulo
Z_delta D_delta.

The source-specific representation implication is supplied by the recognition
module: the actual critical involution, its marked local action and the
index-two hyperplane produce a full natural section. This module assembles
that implication with the forward-span exclusion to prove the requested R₂
noncontainment theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.2), printed p.893.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace Configuration

variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- The proper forward span and the source binary recognition implication are
incompatible with the index-two containment of the literal second commutator.

This is the final noncontainment step in (4.4.2): containment yields the full
radius natural section via `radius_naturalSection_of_secondCommutator_le`, while
the failed forward escape excludes that section at the same vertex. -/
theorem secondCommutator_not_le_delta_Z_sup_fixed
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4)))
    (hnormal : stabilizer R a ≤ Subgroup.normalizer (OrbitEscape.jointSpan p))
    (hindex : (Q R a).relIndex (V R s.delta) = 2)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥) :
    ¬ s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta := by
  have _ := hreverse
  have _ := hnormal
  intro hcontain
  have hsection := s.radius_naturalSection_of_secondCommutator_le
    hb common hlocal hindex hmove hcontain
  exact s.no_radius_naturalSection_at hb common hforward s.delta_color hsection

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction

end
