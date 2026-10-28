module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.FixedCore.ConjugateEscape

/-!
# The completed R₁ subgroup controls and their index-two application

The imported fixed-core calculations prove [V,Zδ] ≤ Z_(a+2), R₁ ≤ U_a,
and R₁ ≤ Dδ whenever R₁ ≤ [Z_a,Vδ]. The conjugate escape proof supplies
[Z_(a+2)^g,Vδ] ≠ 1 from the same configuration and joint normality.
Neither the failed forward/reverse escape bounds nor any stronger critical
distance assumption is needed once the retained configuration is supplied.

The theorem below applies all these controls to the actual index-two consumer.
Its sole additional input is the independent order-four natural fixed-space
identity. That identity remains with the index-two assembly owner; it is not
needed for any of the four subgroup controls. In particular this conditional
application does not claim the complete source theorem (4.4.2).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, the R₁ calculation.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- Discharge every subgroup-control premise of the R₁ index calculation and
prove its conjugate noncommutation. Only the separate natural fixed-space
identity in the order-four branch remains an explicit input. -/
theorem backward_index_two_and_conjugate_noncommutation_of_natural_fixed_space
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p))
    (hfour : (Q R a).relIndex (V R s.delta) = 4 →
      U R a ⊓ centralizer (V R s.delta : Set (FreeAmalgam R)) ≤ ⁅Z R a, V R s.delta⁆) :
    (Q R a).relIndex (V R s.delta) = 2 ∧
      ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥ := by
  refine ⟨?_, s.conjugate_noncommutation hb common hlocal hnorm⟩
  exact s.backward_index_two_of_R1_controls hb common hnorm
    (s.forwardSpan_commutator_le_second_Z hb common hlocal)
    (s.firstCommutator_le_start_natural hb common hlocal)
    (fun _ hcomm => s.firstCommutator_le_delta_fixed_of_le_commutator hb common hlocal hcomm)
    hfour

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
