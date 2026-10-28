module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator.Noncontainment

/-!
# The R₂ contradiction from the preceding R₁ outputs

The failed forward escape and the index-two image of V_delta in G_a/Q_a
force the literal second commutator to escape Z_delta D_delta. The final
calculation identifies it with the first edge commutator, transports it by
the actual Configuration conjugator, and expresses it as the product of
the critical line and the conjugate commutator. Those factors lie in
Z_delta and D_delta respectively, giving the contradiction.

This assembles the R₂ argument with no extra noncontainment, edge identity
or transport premise. The preceding R₁ argument must still supply the
index-two image and the nonzero conjugate commutator to the enclosing
orbit-escape proof; they are the two explicit inputs of this conditional
result. The existing backward configuration is retained throughout.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, second paragraph through the final equation.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace Configuration

variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- The R₂ part of MS93 (4.4.2), conditional on the preceding R₁ outputs.
The relative index is [V_delta : V_delta intersect Q_a]. The noncontainment
in Z_delta D_delta and every premise of the final product calculation are
proved from the retained source inputs. -/
theorem false_of_index_two_and_conjugate_noncommutation
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry)
    (hlocal : PathCentrality.LocalCommutatorControl R)
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4)))
    (hnormal : stabilizer R a ≤ Subgroup.normalizer (OrbitEscape.jointSpan p))
    (hindex : (Q R a).relIndex (V R s.delta) = 2)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥) : False := by
  have hnot := s.secondCommutator_not_le_delta_Z_sup_fixed
    hb common hlocal hforward hreverse hnormal hindex hmove
  exact s.false_of_secondCommutator_not_le_delta_Z_sup_fixed hb common hlocal hmove hnot

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction

end
