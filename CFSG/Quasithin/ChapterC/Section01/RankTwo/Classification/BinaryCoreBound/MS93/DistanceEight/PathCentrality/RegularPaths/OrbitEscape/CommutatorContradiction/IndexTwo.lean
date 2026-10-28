module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.Noncontainment
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.FixedCore.ConjugateEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.NaturalFour

/-!
# The R₁ index calculation in MS93 (4.4.2)

The backward image already has order two or four. Under order four,
the natural fixed-space calculation places every vector of U_a fixed by
Vδ inside [Z_a,Vδ]. Apply it to the actual R₁, which centralizes Vδ.
The source fixed-core calculation then places R₁ in Dδ, contradicting
the reverse-span obstruction and its containment in Uδ.

The final theorems discharge every local calculation using the source
fixed-core bounds and the compatible natural-module marking. The conjugate
escape argument also proves [Z_(a+2)^g,Vδ] ≠ 1, as required by R₂.
Both conclusions use only the retained configuration, common source facts,
b > 4, local commutator control and joint normality. The failed forward and
reverse escape bounds are unnecessary once that configuration is supplied.
The R₂ argument and the full orbit-escape contradiction remain with the
parent module.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- Exclude the index-four branch by its natural fixed-space calculation
and the printed R₁ fixed-core bounds. All extra premises remain explicit. -/
theorem backward_index_two_of_R1_controls (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p))
    (hforwardComm : ⁅localZSpan R (p.walk.getVert 2) a, Z R s.delta⁆ ≤
      Z R (p.walk.getVert 2))
    (hnatural : s.firstCommutator ≤ U R a)
    (hfixed : (Q R a).relIndex (V R s.delta) = 4 →
      s.firstCommutator ≤ ⁅Z R a, V R s.delta⁆ →
      s.firstCommutator ≤ fixedCore R s.delta)
    (hfour : (Q R a).relIndex (V R s.delta) = 4 →
      U R a ⊓ centralizer (V R s.delta : Set (FreeAmalgam R)) ≤ ⁅Z R a, V R s.delta⁆) :
    (Q R a).relIndex (V R s.delta) = 2 := by
  rcases s.backward_index_two_or_four hb common with htwo | hindex
  · exact htwo
  · have hcentral : s.firstCommutator ≤ centralizer (V R s.delta : Set (FreeAmalgam R)) :=
      commutator_eq_bot_iff_le_centralizer.mp (s.firstCommutator_centralizes_radius hb source)
    have hcomm := (le_inf hnatural hcentral).trans (hfour hindex)
    exact (s.firstCommutator_not_le_delta_fixed_of_forward_bound hb common hnorm
      hforwardComm (hfixed hindex hcomm)).elim

/-- The actual backward radius has image of order two in Gₐ/Qₐ.
The fixed-core and marked natural-module calculations exclude order four. -/
theorem backward_index_two (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    (Q R a).relIndex (V R s.delta) = 2 := by
  exact s.backward_index_two_of_R1_controls hb common hnorm
    (s.forwardSpan_commutator_le_second_Z hb common hlocal)
    (s.firstCommutator_le_start_natural hb common hlocal)
    (fun _ hcomm => s.firstCommutator_le_delta_fixed_of_le_commutator hb common hlocal hcomm)
    (s.backward_natural_fixed_le_commutator hb common)

/-- The two R₁ conclusions used by the remaining R₂ source argument,
with no additional index, fixed-space or noncommutation premise. -/
theorem backward_index_two_and_conjugate_noncommutation (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    (Q R a).relIndex (V R s.delta) = 2 ∧
      ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥ :=
  ⟨s.backward_index_two hb common hlocal hnorm,
    s.conjugate_noncommutation hb common hlocal hnorm⟩

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
