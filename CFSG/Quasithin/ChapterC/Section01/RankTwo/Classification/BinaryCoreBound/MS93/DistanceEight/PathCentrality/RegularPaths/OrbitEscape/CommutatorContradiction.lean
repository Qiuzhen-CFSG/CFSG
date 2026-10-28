module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator.Assembly

/-!
# The R₁/R₂ contradiction for MS93 (4.4.2)

Under failure of both orbit escapes and joint normality, construct the
backward critical chain and its actual neighbor conjugator. The R₁
calculation proves that Vδ has image of order two in Gₐ/Qₐ and that
[Z_(a+2)^g,Vδ] is nontrivial. These discharge the two inputs of the R₂
calculation: it forces R₂ both to escape and to lie in ZδDδ.

Joint normality remains an explicit hypothesis for the independent first
subgroup argument to supply. The enclosing orbit-escape theorem owns that
discharge. No index, noncommutation, fixed-space or commutator identity is
an additional premise here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, second subgroup argument.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The second subgroup argument of MS93 (4.4.2). Joint normality and
failure of both orbit escapes contradict the R₁/R₂ calculation on the
constructed backward chain. All intermediate index and commutator premises
are discharged on that same configuration. -/
theorem false_of_joint_normality
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : PathCentrality.LocalCommutatorControl R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4)))
    (hnormal : stabilizer R a ≤ Subgroup.normalizer (OrbitEscape.jointSpan p)) :
    False := by
  obtain ⟨s⟩ := exists_configuration common p hb hnormal
  obtain ⟨hindex, hmove⟩ :=
    s.backward_index_two_and_conjugate_noncommutation hb common hlocal hnormal
  exact s.false_of_index_two_and_conjugate_noncommutation
    hb common hlocal hforward hreverse hnormal hindex hmove

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction

end
