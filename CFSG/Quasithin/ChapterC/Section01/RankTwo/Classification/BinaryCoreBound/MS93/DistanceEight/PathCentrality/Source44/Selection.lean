module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Inside
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Noncritical

/-!
# The source backward witness

In the nonnatural branch, a displacement outside B uses noncritical
normalization, while a displacement inside B uses the proved binary
escaping-seed argument. The two cases supply the same actual local
conjugator, a critical shifted pair and the nontrivial triple commutator.
No conjugate-selection or representation callback remains.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.4.1), claim (2), printed p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

 theorem backward_witness
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hd : (cosetGraph R).dist a c=2)
    (hn : ¬⁅Z R a,Q R c⁆≤fixedCore R c)
    (hnone : ¬HasNaturalSection R a c) :
    Nonempty (BackwardWitness R geometry a c) := by
  apply exists_backwardWitness_of_case_inputs common hb ha hc hd hn hnone
  · intro _ e p g hg ht
    exact normalizes_displacement_of_containment common hb ha hd p hg ht
  · intro hB hn hnone htriple e p
    exact inside_conjugate common hb ha hc hd hB hn hnone htriple p

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
