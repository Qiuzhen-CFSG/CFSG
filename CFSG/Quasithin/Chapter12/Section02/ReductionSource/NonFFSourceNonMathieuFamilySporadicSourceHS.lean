module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamilySporadicSourceM11
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHS

/-!
# The remaining HS inputs on the literal chosen orbit

The degree-window and outer-estimate obligations apply to the unchanged orbit
representation and its actual component, using the generic F* transport.
With both obligations discharged, the non-Mathieu sporadic sieve leaves J₂.
The inner HS calculation and M₁₁ exclusion are already unconditional; this
module retains the two remaining HS obligations for their assembly owner.

Source: Aschbacher--Smith, K.4 and 12.2.2, printed pp.457 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.NonMathieuAssembly
open ChapterK.SporadicCatalogue
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The HS source assembly acts on the actual chosen orbit. Both remaining
representation inputs are explicit and must be discharged by final assembly. -/
theorem sourceOrbit_not_hs_of_degree_and_outer
    (hdegree : HigmanSimsDegreeWindow.{u,u})
    (houter : HigmanSimsOuterEstimates.{u,u})
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (he : Nonempty (D.orbitComponent ⧸ center D.orbitComponent ≃*
      KnownSimple.SporadicName.hs.Carrier)) : False :=
  not_hs_of_rankOne_source_of_degree_and_outer hdegree houter hs he

/-- Once the two HS inputs are proved, only J₂ remains in the marked
non-Mathieu sporadic branch. Its ambient TI exclusion stays with the family owner. -/
theorem sourceOrbit_sporadic_j2_of_degree_and_outer
    (hdegree : HigmanSimsDegreeWindow.{u,u})
    (houter : HigmanSimsOuterEstimates.{u,u})
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    Nonempty (D.orbitComponent ⧸ center D.orbitComponent ≃*
      KnownSimple.SporadicName.j2.Carrier) :=
  (D.sourceOrbit_sporadic_j2_or_hs hs hnm hm).resolve_right
    (D.sourceOrbit_not_hs_of_degree_and_outer hdegree houter hs)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
