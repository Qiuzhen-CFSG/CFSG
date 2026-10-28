module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamilySporadicSourceHS
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSource

/-!
# Removing M₁₁ and HS from the literal chosen-orbit sporadic sieve

Both cubic source exclusions apply to the unchanged orbit representation and
its actual component. The source equality with the generalized Fitting subgroup
transports the same central-quotient marking. The completed HS degree window
and outer estimates discharge the last two inputs of the conditional sieve,
leaving precisely the marked J₂ alternative in the non-Mathieu sporadic branch.
The ambient TI exclusion of J₂ belongs to the final family assembly.

Source: Aschbacher--Smith K.4 and 12.2.2, printed pp.457 and 795;
Guralnick--Malle, Classification of 2F-modules I, Theorem 6.6/Table 6.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.NonMathieuAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual chosen orbit component cannot have central quotient HS.
The original cubic source hypotheses suffice, with no FF premise. -/
theorem sourceOrbit_not_hs
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (he : Nonempty (D.orbitComponent ⧸ center D.orbitComponent ≃*
      KnownSimple.SporadicName.hs.Carrier)) : False :=
  ChapterK.SporadicCatalogue.not_hs_of_rankOne_source hs he

/-- After the M₁₁ and HS source exclusions, the non-Mathieu sporadic branch
on the literal chosen orbit has central quotient J₂. -/
theorem sourceOrbit_sporadic_j2
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    Nonempty (D.orbitComponent ⧸ center D.orbitComponent ≃*
      KnownSimple.SporadicName.j2.Carrier) :=
  (D.sourceOrbit_sporadic_j2_or_hs hs hnm hm).resolve_right (D.sourceOrbit_not_hs hs)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
