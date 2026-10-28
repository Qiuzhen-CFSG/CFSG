module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.CatalogueCores
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.G2

/-!
# Rank-two quotient parabolic recognition

The actual component intersection in the centralizer quotient contains its
Sylow Borel and is maximal among proper Sylow-invariant Borel overgroups.
The complete source catalogue supplies a proper Borel join and
self-centralizing two-cores, including the larger-field PSp₄ and G₂ cases.
Characteristic-two maximality from 15.3.41 identifies this join with the
local intersection and proves the exact `QuotientParabolic` contract.

Both geometric inputs are discharged here, retaining the central covers,
rank-one groups and small-derived models. The final selection of the
p.1139 alternatives remains with the parent selection argument.

Source: Aschbacher--Smith, 15.3.41 and the first paragraph of the final proof
of 15.3.35, printed pp.1138--1139; 1.1.5(3)(a)--(c), pp.501--502.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {L MI Yplus S : Subgroup G} [L.Normal]

/-- All proper invariant Borel overgroups of the actual quotient component
have self-centralizing two-cores, with every catalogue producer discharged. -/
theorem quotient_parabolic_cores (d : Setup L MI Yplus S)
    {z : G} {α : MulAut L} (a : SourceAction L S z α) :
    ∀ Q : Subgroup (CentralizerQuotient L),
      sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ≤ Q →
      Q < centralizerQuotientComponent L →
      S.map (centralizerQuotientMap L) ≤ normalizer (Q : Set (CentralizerQuotient L)) →
      centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q :=
  quotient_parabolic_cores_of_split_core_producers d a
    (fun _ hn hm => symplecticFour_borelOvergroupCores hn hm)
    (fun _ _ hm => g2_borelOvergroupCores hm)

/-- The local component intersection in I/C_I(L) is the maximal invariant
parabolic required in the first paragraph of the final proof of 15.3.35. -/
theorem quotientParabolic (d : Setup L MI Yplus S)
    {z : G} {α : MulAut L} (a : SourceAction L S z α) :
    QuotientParabolic L MI S :=
  quotientParabolic_of_borel_join_and_cores d
    (quotient_borel_join_proper d a) (quotient_parabolic_cores d a)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
