module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.ProductSymmetric

/-!
# The four literal moved-module markings of 13.1.10

The genuine B.5 classification is applied to the reduced action of the
original normalizer. The completed irreducible and hyperplane constructions
and the remaining S5 and exceptional product constructions cover every row.
Each output marks the original moved subgroup and the actual component or
LT action. The rank-four rows include centralization of the original
Omega_1 Z(T), proved in the preceding extension and product modules.

Only the authorized earlier Thompson movement conclusion remains explicit.
Its discharge belongs to the source-supplement assembly; no module
classification, extension identity or centralization premise is added here.
The later orbit and stabilizer assembly consumes this four-way result.

Source: Aschbacher--Smith 13.1.10, printed pp.871--872.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All four source markings, under precisely the original hypotheses and
only the earlier Thompson movement conclusion. -/
theorem fourWayMarking_of_source
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    Nonempty (FourWayMarking.{u,u} T L) := by
  rcases reducedOffender_marked_or_remainingFactor h hmany hL hn hmove with hm | hd
  · exact hm
  · obtain ⟨d,hle,hd⟩ := (remainingTwoFactorCase_iff L).mp hd
    cases hd with
    | symmetricFive hm ha =>
      exact twoFactors_symmetricFive_marked h hmany hL hn hmove d hle hm ha.some
    | exceptional hm q =>
      exact twoFactors_exceptional_marked h hmany hL hn hmove d hle hm q


end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
