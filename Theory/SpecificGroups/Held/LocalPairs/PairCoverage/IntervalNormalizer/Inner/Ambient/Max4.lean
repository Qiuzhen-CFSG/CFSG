module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Representatives
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.CoreWitness
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.LocalBounds
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound

/-!
# The max4 branch of the Held ambient interval calculation

The published reduction covers every labelled index-two entry containing the
certified core word. Changing the true pivot is justified by Schreier's lemma,
and a checked word identity leaves seven masks. Their actual normalizers are
bounded using orbit colors on Held's faithful degree-2058 action and matching
local subgroup lower bounds.

The entry orbit identities and colored-graph bounds are certified in the
imported modules. Their assembly proves the max4 inclusion with only the
representative orbit-cardinality premise supplied by the ambient owner.
Final assembly for both locals belongs to the parent Ambient module.

Sources: GLS3 Table 5.3p; unchanged ATLAS max4 and HeG1-p2058B0 programs.
-/

public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations (representative)

/-- The max4 calculation after the seven orbit tables and their graph bounds
are certified. The representative orbit premise is the one supplied by the
ambient assembly owner. All local witnesses and arbitrary-pivot reductions
have already been discharged. -/
theorem entry_normalizer_le_of_orbit_graph_certificates
    (hentryOrbits : ∀ (j : Fin 7) (x : Fin 2058),
      orbitSizeLabel j x = Nat.card (MulAction.orbit (candidate j) x))
    (hgraph : ∀ j : Fin 7, Nat.card (evenColoredGraphGroup j) ≤ bound j)
    (horbits : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit representative x))
    (k : Fin 4) (m : Fin 4 → Bool) (hk : m k = true)
    (hc : localWord true ^ 5 ∈ entry true k m)
    (hi : (entry true k m).relIndex (fixedSubgroup true) = 2) :
    normalizer (entry true k m : Set He) ≤ localOvergroup true :=
  entry_normalizer_le_of_certificates hentryOrbits hgraph
    (local_normalizer_card_ge_3072 horbits) horbits k m hk hc hi

/-- Every labelled max4 entry of relative index two containing the certified
core word has its ambient normalizer in the literal max4 local overgroup.
The seven entry orbit tables and graph bounds are discharged; only the
permitted representative orbit premise remains for the ambient owner. -/
theorem entry_normalizer_le
    (horbits : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit representative x))
    (k : Fin 4) (m : Fin 4 → Bool) (hk : m k = true)
    (hc : localWord true ^ 5 ∈ entry true k m)
    (hi : (entry true k m).relIndex (fixedSubgroup true) = 2) :
    normalizer (entry true k m : Set He) ≤ localOvergroup true :=
  entry_normalizer_le_of_orbit_graph_certificates
    orbitSizeLabel_eq_card_orbit evenColoredGraphGroup_card_le horbits k m hk hc hi

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
