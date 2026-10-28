module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Geometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LocalOrbit
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LinearIntrinsic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.UnitaryIntrinsic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.Suzuki

/-!
# Rank-one Borel placement in E.6.8

`LocalOrbit` constructs the intermediate group ⟨B,Q⟩ while allowing Q to
permute components. Its characteristic-two and block-exclusion reductions
retain the actual Sylow normalizer and relative subnormality. The binary
linear, fixed-field unitary, and actual Suzuki calculations discharge every
intrinsic premise. Applying the exact universally quantified E.6.7 input
places B in M for every constructor of `Model`, away from PSL₂(4).

The opposite containment from `Geometry` then identifies B with L ∩ M.
Only the earlier source input E.6.7 remains explicit in placement; there
is no added placement, block-exclusion, or intrinsic A₃-rank premise.
The Borel action calculations and full E.6.8 alternative are separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259).
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne

open InvariantSubspaces.BlockSelection

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}

/-- Binary linear placement, with characteristic two and the exclusion of
short subnormal subgroups in finite Borel powers proved intrinsically. -/
theorem linear_sylowBorel_le
    (h67 : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (notFour : ¬ ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    sylowBorel S ≤ M :=
  sylowBorel_le_of_intrinsic h67 hU hL (linear_center_eq_bot hn iso) S hS
    (linear_sylowBorel_characteristicTwo hn iso S)
    (linear_borel_power_noShort hn iso notFour S)

/-- Fixed-field unitary placement, retaining the actual projective Borel
and the square-commutator exclusion in every finite Borel power. -/
theorem unitary_sylowBorel_le
    (h67 : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSU L 3 (2 ^ n)) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    sylowBorel S ≤ M := by
  obtain ⟨hZ, hB, hfree⟩ := unitary_sylowBorel_intrinsic hn iso S
  exact sylowBorel_le_of_intrinsic h67 hU hL hZ S hS hB hfree

/-- The rank-one placement step of E.6.8, excluding its PSL₂(4) overlap.
All three actual models discharge the intrinsic local premises, including
when Q permutes components. Only the exact earlier E.6.7 input is explicit. -/
theorem sylowBorel_le_M
    (h67 : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : Model L n) (notFour : ¬ ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    sylowBorel S ≤ M := by
  cases hm with
  | linear hn iso => exact linear_sylowBorel_le h67 hU hL hn iso notFour S hS
  | unitary hn iso => exact unitary_sylowBorel_le h67 hU hL hn iso S hS
  | suzuki m hm _ iso =>
    obtain ⟨e⟩ := iso
    exact suzuki_sylowBorel_le h67 hU hL hm e S hS

/-- The actual component intersection is its prescribed Sylow-normalizer
Borel. This discharges the placement premise of the Borel action reduction. -/
theorem sylowBorel_eq_intersection
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (h67 : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : Model L n) (notFour : ¬ ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    sylowBorel S = L ⊓ M :=
  le_antisymm (le_inf (sylowBorel_le S) (sylowBorel_le_M h67 hU hL hm notFour S hS))
    (intersection_le_sylowBorel h earlier hU hL hm S hS)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
