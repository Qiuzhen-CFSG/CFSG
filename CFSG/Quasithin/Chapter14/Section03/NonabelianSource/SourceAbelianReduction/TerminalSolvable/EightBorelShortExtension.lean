module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelOrder
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullGeneration

/-!
# The original eight-field component's full short centralizer and generation

Apply the characteristic short-class calculation, the cubic index cancellation
and the binary nonsplitting argument to the original ComponentLift and
EightImageRow. The full ambient short centralizer lies in the same original M,
and both full endpoints and marked base endpoints generate the original G.
The arbitrary normalizer action is transported through the actual right map;
no standard outer extension or extra fusion premise is substituted.

This discharges the cubic short-centralizer and ambient-generation steps of
Aschbacher--Smith F.4.42 and 14.2.18--19 in the original 14.3.15 branch,
printed pp.295,987,994 (`refs/quasithin.pdf`). The matching ambient sixth-power
relation, group recognition and final Borel contradiction remain open.
The genuine earlier marked inclusion-amalgam realization is still explicit.
-/
public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
include hG hempty hM hu hmany hcard e

/-- The chosen original short-root class is preserved by the full endpoint,
and its centralizer supplies the endpoint factorization. -/
theorem source_eight_marked_short_factorization
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0) :
    M = EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G)) ⊔
      (M ⊓ centralizer ({(EightLargeParabolic.markedShortRoot r a : G)} : Set G)) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_short_centralizer_factorization
    hG hempty hM hu hmany hcard e hH r a ha

/-- In the genuine cubic branch, the actual short centralizer grows by three. -/
theorem source_eight_marked_short_index_three
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hne : Mc ≠ K ⊔ (T : Subgroup G))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0) :
    let C := centralizer ({(EightLargeParabolic.markedShortRoot r a : G)} : Set G)
    (EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G)) ⊓ C).relIndex
      (M ⊓ C) = 3 := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_short_centralizer_index_three
    hG hempty hM hu hmany hcard e hH r hne a ha

/-- F.4.42 on the literal component: the full ambient short centralizer lies
in M in both the plain and cubic endpoint cases. -/
theorem source_eight_marked_short_centralizer_le
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0) :
    centralizer ({(EightLargeParabolic.markedShortRoot r a : G)} : Set G) ≤ M := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_short_centralizer_le
    hG hempty hM hu hmany hcard e hH r a ha

/-- Both the full endpoints and their original marked bases generate the
same ambient G. The earlier marked realization remains explicit. -/
theorem source_eight_marked_generation
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    Mc ⊔ M = ⊤ ∧ (K ⊔ (T : Subgroup G)) ⊔
      EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G)) = ⊤ := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact ⟨EightLargeParabolic.source_extended_eq_top
    hG hempty hM hu hmany hcard e hH r,
    EightLargeParabolic.source_generated_eq_top hG hempty hM hu hmany hcard e hH r⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
