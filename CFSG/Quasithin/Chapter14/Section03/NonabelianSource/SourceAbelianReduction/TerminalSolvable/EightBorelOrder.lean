module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelAmbient
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.PlainOrder
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Smallness

/-!
# Ambient order and hexagon geometry on the original eight-field component

In the Mc = K join T branch, the two full ambient involution centralizers
and their literal endpoint fusion determine the order of G by Thompson's
formula. The resulting bound forces a twelve-cycle and diameter six in the
original marked completion, with no extra relation or order premise.

This discharges F.4.43 and the smallness step on these original data.
Group recognition, the cubic partner branch and final Borel exclusion remain;
the earlier genuine marked realization is still explicit.
Source: Aschbacher--Smith F.4.12--13,43 and 14.2.18--19,14.3.15,
printed pp.280,296,987,994.
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

/-- F.4.43 for the original component, with its unchanged endpoint marking. -/
theorem source_eight_marked_card_eq_triality_of_partner_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hplain : Mc = K ⊔ (T : Subgroup G)) :
    Nat.card G = Nat.card (_root_.Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_card_eq_triality_of_partner_eq
    hG hempty hM hu hmany hcard e hH r hplain

/-- The actual completion is a hexagon in the plain partner branch. Its
order bound is discharged by the original centralizer comparison. -/
theorem source_eight_marked_hexagon_of_partner_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hplain : Mc = K ⊔ (T : Subgroup G)) :
    let c := EightLargeParabolic.markedCompletion r
    let Γ := ChapterF.SourceCompletion.TrialityTwo.Completion.graph c
    (∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length) ∧
      (∀ v w, Γ.dist v w ≤ 6) ∧
      (∃ v, ∃ p : Γ.Walk v v, p.IsCycle ∧ p.length = 12) := by
  let H := K ⊔ (T : Subgroup G)
  let J := H ⊔ EightLargeParabolic.secondParabolic T M Mc H
  apply ChapterF.SourceCompletion.TrialityTwo.Completion.hexagon_metric_of_order_bound
    (EightLargeParabolic.markedCompletion r)
  exact (Nat.card_le_card_of_injective J.subtype J.subtype_injective).trans_eq
    (source_eight_marked_card_eq_triality_of_partner_eq hG T hempty hM hu hmany hcard e
      hK h8 r hplain)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
