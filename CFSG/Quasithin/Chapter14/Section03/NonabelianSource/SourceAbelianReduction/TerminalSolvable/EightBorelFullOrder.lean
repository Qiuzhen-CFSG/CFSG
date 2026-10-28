module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelShortExtension
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullGeometry

/-!
# Exact order and elimination of the cubic case on the original component

The marked component's ambient involution centralizers give Thompson's order
formula with the common endpoint index. The original generated completion
has hexagon geometry, whose odd shells recover the native order. Thus the
index is one. In particular the original component K is Mc, and the second
marked endpoint is the original M. No replacement amalgam is introduced.

This discharges the cubic order and smallness steps of F.4.43 and 14.2.18--19
on the literal ComponentLift/EightImageRow. The matching ambient relation,
recognition and the original Borel contradiction remain; the genuine earlier
marked realization remains an explicit premise.
Source: Aschbacher--Smith F.4.12--13,43 and 14.3.15, pp.280,296,994.
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

/-- The full order comparison retains the literal endpoint index. -/
theorem source_eight_marked_card_eq_triality_mul_index
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    Nat.card G = Nat.card (_root_.Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) *
      (K ⊔ (T : Subgroup G)).relIndex Mc := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_card_eq_triality_mul_index
    hG hempty hM hu hmany hcard e hH r

/-- The original ambient order equals the native triality order; no partner
branch or ambient isomorphism is assumed. -/
theorem source_eight_marked_card_eq_triality
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    Nat.card G = Nat.card (_root_.Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_card_eq_triality
    hG hempty hM hu hmany hcard e hH r

/-- Both original full endpoints equal their marked bases, and K itself is Mc. -/
theorem source_eight_marked_endpoints_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    Mc = K ∧ EightLargeParabolic.secondParabolic T M Mc K = M := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have hh := EightLargeParabolic.source_endpoints_eq hG hempty hM hu hmany hcard e hH r
  simpa only [source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r] using hh

/-- The actual original marked completion is a generalized hexagon in every
partner case. Its bound follows from the ambient centralizers and census. -/
theorem source_eight_marked_hexagon
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    let Γ := ChapterF.SourceCompletion.TrialityTwo.Completion.graph c
    (∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length) ∧
      (∀ v w, Γ.dist v w ≤ 6) ∧
      (∃ v, ∃ p : Γ.Walk v v, p.IsCycle ∧ p.length = 12) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_hexagon hG hempty hM hu hmany hcard e hH r

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
