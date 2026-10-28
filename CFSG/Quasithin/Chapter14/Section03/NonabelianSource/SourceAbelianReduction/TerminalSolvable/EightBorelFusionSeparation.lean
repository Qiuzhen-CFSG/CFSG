module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelFusionFixed
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionSeparation

/-!
# Short-root nonfusion on the literal eight-field component

Apply the intrinsic first-endpoint orbit obstruction to the original
ComponentLift/EightImageRow core. The checked equality K join T = K supplies
the core transport. No assumption that Mc equals K is made: the same proof
includes the cubic partner extension.

The marked amalgam remains the independent earlier input owned by
qt-e-1427-eight-amalgam-recognition. The matching sixth-power relation,
ambient generation and final Borel exclusion remain with
qt-e-14315-eight-borel-exclusion. Source: Aschbacher--Smith F.4.35, p.292;
14.2.18--19 and 14.3.15, pp.987,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
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

/-- The original central involution cannot be fused to the marked short-root
representative in the extracted eight-field core, including cubic Mc. -/
theorem source_eight_marked_higher_short_not_fused
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (htQ : MulAut.conj a z∈K.pCoreIn 2)
    (d : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one))
    (hshort : (r.left ⟨MulAut.conj a z,(show K≤K ⊔ (T:Subgroup G) from le_sup_left) (pCoreIn_le 2 K htQ)⟩).val=
      _root_.Triality.Standard.RadicalCoordinates.LeviCommutators.short
        (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one) rfl 2 d) : False := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have htQ' : MulAut.conj a z∈(K ⊔ (T:Subgroup G)).pCoreIn 2 := by
    simpa only [hjoin] using htQ
  apply EightLargeParabolic.source_higher_short_not_fused
    hG hempty hM hu hmany hcard e hH r a ha hz hz1 htQ' d
  rw [EightLargeParabolic.firstCoreEquiv_val]
  exact hshort
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
