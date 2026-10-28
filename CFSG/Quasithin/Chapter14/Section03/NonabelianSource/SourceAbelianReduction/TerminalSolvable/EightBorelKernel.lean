module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelKernelComparison
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelReduction

/-!
# Discharging the L₂(8) kernel input in terminal solvability

The comparison theorem identifies the literal dotted kernel with O₂(K),
so the existing first-isomorphism equivalence supplies the intrinsic
quotient model used by the Borel sieve. This application removes precisely
`hkernel` from the earlier solvability reduction. The separate catalogue,
small-image and Borel noncontainment inputs remain explicit.

Source: Aschbacher--Smith 14.3.15, printed p.994.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original terminal-solvability reduction with its component-action
kernel premise proved. The source Borel exclusion remains independent. -/
theorem source_terminal_solvable_of_eight_sieve
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (g : G)
    (hcases : ¬ Group.IsSolvable F.TerminalHdot →
      ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K)
    (hsmall : ∀ K : Subgroup G, ComponentLift F g K → SmallImageRow F K → False)
    (hsieve : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K →
      ¬ K ≤ M →
      Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3) →
      ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M) :
    Group.IsSolvable F.TerminalHdot := by
  exact source_terminal_solvable_of_eight_kernel_and_sieve
    hG T hempty hM hu hmany hcard e hnot F g hcases hsmall
    (fun _ hK h8 => componentDotMap_ker_eq_twoCore_of_eight hG F hK h8) hsieve

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
