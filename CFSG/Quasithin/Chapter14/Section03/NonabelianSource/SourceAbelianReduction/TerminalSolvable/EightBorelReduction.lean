module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelNormalizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelQuotientDefs

/-!
# The remaining source inputs to the L₂(8) contradiction

The normalizer-placement theorem supplies the ambient side of the Borel
contradiction, with the actual T ∩ K. It combines with the specialized
14.3.6(1) exclusion and an identification of the intrinsic two-core quotient
to discharge the eight-row input of the terminal-solvability assembly.

Both source inputs remain explicit here. In particular an equivalence on
the dotted component does not supply the intrinsic quotient identification.
This is a conditional assembly, not unconditional 14.3.15.
Source: Aschbacher--Smith 14.3.6(1),14.3.15, printed pp.991,994.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly retaining exactly the intrinsic-quotient input and
specialized earlier-source Borel exclusion, on the actual original groups. -/
theorem source_terminal_solvable_of_eight_kernel_and_sieve
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
    (hkernel : ∀ (K : Subgroup G) (hK : ComponentLift F g K), EightImageRow F K →
      (componentDotMap F hK.le_pointNormalizer).ker = pCore 2 K)
    (hsieve : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K →
      ¬ K ≤ M →
      Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3) →
      ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M) :
    Group.IsSolvable F.TerminalHdot := by
  apply source_terminal_solvable_of_component_inputs
    hG T hempty hM hu hmany hcard e hnot F g hcases hsmall
  intro K hK h8
  obtain ⟨edot⟩ := h8.2
  let eK := (componentCoreQuotientEquivDot F hK.le_pointNormalizer (hkernel K hK h8)).trans edot
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    have h := le_normalizer_conjugateSpanBy K (T : Subgroup G)
    rwa [← h8.1] at h
  exact hsieve K hK h8 (hK.not_le hM.1.2 e) ⟨eK⟩
    ((source_eight_borel_placement hG T hempty hM hu hmany hcard e K hn eK).trans inf_le_left)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
