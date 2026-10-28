module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.OuterAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.Quasisimple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.PreciseInputs

/-!
# The exceptional-branch consumer for the first construction in 13.6.13

The five precise earlier inputs construct the recovered outer action on
the literal star offender representation. Its exclusion combines with the
already proved full quasisimple exclusion. The actual adequate classifier
therefore leaves precisely its S₃, two-factor, and hyperplane alternatives,
with every group and module clause retained for the factor-construction owner.

The earlier inputs are B.5.1 (`qt-b05-quasisimple`), B.5.2 and B.5.5
(`qt-b05-quotient-components`), A.2.1 (`qt-a-02`), and A.3.6
(`qt-a03-sqtk-structure`). Their discharge and the full adequate classifier
remain with source assembly. No full multiplier table, recovered module
witness, factor decomposition, or desired exclusion is an extra premise.

Source: Aschbacher–Smith, B.5.7 and 13.6.13, printed pp.106 and 929.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open SourceAction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
variable [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({(A5Module.markedZ s)} : Set G))
    (hT : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hV : IsPGroup 2 V) (hL : Lv L (A5Module.markedV s) ≤ normalizer (V : Set G))
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (hsplit : Vv L (A5Module.markedZ s) (A5Module.markedV s) = zpowers (A5Module.markedV s) ⊔ ⁅V, Lv L (A5Module.markedV s)⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L (A5Module.markedV s)⁆ : Subgroup G) = 4)
    (hnormal : ¬ ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf (Gv (A5Module.markedV s))).Normal)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))} (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)

include S hS hfix hT hV hL hcard hsplit hsmall hnormal hX

/-- Source application: B.5.7's recovery discharges the recovered-action
premise on the literal star offender representation. The universal earlier
B.5.1/B.5.2/A.2.1/B.5.5/A.3.6 inputs belong to the source assembly owner. -/
theorem minimalSolvable_outer_excluded
    {K : GroupClass.{u}} (earlier : PreciseInputs.{u,u} K)
    (hlocal : IsSQTK K (Gv (A5Module.markedV s)))
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) : False := by
  obtain ⟨d⟩ := recover_star_offender_action_of_precise_inputs (A5Module.markedZ s) (A5Module.markedV s) earlier hlocal
    (Gstar_twoCore_eq_bot T (A5Module.markedZ s) (A5Module.markedV s) ⟨S, hS⟩ hfix) c
  exact minimalSolvable_outer_excluded_of_recovered s T S hS hfix hT hV hL hcard
    hsplit hsmall hnormal hX c d

/-- Consumer for the original factor-construction owner: after eliminating
both exceptional branches, every surviving native alternative retains its
full group and module data. No S₃ decomposition is assumed. -/
theorem minimalSolvable_remaining_source_alternatives
    {K : GroupClass.{u}} (earlier : PreciseInputs.{u,u} K)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} K)
    (hlocal : IsSQTK K (Gv (A5Module.markedV s))) :
    let ρ := FFFactors.offenderRepresentation (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))
    Nonempty (ChapterB.SourceInduction.SymmetricThreeCase ρ) ∨
      Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase ρ) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase ρ) := by
  have h := classify_XFamily_source L T (A5Module.markedZ s) (A5Module.markedV s) (A5Module.markedZ_mem_Gv s) S hS hfix
    classification hlocal hX.1
  cases h with
  | quasisimple hq ha =>
    exact (minimalSolvable_quasisimple_excluded L T (A5Module.markedZ s) (A5Module.markedV s)
      (A5Module.markedZ_mem_Gv s) S hS hX hq ha).elim
  | symmetricThree c => exact Or.inl ⟨c⟩
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c =>
    exact (minimalSolvable_outer_excluded s T S hS hfix hT hV hL hcard hsplit hsmall hnormal
      hX earlier hlocal c).elim
  | hyperplane c => exact Or.inr (Or.inr ⟨c⟩)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
