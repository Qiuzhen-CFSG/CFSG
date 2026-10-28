module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Source
public import CFSG.Quasithin.ChapterG.Section10.NonfaithfulFittingSource

/-!
# G.11.5 for the original terminal action

The original rank-two construction supplies G.10 and its SQTK cover on
H/C_H(U/Z(U)). If this quotient is nonsolvable, its literal elementary
actor has nontrivial intersection with the centralizer of the Fitting
subgroup. This is the missing faithful-Fitting exclusion used to select
the component in the nonsolvable branch of 14.3.15.

No solvability, action-kernel, normal-cubic or normalizer-classification
premise is added to the original source context.
Source: Aschbacher--Smith G.11.5 and 14.3.15, printed pp.365 and994.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The source rank-two setup discharges the original G.11.5 conclusion. -/
theorem rankTwo_terminal_fitting_centralizer_ne_bot {K : GroupClass} {T : Sylow 2 G}
    {L M : Subgroup G} (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2) [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    F.terminalDot (F.X g) ⊓ centralizer (fittingSubgroup F.TerminalHdot : Set F.TerminalHdot) ≠ ⊥ := by
  obtain ⟨d,he,hx,B,v,hyp,hc⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  exact hyp.fitting_centralizer_ne_bot_of_not_solvable hc hn

/-- All preceding hypotheses are supplied by original14.2.4, on the actual
terminal quotient and its original X-image. -/
theorem original_terminal_fitting_centralizer_ne_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2) [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    F.terminalDot (F.X g) ⊓ centralizer (fittingSubgroup F.TerminalHdot : Set F.TerminalHdot) ≠ ⊥ := by
  exact rankTwo_terminal_fitting_centralizer_ne_bot
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F hne g hgP hgH hn
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
