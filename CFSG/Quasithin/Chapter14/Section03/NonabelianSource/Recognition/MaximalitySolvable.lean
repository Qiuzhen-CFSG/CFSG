module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalMaximality
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalSolvable

/-!
# Source maximal elementary factors in the solvable branch

The original selected hypotheses produce the full orthogonal action and
center-point identity. The literal parabolic construction then gives two
normalised elementary factors containing every elementary subgroup of its
two-core. Solvability is the independent source branch retained here.

Source: Aschbacher--Smith 14.3.18(4), printed p.996.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_maximal_elementary_factors_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    ∃ A B : Subgroup G,
      A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧ B≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
      rankTwoSeed T M≤A ∧ rankTwoSeed T M≤B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A=16 ∧ Nat.card B=16 ∧ A⊓B=rankTwoSeed T M ∧
      A⊔B=(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
      Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2)=64 ∧
      F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G) ∧
      F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (B:Set G) ∧
      ∀E:Subgroup G,IsElementaryAbelian 2 E→E≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2→E≤A ∨ E≤B := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,hx,B,v,hyp,cover⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact maximal_elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
