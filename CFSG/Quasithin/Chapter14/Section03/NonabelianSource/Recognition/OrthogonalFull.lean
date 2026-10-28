module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ReducibleExclusion
public import CFSG.Quasithin.ChapterG.Section10.SixOrthogonalSource
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.FullOrthogonal

/-!
# The full orthogonal action on the original rank-two terminal quotient

The center-point cubic-index argument forbids a normal cubic subgroup in
the actual dotted group. The original G.10 solvable Fitting reduction, given
the source actor rank bound, yields the index-two orthogonal action.
The marked four-group and the cubic exclusion make this action the full
O₄⁺(2) action, preserving the original quotient representation.

Source: Aschbacher--Smith 14.3.15, printed p.994.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original center-point, rank-two solvable branch has the full
orthogonal four-space action. -/
theorem full_orthogonal_of_center_point_actor_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hcover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot))
    (hs : Group.IsSolvable F.TerminalHdot)
    (hX : F.terminalDot (F.X g) ≠ ⊥)
    (hr : 2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) :
    ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤ := by
  have hi := irreducible_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ g B v hyp
  let hfit := hyp.fittingHypothesis_of_solvable hcover hs hi
  have hno : ∀ C : Subgroup F.TerminalHdot, C.Normal → Nat.card C = 3 → False := by
    intro C hC hCc
    let := hC
    exact no_normal_cubic_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ C hCc
  have hcase := hyp.orthogonal_case_of_actor_rank_and_no_normal_cubic hcover hs hi hX hr hno
  have hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 2 := hcase.1
  have hA : Nat.card (F.terminalDot (F.X g)) = 4 := by
    have hc := hfit.card_actor
    rw [hm] at hc
    simpa using hc
  exact hcase.full_orthogonal_of_no_normal_cubic (F.terminalDot (F.X g)) hA hno

set_option linter.unusedVariables false in
/-- The original center-point, rank-two solvable branch has the full
orthogonal four-space action. -/
theorem full_orthogonal_of_center_point_rank_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hcover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot))
    (hs : Group.IsSolvable F.TerminalHdot)
    (hX : F.terminalDot (F.X g) ≠ ⊥)
    (hr : 2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) :
    ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤ := by
  exact full_orthogonal_of_center_point_actor_rank hG T hempty hM hu hmany hcard e hnot
    F d hZ g B v hyp hcover hs hX hr

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
