module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankIntersection
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.SingularPlane
public import CFSG.Quasithin.ChapterG.Section10.FittingSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ReducibleExclusion

/-!
# The original actor has rank at least two in the cubic degree-four branch

A rank-one actor forces E-hat to have dimension two by original 14.3.12.
Its square form is singular and nondegenerate, and the original Sylow image
preserves it. The faithful order-nine-core action then produces a normal
cubic subgroup, contrary to the selected source's cubic-index exclusion.
Every representation, quotient and intersection is the original one.

Source: Aschbacher--Smith 14.3.15, printed p.994, degree four with cubic
Fitting commutator. The degree-two and five-core branches are separate.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {L M : Subgroup G}

/-- The literal source geometry excludes a rank-one degree-four actor
when the three-core has order nine and the group has no normal cubic. -/
theorem rankTwo_actor_rank_of_nine_core
    (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g∈F.P L) (hgH : g∉F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4)
    (h9 : Nat.card (pCore 3 F.TerminalHdot)=9)
    (hno : ∀ C : Subgroup F.TerminalHdot, C.Normal → Nat.card C=3 → False) :
    2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  by_contra! hr
  have hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))≤
      finrank (ZMod 2) (Additive F.Uhat)/2-1 := by rw [hd]; omega
  have s := rankTwo_small_actor_conclusions h F d hne g hgP hgH hyp hm
  let Q := centerPointQuadraticForm F d (by decide) s.center_point
  have hQ : ∀ a u, Q (F.terminalRepresentation a u)=Q u := by
    intro a u
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact s.invariant b u.toMul
  let P : Sylow 2 F.TerminalHdot :=
    (T.subtype (F.invariant 1)).mapSurjective (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  have hP : (P:Subgroup F.TerminalHdot)=F.terminalDot (T:Subgroup G) := rfl
  have hS : 2≤finrank (ZMod 2) (hatSpace F (F.E g)) := by
    rw [s.intersection_dimension,hd]
  have hi := rankTwo_terminal_intersection_invariant h F hne g hgP hgH
  obtain ⟨C,hCn,hCc⟩ :=
    ChapterG.Section09.FittingRecognition.Four.normal_cubic_of_nine_core_singular_plane
      F.terminalRepresentation F.terminalRepresentation_injective hd h9 Q s.nondegenerate hQ
      P (hatSpace F (F.E g)) hS s.singular (hP.symm ▸ hi)
  exact hno C hCn hCc

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
/-- Actual selected-data consumer: the solvable cubic Fitting branch in
four dimensions has the required actor rank, with no recognition callback. -/
theorem actor_rank_ge_two_of_center_point_cubic_degree_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T=∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G))={Mc})
    (hmany : 1<(maximalTwoLocalOvergroups (T:Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M)=4)
    (e : (M⧸(centralizer (localModule T M:Set G)).subgroupOf M)≃*Equiv.Perm (Fin 3))
    (hnot : ¬ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬IsMulCommutative F.U) (hZ : F.ZU=F.Vi 1)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot))
    (hs : Group.IsSolvable F.TerminalHdot) (hX : F.terminalDot (F.X g)≠⊥)
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4)
    (hc : IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,F.terminalDot (F.X g)⁆ : Subgroup F.TerminalHdot)) :
    2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  have hi := irreducible_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ g B v hyp
  let fit := hyp.fittingHypothesis_of_solvable cover hs hi
  let : Nontrivial (F.terminalDot (F.X g)) := (F.terminalDot (F.X g)).nontrivial_iff_ne_bot.mpr hX
  have hm : 0<finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := Module.finrank_pos
  have h9 := ChapterG.Section09.FittingRecognition.Four.threeCore_card_nine_of_solvable fit hm hc hd hs
  apply rankTwo_actor_rank_of_nine_core
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F d hne g hgP hgH hyp hd h9
  intro C hCn hCc
  let := hCn
  exact no_normal_cubic_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ C hCc
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
