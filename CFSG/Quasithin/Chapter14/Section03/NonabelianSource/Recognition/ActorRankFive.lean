module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OrthogonalFull
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore.OrdinarySource
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourFiveAction

/-!
# The original five-core branch has actor rank at least two

A rank-one actor gives the original square form a singular plane in binary
four-space. The ten-zero count excludes any faithful order-five isometry.
The actual noncubic G.9.4 branch supplies a dihedral order-ten subgroup,
so it cannot have actor rank one. All forms, intersections and actions here
are the original source ones; no coordinate marking is assumed.
Source: Aschbacher--Smith 14.3.15, printed p.994.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {L M : Subgroup G}
/-- The literal square-form geometry excludes rank one if the original actor
has order divisible by five. -/
theorem rankTwo_actor_rank_of_five_dvd
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
    (h5 : 5 ∣ Nat.card F.TerminalHdot) :
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
  have hE : finrank (ZMod 2) (hatSpace F (F.E g))=2 := by
    rw [s.intersection_dimension,hd]
  exact QuadraticForm.BinaryFour.not_five_dvd_card
    F.terminalRepresentation F.terminalRepresentation_injective Q s.nondegenerate
    hd (hatSpace F (F.E g)) hE s.singular hQ h5

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
/-- The actual noncubic Fitting branch has the required actor rank. -/
theorem actor_rank_ge_two_of_center_point_noncubic
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
    (hn : ¬IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,F.terminalDot (F.X g)⁆ : Subgroup F.TerminalHdot)) :
    2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  have hi := irreducible_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ g B v hyp
  let fit := hyp.fittingHypothesis_of_solvable cover hs hi
  let : Nontrivial (F.terminalDot (F.X g)) := (F.terminalDot (F.X g)).nontrivial_iff_ne_bot.mpr hX
  have hm : 0<finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := Module.finrank_pos
  have hc := ChapterG.Section09.FittingRecognition.caseTwo_from_source fit hm hn
  obtain ⟨ec⟩ := hc.2.2
  have h5 : 5 ∣ Nat.card F.TerminalHdot := by
    have hh := (Subgroup.normalClosure ((F.terminalDot (F.X g)) : Set F.TerminalHdot)).card_subgroup_dvd_card
    rw [Nat.card_congr ec.toEquiv,DihedralGroup.nat_card] at hh
    exact dvd_trans (by decide : 5 ∣ 2 * 5) hh
  exact rankTwo_actor_rank_of_five_dvd
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F d hne g hgP hgH hyp hc.2.1 h5

/-- The original full orthogonal action, with noncubic actor rank discharged. -/
theorem full_orthogonal_of_center_point_noncubic
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
    (hn : ¬IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,F.terminalDot (F.X g)⁆ : Subgroup F.TerminalHdot)) :
    ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤ := by
  have hr := actor_rank_ge_two_of_center_point_noncubic hG T hempty hM hu hmany hcard e hnot
    F d hne hZ g hgP hgH hyp cover hs hX hn
  exact full_orthogonal_of_center_point_actor_rank hG T hempty hM hu hmany hcard e hnot
    F d hZ g B v hyp cover hs hX hr
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
