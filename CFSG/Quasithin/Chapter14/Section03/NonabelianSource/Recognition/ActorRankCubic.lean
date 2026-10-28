module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.DegreeTwo
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OrthogonalFull

/-!
# The cubic source branch has actor rank at least two

The solvable irreducible Fitting reduction leaves degree two, cubic degree
four, or actor rank two. The first branch is excluded by the original
point-kernel argument, and the second by the literal Sylow-invariant singular
intersection. The five-core branch remains a separate source obligation.
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
/-- The actual center-point cubic branch has actor rank at least two,
with degree two excluded by the original selected source. -/
theorem actor_rank_ge_two_of_center_point_cubic
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
    (hc : IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,F.terminalDot (F.X g)⁆ : Subgroup F.TerminalHdot)) :
    2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  have hi := irreducible_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ g B v hyp
  let fit := hyp.fittingHypothesis_of_solvable cover hs hi
  let : Nontrivial (F.terminalDot (F.X g)) := (F.terminalDot (F.X g)).nontrivial_iff_ne_bot.mpr hX
  have hm : 0<finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := Module.finrank_pos
  rcases ChapterG.Section09.FittingRecognition.source_cubic_degree_cases fit hm hc with
      h2 | ⟨_,hd⟩ | ⟨hr,_⟩ | ⟨hr,_⟩
  · exact (false_of_degree_two hG T hempty hM hu hmany hcard e hnot F d hne
      g hgP hgH B v hyp h2.2.1).elim
  · exact actor_rank_ge_two_of_center_point_cubic_degree_four hG T hempty hM hu hmany
      hcard e hnot F d hne hZ g hgP hgH hyp cover hs hX hd hc
  · omega
  · omega

/-- Full original orthogonal action in the solvable center-point cubic
branch, with the actor-rank premise now discharged. -/
theorem full_orthogonal_of_center_point_cubic
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
    (hc : IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,F.terminalDot (F.X g)⁆ : Subgroup F.TerminalHdot)) :
    ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤ := by
  have hr := actor_rank_ge_two_of_center_point_cubic hG T hempty hM hu hmany hcard e hnot
    F d hne hZ g hgP hgH hyp cover hs hX hc
  exact full_orthogonal_of_center_point_actor_rank hG T hempty hM hu hmany hcard e hnot
    F d hZ g B v hyp cover hs hX hr
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
