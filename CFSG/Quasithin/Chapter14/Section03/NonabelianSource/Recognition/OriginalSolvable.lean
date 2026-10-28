module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankCubic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankFive
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalFactors

/-!
# The original solvable nonabelian closure

The source terminal action has nontrivial elementary actor: a trivial actor
would force degree two, which the original local movement excludes. The
larger-center source exclusion then identifies the center with the original
point. The cubic and noncubic Fitting branches both force the full four-dimensional plus-type orthogonal action. Applying the original parabolic
section constructs the two elementary factors without additional action,
rank or normalizer assumptions.

Source: Aschbacher--Smith 14.3.15 and 14.3.18(4), printed pp.995--996.
Solvability remains explicit here; the nonsolvable source branch is separate.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
theorem terminal_actor_ne_bot_from_source
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
    (d : ClosureGeometry F) (hne : ¬IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    : F.terminalDot (F.X g) ≠ ⊥ := by
  intro hbot
  let : Subsingleton (F.terminalDot (F.X g)) := ⟨fun a b => Subtype.ext (by
    have ha : (a : F.TerminalHdot)=1 := by
      exact mem_bot.mp (hbot.le a.property)
    have hb : (b : F.TerminalHdot)=1 := by
      exact mem_bot.mp (hbot.le b.property)
    exact ha.trans hb.symm)⟩
  have hzero := Group.rank_eq_zero
    ((F.terminalDot (F.X g)) ⧸
      (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))
  have hb := hyp.dimension_bound.1
  rw [hzero] at hb
  have hl := hyp.two_le_dimension
  have hd : finrank (ZMod 2) (Additive F.Uhat)=2 := by omega
  exact false_of_degree_two hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH B v hyp hd

theorem source_full_orthogonal_of_solvable
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
    (hne : ¬IsMulCommutative F.U)
    (g : G)
    (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤ := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨d,he,hx,B,v,hyp,cover⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := hx
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hX := terminal_actor_ne_bot_from_source hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH hyp
  by_cases hc : IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,F.terminalDot (F.X g)⁆ : Subgroup F.TerminalHdot)
  · exact full_orthogonal_of_center_point_cubic hG T hempty hM hu hmany hcard e hnot F d hne hZ
      g hgP hgH hyp cover hs hX hc
  · exact full_orthogonal_of_center_point_noncubic hG T hempty hM hu hmany hcard e hnot F d hne hZ
      g hgP hgH hyp cover hs hX hc

theorem source_elementary_factors_of_solvable
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
      F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (B:Set G) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,hx,B,v,hyp,cover⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
