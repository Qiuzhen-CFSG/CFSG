module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinarySecondCore
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenCentralizerStructure

/-! # The original binary center plane and order-seven centralization -/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCenterProfile
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction Noncommuting NoncommutingProfile CommutingOneProfile CommutingNontrivial

private theorem seven_centralizes_four {E : Type*} [Group E] [Finite E]
    (C Z : Subgroup E) (hC : Nat.card C=7) (hZ : Nat.card Z=4)
    (hn : C≤normalizer (Z:Set E)) : Z≤centralizer (C:Set E) := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let native := conjMulDistribMulActionOfLeNormalizer C Z hn
  let _ : MulDistribMulAction C Z := native
  let _ : SMul C Z := native.toSMul
  let _ : MulAction C Z := native.toMulAction
  let fixed := FixedPoints.subgroup C Z
  have hp : IsPGroup 7 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hm := hp.card_modEq_card_fixedPoints Z
  change Nat.card Z % 7=Nat.card fixed % 7 at hm
  have hle : Nat.card fixed≤Nat.card Z :=
    Nat.card_le_card_of_injective (Subtype.val : fixed→Z) Subtype.val_injective
  have hf : fixed=⊤ := fixed.eq_top_of_card_eq (by
    rw [hZ] at hm hle ⊢
    rw [Nat.mod_eq_of_lt (by decide),Nat.mod_eq_of_lt (by omega)] at hm
    omega)
  intro z hz
  apply mem_centralizer_iff.mpr
  intro c hc
  have hzfix : (⟨z,hz⟩:Z)∈fixed := hf ▸ mem_top _
  have hh := congrArg Subtype.val (((FixedPoints.mem_subgroup (M := C) (a := (⟨z,hz⟩:Z))).mp hzfix) (⟨c,hc⟩:C))
  change c*z*c⁻¹=z at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

private theorem pair_binary_center {G : Type*} [Group G] {K U S : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    let F := reducedFamily ![U,K] S
    let α := base F false
    Nat.card (Z F α)=4 ∧
      Z F α≤(ballKernel F α 2).pCoreIn 2 ∧ center (graphLocalGroup F α)=⊥ := by
  let F := reducedFamily ![U,K] S
  let α := base F false
  let β := base F true
  have hb : b F=2 := (pair_b_swap K U S).trans
    (SourceCriticalGeometry.critical_distance_two h eK eU)
  obtain ⟨u,hc,hne,hβu⟩ := SourceCriticalGeometry.reversed_base_critical h eK eU
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
    reduced_bTwo_center_action_exists h.swap hc hne hb hab hβu
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let e0 := (reduced_graphLinearQuotient h.swap false
    ((eU.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
      (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))).trans
        (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (ZMod 2)).symm
  have hk := MixedDGS.source_action_field_card h.swap hactor c.quotient c.onto c.kernel e0
  have hcentral := reduced_bTwo_middle_central h.swap hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor (reduced_triple h.swap)
    (reduced_borel_core_sylow h.swap) (reduced_vertex_sylow h.swap) hactor hcentral
  have hz : Nat.card (Z F α)=4 := by
    have hh := c.central_center_card (LinearEquiv.refl _ _) hω
    change Nat.card (Z F α)=Nat.card k^2 at hh
    rw [hk,Nat.card_zmod] at hh
    exact hh
  refine ⟨hz,?_,(reduced_bTwo_center_identities h.swap hc hne hb hab hβu).2.1⟩
  rw [←reduced_neighborCoreIntersection_eq_second_core h.swap hab.symm]
  apply le_iInf
  intro w
  exact graph_Z_le_Q_of_short (reduced_triple h.swap) (reduced_kernel_sylow h.swap)
    (by
      change (graph F).dist α w.val<b F
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr w.property,hb]; decide)


open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ
local notation "Aₛ" => reducedAmalgam Lₛ Sₛ

private theorem source_binary_marking :
    Nonempty ((locals T M Mc H 1 ⧸ pCore 2 (locals T M Mc H 1)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨_,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3,inferInstance,inferInstance,
      GaloisField.card 2 3 (by decide),⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  exact ⟨eU⟩

/-- The original binary center plane has order four, lies in the full
second-ball core, and its whole local actor has trivial center. -/
theorem source_binary_center_profile :
    Nat.card (Z Fₛ (base Fₛ false))=4 ∧
      Z Fₛ (base Fₛ false)≤(ballKernel Fₛ (base Fₛ false) 2).pCoreIn 2 ∧
      center (graphLocalGroup Fₛ (base Fₛ false))=⊥ := by
  obtain ⟨eU⟩ := source_binary_marking hG T hempty hM hu hmany hcard e H hH eR
  exact pair_binary_center (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
    (residualQuotientEquiv H eR) eU


end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCenterProfile
