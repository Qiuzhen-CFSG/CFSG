module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCriticalGeometry
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReducedPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoStrictCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalFieldBoundSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceNoncommutingParameters

/-!
# Original core orders in the eight-field source pair

The actual L₂(8)/S₃ pair has a noncommuting critical pair of distance two,
with binary initial vertex and eight-field middle vertex. The exceptional
intersection would force the middle field to have order two or four.
The strict intersection therefore holds, and the original DGS core formulas
give orders 512 and 2048, with full Borel two-core of order 4096.

In the original Chapter 14 pair the full Borel two-core is precisely T.
No marked triality amalgam, completion or catalogue comparison is assumed.
Source: DGS (10.7)--(10.10), pp.158--165; Aschbacher--Smith 14.2.16,
printed pp.986--987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Reduction
open ChapterF.Source.DGS85.NoncommutingProfile
open ChapterF.Source.DGS85.NoncommutingProfile.Reduction
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}

private abbrev eightFields (i : Bool) : Type := if i then GaloisField 2 3 else ZMod 2
private instance eightFields_field (i : Bool) : Field (eightFields i) := by
  cases i <;> dsimp [eightFields] <;> infer_instance
private instance eightFields_finite (i : Bool) : Finite (eightFields i) := by
  cases i <;> dsimp [eightFields] <;> infer_instance
private instance eightFields_char (i : Bool) : CharP (eightFields i) 2 := by
  cases i <;> dsimp [eightFields] <;> infer_instance

private def eight_field_markings
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (i : Bool) :
    (family ![U,K] i ⧸ pCore 2 (family ![U,K] i)) ≃* PSL(2,eightFields i) := by
  cases i
  · exact (eU.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
      (Theory.PSL2.sl2QuotientEquiv (ZMod 2))
  · exact eK

omit [Finite G] in
/-- The literal mixed eight/binary pair has the full original core orders.
Its original common subgroup is not silently identified with the Borel core. -/
theorem eight_pair_core_orders
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card ((parabolic ![K,U] S 0).pCoreIn 2) = 512 ∧
      Nat.card ((parabolic ![K,U] S 1).pCoreIn 2) = 2048 ∧
      Nat.card ((commonBorel ![K,U] S).pCoreIn 2) = 4096 := by
  let F := reducedFamily ![U,K] S
  let α := base F false
  let β := base F true
  let ι := (G₀ ![U,K] S).subtype
  have hb : b F = 2 := (pair_b_swap K U S).trans
    (SourceCriticalGeometry.critical_distance_two h eK eU)
  obtain ⟨u,hc,hne,hβu⟩ := SourceCriticalGeometry.reversed_base_critical h eK eU
  have hval : 3 ≤ Nat.card ((graph F).neighborSet α) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h.swap) (reduced_vertex_sylow h.swap) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet α) (by rw [←Nat.card_coe_set_eq]; omega) β
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hD : (parabolic ![U,K] S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι := by
    intro hD
    obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
      reduced_bTwo_center_action_exists h.swap hc hne hb hab hβu
    have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
    subst alg
    let : Algebra (ZMod 2) k := ZMod.algebra k 2
    let e0 := (reduced_graphLinearQuotient h.swap false (eight_field_markings eK eU false)).trans
      (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (ZMod 2)).symm
    have hk := MixedDGS.source_action_field_card h.swap hactor c.quotient c.onto c.kernel e0
    have hcentral := reduced_bTwo_middle_central h.swap hc hne hb hab hβu
    have hcomm := (reduced_bTwo_center_identities h.swap hc hne hb hab hβu).2.2.2
    have hparam := (original_bTwo_exceptional_beta_parameters h.swap hb c hactor hcentral
      ht htne hcomm (reduced_graph_core_obstruction h.swap α β hab)
      (eight_field_markings eK eU true) hD (LinearEquiv.refl _ _)).2
    rw [hk] at hparam
    norm_num [eightFields, GaloisField.card 2 3 (by decide), Nat.card_zmod] at hparam
  obtain ⟨_,_,_,_,_,_,hzero,hone,_,hB,_⟩ :=
    original_bTwo_strict_core_orders h.swap hc hne hb hβu ht htne
      eightFields (eight_field_markings eK eU) hD
  have hP0 : parabolic ![U,K] S 0 = parabolic ![K,U] S 1 := rfl
  have hP1 : parabolic ![U,K] S 1 = parabolic ![K,U] S 0 := rfl
  have hCB : commonBorel ![U,K] S = commonBorel ![K,U] S := by
    change borel U S ⊔ borel K S ⊔ S = borel K S ⊔ borel U S ⊔ S
    rw [sup_comm (borel U S)]
  rw [hP0] at hzero
  rw [hP1] at hone
  rw [hCB] at hB
  norm_num [eightFields, GaloisField.card 2 3 (by decide), Nat.card_zmod] at hzero hone hB
  exact ⟨hone,hzero,hB⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable
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

/-- The original normal eight-field source has Sylow order 4096 and full
parabolic core orders 512 and 2048 before any amalgam recognition. -/
theorem source_core_orders :
    Nat.card (H.pCoreIn 2) = 512 ∧
      Nat.card ((secondParabolic T M Mc H).pCoreIn 2) = 2048 ∧ Nat.card T = 4096 := by
  obtain ⟨hF,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3, inferInstance, inferInstance,
      GaloisField.card 2 3 (by decide), ⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  have hh := eight_pair_core_orders hF (residualQuotientEquiv H eR) eU
  obtain ⟨hP0,hP1,hB,_,_⟩ := source_parabolics hG T hempty hM hu hmany hcard e H hH eR
  change Nat.card ((parabolic (locals T M Mc H) (T : Subgroup G) 0).pCoreIn 2) = 512 ∧
    Nat.card ((parabolic (locals T M Mc H) (T : Subgroup G) 1).pCoreIn 2) = 2048 ∧
    Nat.card ((commonBorel (locals T M Mc H) (T : Subgroup G)).pCoreIn 2) = 4096 at hh
  rw [hP0,hP1,hB,source_borel_twoCore hG T hempty hM hu hmany hcard e H hH eR] at hh
  exact hh

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
