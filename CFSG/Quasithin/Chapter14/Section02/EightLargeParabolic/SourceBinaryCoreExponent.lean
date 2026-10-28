module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCriticalGeometry
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReducedPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoAlphaExponent

/-!
# Fourth powers in the original binary core

The literal eight/binary source supplies its original critical pair and
linear quotient. The actual binary core has elementary D_alpha and
canonical elementary quotient, so every fourth power is one. This is
transported through the original reduced inclusion and conjugation to all
binary vertices, with the whole endpoint core retained throughout.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCoreExponent
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open ChapterF.Source.DGS85.Reduction
open ChapterF.Source.DGS85.NoncommutingProfile
open ChapterF.Source.DGS85.NoncommutingProfile.Reduction
variable {G : Type*} [Group G] {K U S : Subgroup G}

/-- Fourth powers on the whole endpoint core and all original binary graph cores. -/
@[expose] def HasBinaryCoreFourth (P : Subgroup G) (L : Fin 2 → Subgroup G) (S : Subgroup G) : Prop :=
  (∀ x∈P.pCoreIn 2, x^4=1) ∧
    (∀ v : Vertex (reducedFamily L S), v.type=false →
      ∀ x∈Q (reducedFamily L S) v, x^4=1)

/-- The actual pair gives fourth powers on the whole binary parabolic core
and on every binary vertex core of its unchanged reduced family. -/
theorem eight_pair_binary_core_fourth
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    HasBinaryCoreFourth (parabolic ![K,U] S 1) ![U,K] S := by
  let F := reducedFamily ![U,K] S
  let α := base F false
  let β := base F true
  have hb : b F=2 := (pair_b_swap K U S).trans
    (SourceCriticalGeometry.critical_distance_two h eK eU)
  obtain ⟨u,hc,hne,hβu⟩ := SourceCriticalGeometry.reversed_base_critical h eK eU
  have hval : 3≤Nat.card ((graph F).neighborSet α) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h.swap) (reduced_vertex_sylow h.swap) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet α)
    (by rw [←Nat.card_coe_set_eq]; omega) β
  have hfour := original_bTwo_linear_alpha_fourth_power h.swap hc hne hb hβu ht htne eK
  refine ⟨hfour,?_⟩
  have hbase (x : G₀ ![U,K] S) (hx : x∈Q F α) : x^4=1 := by
    apply (G₀ ![U,K] S).subtype_injective
    rw [map_pow,map_one]
    apply hfour
    have hmap : (Q F α).map (G₀ ![U,K] S).subtype = (parabolic ![U,K] S 0).pCoreIn 2 :=
      reduced_base_Q_map h.swap false
    exact hmap ▸ mem_map_of_mem _ hx
  intro v hv x hx
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  change g • base F v.type=v at hg
  rw [hv] at hg
  rw [←hg,Q_translate] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  rw [←map_pow,hbase y hy,map_one]

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
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



set_option maxHeartbeats 800000 in
/-- The whole original second core and every corresponding binary graph
core have exponent dividing four, without a selected module or path premise. -/
theorem source_binary_core_fourth :
    HasBinaryCoreFourth (secondParabolic T M Mc H) Lₛ (T : Subgroup G) := by
  obtain ⟨hF,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3,inferInstance,inferInstance,
      GaloisField.card 2 3 (by decide),⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  have hh := eight_pair_binary_core_fourth hF (residualQuotientEquiv H eR) eU
  have hP := (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.1
  exact (congrArg (fun P => HasBinaryCoreFourth P Lₛ (T : Subgroup G)) hP).mp hh

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCoreExponent
