module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCoreExponent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SecondKernel
public import Theory.ElementaryAbelian.Injective

/-!
# The original binary radius-two core is elementary

The original critical geometry constructs two distinct neighbors of the
binary base. The intersection of their whole cores is elementary. The
actual radius-two kernel's two-core is the intersection of all neighboring
cores, so it embeds into that elementary intersection. Conjugation transports
the conclusion to every binary vertex, without selected-path data.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinarySecondCore
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open ChapterF.Source.DGS85.Reduction
open ChapterF.Source.DGS85.NoncommutingProfile
open ChapterF.Source.DGS85.NoncommutingProfile.Reduction CommutingOneProfile
variable {G : Type*} [Group G] {K U S : Subgroup G}

/-- Every binary second-ball two-core of the literal eight/binary source
is elementary, with the complete kernel retained. -/
theorem eight_pair_binary_second_core
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    ∀ v : Vertex (reducedFamily ![U,K] S), v.type=false →
      IsElementaryAbelian 2 ((ballKernel (reducedFamily ![U,K] S) v 2).pCoreIn 2) := by
  let F := reducedFamily ![U,K] S
  let α := base F false
  let β := base F true
  let ι := (G₀ ![U,K] S).subtype
  have hb : b F=2 := (pair_b_swap K U S).trans
    (SourceCriticalGeometry.critical_distance_two h eK eU)
  obtain ⟨u,hc,hne,hβu⟩ := SourceCriticalGeometry.reversed_base_critical h eK eU
  have hval : 3≤Nat.card ((graph F).neighborSet α) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h.swap) (reduced_vertex_sylow h.swap) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet α)
    (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨k,f,fin,ch,alg,c,hactor,_,_,hD,_⟩ :=
    original_bTwo_intrinsic_core_orders h.swap hc hne hb hβu ht htne eK
  have hmap : (Q F β ⊓ Q F t).map ι=
      (parabolic ![U,K] S 1).pCoreIn 2 ⊓ (Q F t).map ι := by
    rw [map_inf _ _ _ (G₀ ![U,K] S).subtype_injective,reduced_base_Q_map h.swap true]
    rfl
  let _ : IsElementaryAbelian 2 ((Q F β ⊓ Q F t).map ι) := hmap.symm ▸ hD
  let eD := (Q F β ⊓ Q F t).equivMapOfInjective ι (G₀ ![U,K] S).subtype_injective
  let _ : IsElementaryAbelian 2 (Q F β ⊓ Q F t : Subgroup (G₀ ![U,K] S)) :=
    IsElementaryAbelian.of_injective eD.toMonoidHom eD.injective
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hI : (ballKernel F α 2).pCoreIn 2≤Q F β ⊓ Q F t := by
    rw [←reduced_neighborCoreIntersection_eq_second_core h.swap hab.symm]
    exact le_inf (neighborCoreIntersection_le F hab.symm) (neighborCoreIntersection_le F ht.symm)
  let _ : IsElementaryAbelian 2 ((ballKernel F α 2).pCoreIn 2) :=
    IsElementaryAbelian.of_injective (inclusion hI) (inclusion_injective _)
  intro v hv
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  change g • base F v.type=v at hg
  rw [hv] at hg
  rw [←hg,ballKernel_translate,AmalgamLocalCores.pCoreIn_map_of_injective
    2 _ (MulAut.conj g).injective]
  exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom

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
/-- The original source makes every binary radius-two two-core elementary,
without a selected critical pair, path or core hypothesis. -/
theorem source_binary_second_core :
    ∀ v : Vertex (reducedFamily Lₛ (T : Subgroup G)), v.type=false →
      IsElementaryAbelian 2 ((ballKernel (reducedFamily Lₛ (T : Subgroup G)) v 2).pCoreIn 2) := by
  obtain ⟨hF,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3,inferInstance,inferInstance,
      GaloisField.card 2 3 (by decide),⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  exact eight_pair_binary_second_core hF (residualQuotientEquiv H eR) eU

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinarySecondCore
