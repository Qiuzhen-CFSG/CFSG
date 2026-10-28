module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoStrictTreeSource

/-!
# Seven-path geometry of the original eight-field source

The original L₂(8)/S₃ quotient markings construct a binary-start critical
pair on the reversed original family. Its eight-field core has order 512.
The intrinsic exceptional criterion would give order 64, so the actual
intersection is strict. The unrestricted strict tree theorem then supplies
path parameters (6,7), seven-path transitivity and odd seven-path fixers.

The reversal only exchanges the original endpoints; all reduced groups,
Borel inclusions and universal-cover actions remain those of the source.
No critical-path, strictness or marked-amalgam comparison input is assumed.
Source: DGS, Groups and Graphs (1985), (10.7)--(10.10), pp.158--165.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Reduction
open ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.DGS85.NoncommutingProfile
open ChapterF.Source.DGS85.NoncommutingProfile.Reduction
variable {G : Type*} [Group G] {K U S : Subgroup G}

private abbrev pathFields (i : Bool) : Type := if i then GaloisField 2 3 else ZMod 2
private instance pathFields_field (i : Bool) : Field (pathFields i) := by
  cases i <;> dsimp [pathFields] <;> infer_instance
private instance pathFields_finite (i : Bool) : Finite (pathFields i) := by
  cases i <;> dsimp [pathFields] <;> infer_instance
private instance pathFields_char (i : Bool) : CharP (pathFields i) 2 := by
  cases i <;> dsimp [pathFields] <;> infer_instance

private def path_field_markings
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (i : Bool) :
    (family ![U,K] i ⧸ pCore 2 (family ![U,K] i)) ≃* PSL(2,pathFields i) := by
  cases i
  · exact (eU.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
      (Theory.PSL2.sl2QuotientEquiv (ZMod 2))
  · exact eK

/-- The literal eight-field/binary pair has the strict seven-path profile
on its original universal cover, with the binary endpoint placed first. -/
theorem eight_pair_path_profile
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    HasSourcePathParameters (P := fun i => (P₀ ![U,K] S i).subgroupOf (G₀ ![U,K] S)) 6 7 ∧
    BasedPathTransitive (X := (reducedAmalgam ![U,K] S).Universal)
      (sourceGraph (reducedAmalgam ![U,K] S)) 7 ∧
    ∀ {a d} (p : (sourceGraph (reducedAmalgam ![U,K] S)).Walk a d),
      p.IsPath → p.length = 7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam ![U,K] S).Universal) p)) := by
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
  have hD : (parabolic ![U,K] S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι := by
    intro he
    obtain ⟨k,f,fin,ch,alg,c,hactor,_,_,_,_,_,_,_,hiff,_⟩ :=
      original_bTwo_intrinsic_core_orders h.swap hc hne hb hβu ht htne eK
    have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
    subst alg
    let : Algebra (ZMod 2) k := ZMod.algebra k 2
    let e0 := (reduced_graphLinearQuotient h.swap false (path_field_markings eK eU false)).trans
      (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (ZMod 2)).symm
    have hk := MixedDGS.source_action_field_card h.swap hactor c.quotient c.onto c.kernel e0
    have hcard := hiff.mp he
    have h512 := (eight_pair_core_orders h eK eU).1
    change Nat.card ((parabolic ![K,U] S 0).pCoreIn 2) = _ at hcard
    rw [h512,hk] at hcard
    norm_num [GaloisField.card 2 3 (by decide),Nat.card_zmod] at hcard
  exact original_bTwo_strict_tree_source_profile h.swap hc hne hb hβu ht htne
    pathFields (path_field_markings eK eU) hD

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

set_option maxHeartbeats 800000 in
/-- The same original Chapter 14 source has seven-path transitivity and
odd seven-path fixers, with its two original endpoints exchanged. -/
theorem source_path_profile :
    let L := ![locals T M Mc H 1,locals T M Mc H 0]
    HasSourcePathParameters (P := fun i => (P₀ L (T : Subgroup G) i).subgroupOf
      (G₀ L (T : Subgroup G))) 6 7 ∧
    BasedPathTransitive (X := (reducedAmalgam L (T : Subgroup G)).Universal)
      (sourceGraph (reducedAmalgam L (T : Subgroup G))) 7 ∧
    ∀ {a d} (p : (sourceGraph (reducedAmalgam L (T : Subgroup G))).Walk a d),
      p.IsPath → p.length = 7 → Odd (Nat.card
        (pathFixer (X := (reducedAmalgam L (T : Subgroup G)).Universal) p)) := by
  obtain ⟨hF,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3, inferInstance, inferInstance,
      GaloisField.card 2 3 (by decide), ⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  exact eight_pair_path_profile (K := locals T M Mc H 0) (U := locals T M Mc H 1)
    hF (residualQuotientEquiv H eR) eU

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
