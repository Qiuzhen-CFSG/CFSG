module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoUnequalBetaModule
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The original eight-field extraspecial core and its irreducible section

The actual eight-field core has order 512. Its strict unequal-field chief
interval forces its center to equal the order-two derived and Frattini
subgroups. Thus the original core is extraspecial. The original full
parabolic quotient acts irreducibly on its 256-element central quotient,
with coordinates given by the actual quotient map.

Critical geometry and the strict intersection are constructed from the
literal L₂(8)/S₃ pair. No chosen action, strictness or recognition hypothesis
is retained in the producers, including the original Chapter 14 application.
Source: DGS, Groups and Graphs (1985), (10.10)(d), pp.164--165.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Reduction
open ChapterF.Source.DGS85.NoncommutingProfile
open ChapterF.Source.DGS85.NoncommutingProfile.Reduction
variable {G : Type*} [Group G] {K U S : Subgroup G}

/-- The actual parabolic core is extraspecial and its canonical central
quotient is an irreducible 256-element module for the full parabolic quotient.
The source center is retained with its equality to the intrinsic center,
so the whole dependent action need not be transported across that equality. -/
@[expose] def HasIrreducibleExtraspecialCore (P : Subgroup G) : Prop :=
  let Q := P.pCoreIn 2
  IsExtraspecial 2 Q ∧ ∃ C : Subgroup G, C = centerIn Q ∧
    ∃ hN : (C.subgroupOf Q).Normal, letI := hN
      ∃ hel : IsElementaryAbelian 2 (Q ⧸ C.subgroupOf Q), letI := hel
        ∃ ρ : Representation (ZMod 2) (P ⧸ pCore 2 P) (Additive (Q ⧸ C.subgroupOf Q)),
          ∃ d : Representation.BinaryConjugationSection P Q C
              (ρ.comp (QuotientGroup.mk' (pCore 2 P))),
            (∀ q : Q, (d.coordinates q).toAdd =
              Additive.ofMul (QuotientGroup.mk' (C.subgroupOf Q) q)) ∧
            ρ.IsIrreducible ∧ Nat.card (Q ⧸ C.subgroupOf Q) = 256

private theorem package_core_structure (P C : Subgroup G)
    (he : IsExtraspecial 2 (P.pCoreIn 2)) (hC : C = centerIn (P.pCoreIn 2))
    (n : ℕ) (hn : n = 256)
    (hs : ∃ hN : (C.subgroupOf (P.pCoreIn 2)).Normal, letI := hN
      ∃ hel : IsElementaryAbelian 2 (P.pCoreIn 2 ⧸ C.subgroupOf (P.pCoreIn 2)), letI := hel
        ∃ ρ : Representation (ZMod 2) (P ⧸ pCore 2 P)
            (Additive (P.pCoreIn 2 ⧸ C.subgroupOf (P.pCoreIn 2))),
          ∃ d : Representation.BinaryConjugationSection P (P.pCoreIn 2) C
              (ρ.comp (QuotientGroup.mk' (pCore 2 P))),
            (∀ q : P.pCoreIn 2, (d.coordinates q).toAdd =
              Additive.ofMul (QuotientGroup.mk' (C.subgroupOf (P.pCoreIn 2)) q)) ∧
            ρ.IsIrreducible ∧ Nat.card (P.pCoreIn 2 ⧸ C.subgroupOf (P.pCoreIn 2)) = n) :
    HasIrreducibleExtraspecialCore P := by
  obtain ⟨hN,hel,ρ,d,hd,hi,hcard⟩ := hs
  exact ⟨he,C,hC,hN,hel,ρ,d,hd,hi,hcard.trans hn⟩

private abbrev coreFields (i : Bool) : Type := if i then GaloisField 2 3 else ZMod 2
private instance coreFields_field (i : Bool) : Field (coreFields i) := by
  cases i <;> dsimp [coreFields] <;> infer_instance
private instance coreFields_finite (i : Bool) : Finite (coreFields i) := by
  cases i <;> dsimp [coreFields] <;> infer_instance
private instance coreFields_char (i : Bool) : CharP (coreFields i) 2 := by
  cases i <;> dsimp [coreFields] <;> infer_instance

private def core_field_markings
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (i : Bool) :
    (family ![U,K] i ⧸ pCore 2 (family ![U,K] i)) ≃* PSL(2,coreFields i) := by
  cases i
  · exact (eU.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
      (Theory.PSL2.sl2QuotientEquiv (ZMod 2))
  · exact eK

private theorem strict_core_selection
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    let F := reducedFamily ![U,K] S
    let α := base F false
    let β := base F true
    let ι := (G₀ ![U,K] S).subtype
    ∃ u t : Vertex F, IsCriticalPair F α u ∧ ⁅Z F α,Z F u⁆ ≠ ⊥ ∧
      b F = 2 ∧ (graph F).Adj β u ∧ (graph F).Adj α t ∧ t ≠ β ∧
      (parabolic ![U,K] S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι := by
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
  refine ⟨u,t,hc,hne,hb,hβu,ht,htne,?_⟩
  intro he
  obtain ⟨k,f,fin,ch,alg,c,hactor,_,_,_,_,_,_,_,hiff,_⟩ :=
    original_bTwo_intrinsic_core_orders h.swap hc hne hb hβu ht htne eK
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let e0 := (reduced_graphLinearQuotient h.swap false (core_field_markings eK eU false)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (ZMod 2)).symm
  have hk := MixedDGS.source_action_field_card h.swap hactor c.quotient c.onto c.kernel e0
  have hcard := hiff.mp he
  have h512 := (eight_pair_core_orders h eK eU).1
  change Nat.card ((parabolic ![K,U] S 0).pCoreIn 2) = _ at hcard
  rw [h512,hk] at hcard
  norm_num [GaloisField.card 2 3 (by decide),Nat.card_zmod] at hcard

set_option maxHeartbeats 800000 in
private theorem strict_core_structure
    {L : Fin 2 → Subgroup G} (h : HypothesisF11 L S)
    {u t : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2)
    (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
    (ht : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) false) t)
    (htne : t ≠ base (reducedFamily L S) true)
    (E : Bool → Type*) [∀ i, Field (E i)] [∀ i, Finite (E i)] [∀ i, CharP (E i) 2]
    (eL : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,E i))
    (h2 : Nat.card (E false) = 2) (h8 : Nat.card (E true) = 8)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓
      (Q (reducedFamily L S) t).map (G₀ L S).subtype ≠
        (Z (reducedFamily L S) (base (reducedFamily L S) false)).map (G₀ L S).subtype) :
    HasIrreducibleExtraspecialCore (parabolic L S 1) := by
  let P := parabolic L S 1
  let Q₁ := P.pCoreIn 2
  let F := reducedFamily L S
  let Z₁ := (Z F (base F true)).map (G₀ L S).subtype
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 P)) (inclusion_injective _)
  have hK : 2 < Nat.card (E true) := by
    omega
  have hfields : Nat.card (E false) ≠ Nat.card (E true) := by
    omega
  obtain ⟨_,_,_,_,hZ,_,_,_,_,_,hPhi,hder⟩ :=
    original_bTwo_strict_core_orders h hc hne hb hβu ht htne
      E eL hD
  change Nat.card Z₁ = Nat.card (E false) at hZ
  rw [h2] at hZ
  change (frattini Q₁).map Q₁.subtype = Z₁ at hPhi
  change ⁅Q₁,Q₁⁆ = Z₁ at hder
  have hPhiCard : Nat.card (frattini Q₁) = 2 := by
    rw [←card_map_of_injective Q₁.subtype_injective,hPhi]
    exact hZ
  have hZcenter : Z₁ ≤ centerIn Q₁ := by
    rw [←hPhi,centerIn_eq_map_center]
    exact map_mono (central_of_normal_card_two (frattini Q₁) hPhiCard)
  have hnon : ¬ IsMulCommutative Q₁ := by
    intro hcomm
    have hz : Z₁ = ⊥ := hder.symm.trans (commutator_self_eq_bot_iff.mpr hcomm)
    rw [hz,Subgroup.card_bot] at hZ
    omega
  have hPQ : P ≤ normalizer (Q₁ : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hcenterIn : centerIn Q₁ = Z₁ := by
    rcases original_bTwo_unequal_beta_interval h hc hne hb hβu ht htne
        E eL hK hD hfields
        (centerIn Q₁) inf_le_left hZcenter (normalizes_centerIn hPQ) with hz | hfull
    · exact hz
    · exact (hnon (commutator_self_eq_bot_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mpr
          ((show Q₁ ≤ centerIn Q₁ from hfull.ge).trans inf_le_right)))).elim
  have hcenter : center Q₁ = frattini Q₁ := by
    apply map_injective Q₁.subtype_injective
    exact (centerIn_eq_map_center Q₁).symm.trans (hcenterIn.trans hPhi.symm)
  have hextra : IsExtraspecial 2 Q₁ := by
    refine ⟨by rw [hcenter,hPhiCard],
      elementary_quotient_of_frattini_le (isPGroup_pCoreIn 2 P) _ hcenter.ge,?_⟩
    exact QuotientGroup.nontrivial_iff.mpr (fun he => hnon (center_eq_top_iff.mp he))
  have hirr := original_bTwo_unequal_beta_irreducible h hc hne hb hβu ht htne
    E eL hK hD hfields
  have hsize : Nat.card (E false)^2 * Nat.card (E true)^2 = 256 := by
    rw [h2,h8]
    norm_num
  exact package_core_structure P Z₁ hextra hcenterIn.symm _ hsize hirr


set_option maxHeartbeats 800000 in
/-- The literal eight-field/binary pair produces the extraspecial first
core and its irreducible canonical central quotient without additional data. -/
theorem eight_pair_core_structure
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    HasIrreducibleExtraspecialCore (parabolic ![K,U] S 0) := by
  obtain ⟨u,t,hc,hne,hb,hβu,ht,htne,hD⟩ := strict_core_selection h eK eU
  have hh := strict_core_structure h.swap hc hne hb hβu ht htne
    coreFields (core_field_markings eK eU)
    (by norm_num [coreFields,Nat.card_zmod])
    (by norm_num [coreFields,GaloisField.card 2 3 (by decide)]) hD
  have hP : parabolic ![U,K] S 1 = parabolic ![K,U] S 0 := rfl
  exact (congrArg HasIrreducibleExtraspecialCore hP).mp hh

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

/-- The actual original H has an extraspecial two-core and a canonical
irreducible central quotient of order 256 for the full H/O₂(H) action. -/
theorem source_core_structure : HasIrreducibleExtraspecialCore H := by
  obtain ⟨hF,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3, inferInstance, inferInstance,
      GaloisField.card 2 3 (by decide), ⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  have hh := eight_pair_core_structure hF (residualQuotientEquiv H eR) eU
  change HasIrreducibleExtraspecialCore (parabolic (locals T M Mc H) (T : Subgroup G) 0) at hh
  rw [(source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1] at hh
  exact hh

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
