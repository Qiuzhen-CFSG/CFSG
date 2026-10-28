module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.ThreeElement.Core

/-!
# Overgroups of Held's lambda core

Fusion of lambda with pi gives an order-64 subgroup of its ambient
centralizer containing W. Both this subgroup and the displayed xi normalize
W. The corresponding pi-lambda extension is already supplied by
`exists_sCase_centralizer_overgroup` with index 1.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, printed p.226.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
open Coordinates

public theorem xi_mem_lambdaModelCenter_normalizer :
    xi ∈ normalizer (lambdaModelCenter : Set H) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap]
    nth_rw 1 [lambdaModelCenter_eq]
    apply (closure_le _).mpr
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · change xi * pi * xi⁻¹ ∈ lambdaModelCenter
      rw [show xi * pi * xi⁻¹ = pi by decide +kernel]
      exact lambdaModelCenter_pi
    · change xi * mu * xi⁻¹ ∈ lambdaModelCenter
      rw [show xi * mu * xi⁻¹ = mu by decide +kernel]
      exact lambdaModelCenter_mu
    · change xi * lam * xi⁻¹ ∈ lambdaModelCenter
      rw [show xi * lam * xi⁻¹ = mu * lam by decide +kernel]
      exact lambdaModelCenter.mul_mem lambdaModelCenter_mu lambdaModelCenter_lam
  · rw [card_map_of_injective (MulAut.conj xi).injective]

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem xi_mem_lambdaCore_normalizer :
    D.a10ModelEmbedding e xi ∈ normalizer (lambdaCore D e : Set G) := by
  rw [← lambdaCenter_normalizer_eq]
  exact le_normalizer_map (D.a10ModelEmbedding e)
    (mem_map_of_mem (D.a10ModelEmbedding e) xi_mem_lambdaModelCenter_normalizer)

omit [Finite G] in
/-- W is the actual common centralizer of pi and lambda. -/
public theorem lambdaCore_eq_inf_centralizer_lam :
    lambdaCore D e = D.centralizer ⊓
      centralizer ({D.a10ModelEmbedding e lam} : Set G) := by
  let f := D.a10ModelEmbedding e
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [lambdaModelCore_eq_centralizer_lam] at hy
    refine ⟨(e.symm y).property, mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hy)
  · rintro ⟨hx, hc⟩
    have hxr : x ∈ f.range := by rwa [D.a10ModelEmbedding_range e]
    obtain ⟨y, rfl⟩ := hxr
    refine ⟨y, ?_, rfl⟩
    rw [lambdaModelCore_eq_centralizer_lam]
    apply mem_centralizer_singleton_iff.mpr
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc

/-- The first order-64 extension in Held's construction. -/
public theorem exists_lambda_core_overgroup
    (h : IsConj D.z (D.a10ModelEmbedding e lam)) :
    ∃ P : Subgroup G, Nat.card P = 64 ∧ lambdaCore D e ≤ P ∧
      P ≤ centralizer ({D.a10ModelEmbedding e lam} : Set G) := by
  let C := centralizer ({D.a10ModelEmbedding e lam} : Set G)
  let W := lambdaCore D e
  have hWC : W ≤ C := by
    change lambdaCore D e ≤ C
    rw [lambdaCore_eq_inf_centralizer_lam]
    exact inf_le_right
  have hW : Nat.card (W.subgroupOf C) = 2 ^ 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv, lambdaCore_card]
    norm_num
  have hd : 2 ^ 6 ∣ Nat.card C := by
    rw [centralizer_card_of_isConj D h]
    norm_num
  obtain ⟨P, hP, hWP⟩ := Sylow.exists_subgroup_card_pow_prime_le 2 hd
    (W.subgroupOf C) hW (show 5 ≤ 6 by decide)
  refine ⟨P.map C.subtype, ?_, ?_, map_subtype_le _⟩
  · rw [card_map_of_injective C.subtype_injective, hP]
    norm_num
  · change W ≤ P.map C.subtype
    rw [← map_subgroupOf_eq_of_le hWC]
    exact map_mono hWP

/-- The second order-64 extension in Held's construction. -/
public theorem exists_pi_lambda_core_overgroup
    (h : IsConj D.z (D.a10ModelEmbedding e (pi * lam))) :
    ∃ P : Subgroup G, Nat.card P = 64 ∧ lambdaCore D e ≤ P ∧
      P ≤ centralizer ({D.a10ModelEmbedding e (pi * lam)} : Set G) :=
  exists_sCase_centralizer_overgroup D e 1 h

omit [Finite G] in
/-- Normality here is relative to the order-64 extension, by index two. -/
public theorem lambda_core_overgroup_le_normalizer (P : Subgroup G)
    (hP : Nat.card P = 64) (hWP : lambdaCore D e ≤ P) :
    P ≤ normalizer (lambdaCore D e : Set G) := by
  have hi : ((lambdaCore D e).subgroupOf P).index = 2 := by
    have hh := ((lambdaCore D e).subgroupOf P).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hWP).toEquiv, lambdaCore_card, hP] at hh
    omega
  exact (normal_subgroupOf_iff_le_normalizer hWP).mp (normal_of_index_eq_two hi)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
