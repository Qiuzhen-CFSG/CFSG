/-
Authors: OpenAI
-/

module

public import FeitThompson.BGsection10.corollary_10_7_c
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 10.7(d). -/
public theorem corollary_10_7_d
    {p : Nat.Primes} (P : Sylow p.val G) {Q : Subgroup G}
    (hQle : Q ≤ (P : Subgroup G)) :
    ∃ S : Sylow p.val (Subgroup.normalizer (Q : Set G)),
      section10AmbientSylowSubgroup (Subgroup.normalizer (Q : Set G)) S =
        subgroupNormalizerIn (P : Subgroup G) (Q : Set G) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let NQ : Subgroup G := Subgroup.normalizer (Q : Set G)
  let NPQ : Subgroup G := subgroupNormalizerIn (P : Subgroup G) (Q : Set G)
  have hQp : IsPGroup p.val Q :=
    IsPGroup.to_le (H := Q) (K := (P : Subgroup G)) P.isPGroup' hQle
  have hQ_le_NQ : Q ≤ NQ := by
    intro q hq
    exact Subgroup.le_normalizer hq
  let QN : Subgroup NQ := Q.subgroupOf NQ
  have hQNp : IsPGroup p.val QN :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Q) (K := NQ) hQ_le_NQ).symm
  haveI : QN.Normal := by
    simpa [QN, NQ] using (Subgroup.normal_in_normalizer (H := Q))
  let S₀ : Sylow p.val NQ := default
  let SG : Subgroup G := section10AmbientSylowSubgroup NQ S₀
  have hQN_le_S₀ : QN ≤ (S₀ : Subgroup NQ) :=
    section10_normal_pSubgroup_le_sylow hQNp S₀
  have hQ_le_SG : Q ≤ SG := by
    intro q hq
    have hqQN : (⟨q, hQ_le_NQ hq⟩ : NQ) ∈ QN := by
      simpa [QN, Subgroup.mem_subgroupOf] using hq
    have hqS₀ : (⟨q, hQ_le_NQ hq⟩ : NQ) ∈ (S₀ : Subgroup NQ) :=
      hQN_le_S₀ hqQN
    change q ∈ (S₀ : Subgroup NQ).map NQ.subtype
    exact Subgroup.mem_map_of_mem NQ.subtype hqS₀
  have hSGp : IsPGroup p.val SG :=
    IsPGroup.map (p := p.val) (H := (S₀ : Subgroup NQ)) S₀.isPGroup' NQ.subtype
  obtain ⟨T, hSG_le_T⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hSGp
  obtain ⟨x, hxT⟩ := MulAction.exists_smul_eq G T P
  have hTconjP : (T : Subgroup G).conjBy x = (P : Subgroup G) := by
    have hxT' := congrArg (fun S : Sylow p.val G => (S : Subgroup G)) hxT
    have hTconj_smul :
        (T : Subgroup G).conjBy x = ((x • T : Sylow p.val G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      ext y
      constructor <;> rintro ⟨z, hz, rfl⟩ <;> exact ⟨z, hz, rfl⟩
    exact hTconj_smul.trans hxT'
  have hSGxP : SG.conjBy x ≤ (P : Subgroup G) := by
    exact (section10_conjBy_mono hSG_le_T x).trans (le_of_eq hTconjP)
  have hQxP : Q.conjBy x ≤ (P : Subgroup G) :=
    (section10_conjBy_mono hQ_le_SG x).trans hSGxP
  rcases corollary_10_7_c (G := G) P hQle hQxP with ⟨y, hQx_eq_Qy⟩
  let a : G := (y : G)⁻¹ * x
  have haNQ : a ∈ NQ := by
    apply section10_mem_normalizer_of_conjBy_eq
    calc
      Q.conjBy a = (Q.conjBy x).conjBy ((y : G)⁻¹) := by
        simpa [a] using section10_conjBy_mul Q ((y : G)⁻¹) x
      _ = (Q.conjBy (y : G)).conjBy ((y : G)⁻¹) := by rw [hQx_eq_Qy]
      _ = Q := section10_conjBy_inv Q (y : G)
  let aNQ : NQ := ⟨a, haNQ⟩
  let S : Sylow p.val NQ := aNQ • S₀
  let SG' : Subgroup G := section10AmbientSylowSubgroup NQ S
  have hSGaP : SG.conjBy a ≤ (P : Subgroup G) := by
    calc
      SG.conjBy a = (SG.conjBy x).conjBy ((y : G)⁻¹) := by
        simpa [a] using section10_conjBy_mul SG ((y : G)⁻¹) x
      _ ≤ ((P : Subgroup G).conjBy ((y : G)⁻¹)) :=
        section10_conjBy_mono hSGxP ((y : G)⁻¹)
      _ = (P : Subgroup G) := by
        exact section10_conjBy_eq_of_mem_normalizer
          ((Subgroup.normalizer (((P : Subgroup G) : Set G))).inv_mem y.property)
  have hSG'_eq : SG' = SG.conjBy a := by
    simpa [SG', SG, S, aNQ] using
      section10AmbientSylowSubgroup_smul (M := NQ) S₀ aNQ
  have hSG'_le_P : SG' ≤ (P : Subgroup G) := by
    simpa [hSG'_eq] using hSGaP
  have hSG'_le_NQ : SG' ≤ NQ := by
    intro z hz
    change z ∈ (S : Subgroup NQ).map NQ.subtype at hz
    rcases Subgroup.mem_map.mp hz with ⟨w, _hw, rfl⟩
    exact w.property
  have hSG'_le_NPQ : SG' ≤ NPQ := by
    intro z hz
    exact section10_mem_subgroupNormalizerIn.mpr ⟨hSG'_le_NQ hz, hSG'_le_P hz⟩
  have hNPQ_le_NQ : NPQ ≤ NQ :=
    section10_subgroupNormalizerIn_le_normalizer (P : Subgroup G) (Q : Set G)
  have hNPQ_le_P : NPQ ≤ (P : Subgroup G) :=
    section10_subgroupNormalizerIn_le (P : Subgroup G) (Q : Set G)
  let NPQsub : Subgroup NQ := NPQ.subgroupOf NQ
  have hNPQp : IsPGroup p.val NPQ :=
    IsPGroup.to_le (H := NPQ) (K := (P : Subgroup G)) P.isPGroup' hNPQ_le_P
  have hNPQsub_p : IsPGroup p.val NPQsub :=
    hNPQp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := NPQ) (K := NQ) hNPQ_le_NQ).symm
  have hS_le_NPQsub : (S : Subgroup NQ) ≤ NPQsub := by
    intro z hz
    change ((z : NQ) : G) ∈ NPQ
    exact hSG'_le_NPQ (Subgroup.mem_map_of_mem NQ.subtype hz)
  have hNPQsub_eq : NPQsub = (S : Subgroup NQ) :=
    S.is_maximal' hNPQsub_p hS_le_NPQsub
  refine ⟨S, ?_⟩
  calc
    section10AmbientSylowSubgroup NQ S = (S : Subgroup NQ).map NQ.subtype := by
      rfl
    _ = NPQsub.map NQ.subtype := by rw [← hNPQsub_eq]
    _ = NPQ := by
      simpa [NPQsub] using
        (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := NPQ) (K := NQ) hNPQ_le_NQ)
