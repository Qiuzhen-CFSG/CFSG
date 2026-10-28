module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.CrossBranch.Overgroup.Local
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.SylowActor.LocalGeometry
public import Mathlib.GroupTheory.IndexNormal

/-!
# The order-64 overgroup in Held's cross branch

If pi is fused to tau*lambda*xi, a Sylow subgroup of its centralizer
containing L2 is an ambient Sylow subgroup. Sylow conjugacy and the complete
elementary-sixteen catalogue give an order-64 subgroup of that centralizer
which contains and normalizes L2.

Under pi--mu nonfusion, N_G(L2) cannot be a two-group: its local order-64
subgroup C_H(mu) would have index at most two and hence be normal. Its center
is <pi,mu>, and nonfusion makes pi characteristic under ambient conjugation.
Thus N_G(L2) would lie in C_G(pi), forcing the order-64 overgroup into the
local cross centralizer L2 of order sixteen.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.9, printed p.230.
-/

open Subgroup Equiv

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

omit [Finite G] in
public theorem cross_muIntersection_normalizes (k : Fin 4) :
    muIntersection D e ≤ normalizer (ambientElementary D e k : Set G) := by
  rw [muIntersection, ← ambient_centralizer_mu_map]
  exact (map_mono (cross_model_mu_normalizes k)).trans (le_normalizer_map _)

omit [Finite G] in
public theorem cross_intersection_eq :
    D.centralizer ⊓ centralizer ({D.a10ModelEmbedding e (tau * lam * xi)} : Set G) =
      ambientElementary D e 3 := by
  let f := D.a10ModelEmbedding e
  have hm : (centralizer ({tau * lam * xi} : Set H)).map f =
      D.centralizer ⊓ centralizer ({f (tau * lam * xi)} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(e.symm y).property, mem_centralizer_singleton_iff.mpr ?_⟩
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hy)
    · rintro ⟨hx, hc⟩
      have hxr : x ∈ f.range := by rwa [D.a10ModelEmbedding_range e]
      obtain ⟨y, rfl⟩ := hxr
      refine ⟨y, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      apply D.a10ModelEmbedding_injective e
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc
  rw [cross_model_centralizer_eq] at hm
  exact hm.symm

public theorem exists_cross_overgroup
    (hcross : IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi))) :
    ∃ P : Subgroup G, Nat.card P = 64 ∧
      ambientElementary D e 3 ≤ P ∧
      P ≤ centralizer ({D.a10ModelEmbedding e (tau * lam * xi)} : Set G) ∧
      P ≤ normalizer (ambientElementary D e 3 : Set G) := by
  let A := ambientElementary D e 3
  let C := centralizer ({D.a10ModelEmbedding e (tau * lam * xi)} : Set G)
  have hAC : A ≤ C := by
    change ambientElementary D e 3 ≤ C
    rw [← cross_intersection_eq]
    exact inf_le_right
  have hA : IsPGroup 2 (A.subgroupOf C) := IsPGroup.of_card (n := 4) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, ambientElementary_card]
    norm_num)
  obtain ⟨T, hAT⟩ := hA.exists_le_sylow
  let R := (T : Subgroup C).map C.subtype
  have hAR : A ≤ R := by
    rw [← map_subgroupOf_eq_of_le hAC]
    exact map_mono hAT
  have hRc : Nat.card R = 128 := by
    rw [card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity,
      centralizer_card_of_isConj D hcross]
    decide +kernel
  let S : Sylow 2 G := Sylow.ofCard R (by
    rw [hRc]
    exact D.sylow_card.symm.trans D.sylow.card_eq_multiplicity)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S (ambientSylow D e)
  let f := (MulAut.conj g).toMonoidHom
  have hRS : R.map f = (ambientSylow D e : Subgroup G) := congrArg Sylow.toSubgroup hg
  have hAS : A.map f ≤ ambientSylow D e := (map_mono hAR).trans_eq hRS
  have heA : IsElementaryAbelian 2 (A.map f) := by
    let := ambientElementary_isElementaryAbelian D e 3
    exact IsElementaryAbelian.map f
  have hcA : Nat.card (A.map f) = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective, ambientElementary_card]
  obtain ⟨k, hk⟩ := ambient_elementary_sixteen D e (A.map f) hAS heA hcA
  let P := (muIntersection D e).comap f
  have hPN : P ≤ normalizer (A : Set G) := by
    have h := comap_mono (f := f) (cross_muIntersection_normalizes D e k)
    rw [← hk, comap_normalizer_eq_of_surjective _ (MulAut.conj g).surjective,
      comap_map_eq_self_of_injective (MulAut.conj g).injective] at h
    exact h
  refine ⟨P, ?_, ?_, ?_, hPN⟩
  · change Nat.card ((muIntersection D e).comap (MulAut.conj g).toMonoidHom) = 64
    rw [comap_equiv_eq_map_symm', card_map_of_injective (MulAut.conj g).symm.injective,
      muIntersection_card]
  · have hAk : ambientElementary D e k ≤ muIntersection D e := by
      rw [muIntersection]
      apply le_inf
      · rw [← D.a10ModelEmbedding_range e]
        exact map_le_range _ _
      · exact ambientElementary_le_centralizer_mu D e k
    exact (map_le_iff_le_comap).mp (hk ▸ hAk)
  · have hPR : P ≤ R := by
      have h := comap_mono (f := f) (muIntersection_le_sylow D e)
      rw [← hRS, comap_map_eq_self_of_injective (MulAut.conj g).injective] at h
      exact h
    exact hPR.trans (map_subtype_le _)

/-- Nonfusion singles out pi in the center of the common order-64 subgroup. -/
public theorem cross_muIntersection_normalizer_le_centralizer
    (hmu : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    normalizer (muIntersection D e : Set G) ≤ D.centralizer := by
  intro g hg
  have hzV : D.z ∈ muPlane D e :=
    (muPlane_mem D e _).mpr (Or.inr (Or.inl rfl))
  have hcV := (mem_normalizer_iff.mp (muPlane_normalizer D e hg) D.z).mp hzV
  have hc : IsConj D.z (g * D.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hprod : IsConj (D.a10NoncentralInvolution e) (D.z * D.a10NoncentralInvolution e) := by
    have hm : IsConj mu (pi * mu) := isConj_iff.mpr ⟨taup, by decide +kernel⟩
    simpa only [map_mul, D.a10ModelEmbedding_central e,
      LocalData.a10NoncentralInvolution, Coordinates.mu] using
      (D.a10ModelEmbedding e).map_isConj hm
  rcases (muPlane_mem D e _).mp hcV with h | h | h | h
  · rw [h] at hc
    exact (D.z_ne_one (isConj_one_left.mp hc)).elim
  · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)
  · exact (hmu (h ▸ hc)).elim
  · exact (hmu ((h ▸ hc).trans hprod.symm)).elim

/-- Under pi--mu nonfusion, a two-group L2 normalizer would lie in C_G(pi). -/
public theorem cross_two_normalizer_le_centralizer
    (hmu : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (htwo : IsPGroup 2 (normalizer (ambientElementary D e 3 : Set G))) :
    normalizer (ambientElementary D e 3 : Set G) ≤ D.centralizer := by
  let N := normalizer (ambientElementary D e 3 : Set G)
  let B := muIntersection D e
  have hBN : B ≤ N := cross_muIntersection_normalizes D e 3
  obtain ⟨T, hNT⟩ := htwo.exists_le_sylow
  have hbound : Nat.card N ≤ 128 := by
    have h := card_le_of_le hNT
    have hT : Nat.card T = 128 :=
      (Nat.card_congr (T.equiv D.sylow).toEquiv).trans D.sylow_card
    rwa [hT] at h
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hind := (B.subgroupOf N).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv, muIntersection_card] at hind
  have hindex : (B.subgroupOf N).index = 1 ∨ (B.subgroupOf N).index = 2 := by omega
  have hnormal : (B.subgroupOf N).Normal := by
    rcases hindex with h | h
    · exact normal_of_index_eq_one h
    · exact normal_of_index_eq_two h
  exact ((normal_subgroupOf_iff_le_normalizer hBN).mp hnormal).trans
    (cross_muIntersection_normalizer_le_centralizer D e hmu)

/-- Held 2.9: cross fusion forces a non-two normalizer of the actual L2. -/
public theorem cross_normalizer_not_isPGroup
    (hmu : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcross : IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi))) :
    ¬ IsPGroup 2 (normalizer (ambientElementary D e 3 : Set G)) := by
  obtain ⟨P, hPc, _, hPC, hPN⟩ := exists_cross_overgroup D e hcross
  intro htwo
  have hPH := hPN.trans (cross_two_normalizer_le_centralizer D e hmu htwo)
  have hPA : P ≤ ambientElementary D e 3 := by
    rw [← cross_intersection_eq]
    exact le_inf hPH hPC
  have hc := card_le_of_le hPA
  rw [hPc, ambientElementary_card] at hc
  omega

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
