module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.SylowActor.LocalGeometry
public import Theory.GroupTheory.WeakClosureOvergroups
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.Finite

/-!
# An order-three actor from the two centralizer Sylow groups

Assume pi is conjugate to mu, while lambda and the five additional local
representatives are not conjugate to pi. Choose a Sylow two-subgroup D_mu
of C_G(mu) containing Q = C_G(pi) ∩ C_G(mu), which has order 64.
Both D_mu and the displayed ambient Sylow D have order 128, so Q is normal
in each. Weak closure of M makes D_mu normalize M as well.

Their join K normalizes Z(Q) = <pi, mu> and M, and is not a two-group:
otherwise Sylow maximality would force D = D_mu, contradicting the explicit
action of tau' on mu. The action on the four elements of Z(Q) has kernel Q.
Thus |K:Q| divides 24, and Cauchy's theorem supplies an actual element of
order three in K. It acts nontrivially on Z(Q); choosing its orientation
gives pi^v = mu and mu^v = pi*mu.

These are conditional consequences of the three stated fusion assumptions.
No simplicity hypothesis, later pi--mu separation, full mu-centralizer
identification or recognition theorem is used.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, first paragraph, p.228.
The source convention x^v is v^-1*x*v.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

omit [Finite G] in
private theorem index_two_normalizes (Q R : Subgroup G) (hQR : Q ≤ R)
    (hQ : Nat.card Q = 64) (hR : Nat.card R = 128) : R ≤ normalizer (Q : Set G) := by
  have hi : (Q.subgroupOf R).index = 2 := by
    have hc := (Q.subgroupOf R).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv, hQ, hR] at hc
    omega
  exact (normal_subgroupOf_iff_le_normalizer hQR).mp (normal_of_index_eq_two hi)

/-- Choose a Sylow subgroup of C_G(mu) containing the actual order-64 intersection.
Its ambient image normalizes both the intersection and M. -/
public theorem exists_mu_sylow
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) :
    ∃ S : Sylow 2 (centralizer ({D.a10NoncentralInvolution e} : Set G)),
      let R := (S : Subgroup _).map (centralizer ({D.a10NoncentralInvolution e} : Set G)).subtype
      muIntersection D e ≤ R ∧ Nat.card R = 128 ∧
      R ≤ normalizer (muIntersection D e : Set G) ∧
      R ≤ normalizer (ambientElementary D e 0 : Set G) := by
  let C := centralizer ({D.a10NoncentralInvolution e} : Set G)
  let Q := muIntersection D e
  have hQC : Q ≤ C := inf_le_right
  have hQtwo : IsPGroup 2 (Q.subgroupOf C) := by
    apply IsPGroup.of_card (n := 6)
    rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, muIntersection_card]
    norm_num
  obtain ⟨S, hS⟩ := hQtwo.exists_le_sylow
  let R := (S : Subgroup C).map C.subtype
  have hQR : Q ≤ R := by
    have h := map_mono (f := C.subtype) hS
    rwa [map_subgroupOf_eq_of_le hQC] at h
  have hRcard : Nat.card R = 128 := by
    rw [card_map_of_injective C.subtype_injective, S.card_eq_multiplicity,
      centralizer_card_of_isConj D hmu]
    decide +kernel
  have hMR : ambientElementary D e 0 ≤ R := by
    apply le_trans ?_ hQR
    exact le_inf (by
      change (elementary 0).map (D.a10ModelEmbedding e) ≤ D.centralizer
      rw [← D.a10ModelEmbedding_range e]
      exact map_le_range _ _) (ambientElementary_le_centralizer_mu D e 0)
  refine ⟨S, hQR, hRcard, index_two_normalizes _ _ hQR (muIntersection_card D e) hRcard, ?_⟩
  exact le_normalizer_of_isPGroup_of_weakly_closed (ambientSylow D e) _ R
    (ambientM_weakly_closed D e hmu hlam hno) (S.isPGroup'.map C.subtype) hMR

private theorem sylow_not_le_centralizer_mu :
    ¬ (ambientSylow D e : Subgroup G) ≤ centralizer ({D.a10NoncentralInvolution e} : Set G) := by
  intro h
  have ht : taup ∈ modelD := subset_closure ⟨(4 : Fin 7), rfl⟩
  have htc := h (mem_map_of_mem (D.a10ModelEmbedding e) ht)
  have hc := mem_centralizer_singleton_iff.mp htc
  change D.a10ModelEmbedding e taup * D.a10ModelEmbedding e mu =
    D.a10ModelEmbedding e mu * D.a10ModelEmbedding e taup at hc
  have he : taup * mu = mu * taup := D.a10ModelEmbedding_injective e (by
    simpa only [map_mul] using hc)
  have hn : taup * mu ≠ mu * taup := by decide +kernel
  exact hn he

private theorem exists_mu_join
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) :
    ∃ K : Subgroup G, muIntersection D e ≤ K ∧
      K ≤ normalizer (muPlane D e : Set G) ∧
      K ≤ normalizer (ambientElementary D e 0 : Set G) ∧ ¬ IsPGroup 2 K := by
  obtain ⟨S, hQR, hRcard, hRQ, hRM⟩ := exists_mu_sylow D e hmu hlam hno
  let C := centralizer ({D.a10NoncentralInvolution e} : Set G)
  let R := (S : Subgroup C).map C.subtype
  let T : Subgroup G := ambientSylow D e
  let K := T ⊔ R
  have hTcard : Nat.card T = 128 := ambientD_card D e
  have hTQ : T ≤ normalizer (muIntersection D e : Set G) :=
    index_two_normalizes _ _ (muIntersection_le_sylow D e) (muIntersection_card D e) hTcard
  have hKQ : K ≤ normalizer (muIntersection D e : Set G) := sup_le hTQ hRQ
  refine ⟨K, (muIntersection_le_sylow D e).trans le_sup_left,
    hKQ.trans (muPlane_normalizer D e), ?_, ?_⟩
  · apply sup_le ?_ hRM
    apply le_trans ?_ (centralizer_le_normalizer_M D e)
    change modelD.map (D.a10ModelEmbedding e) ≤ D.centralizer
    rw [← D.a10ModelEmbedding_range e]
    exact map_le_range _ _
  · intro hK
    have hKT : K = T := (ambientSylow D e).is_maximal' hK le_sup_left
    have hRT : R ≤ T := hKT ▸ (le_sup_right : R ≤ K)
    have hRT' : R = T := eq_of_le_of_card_ge hRT (by rw [hRcard, hTcard])
    have hRC : R ≤ C := map_subtype_le _
    apply sylow_not_le_centralizer_mu D e
    change T ≤ C
    rw [← hRT']
    exact hRC

private theorem divisor_twentyfour (n : ℕ) (hn : n ∣ 24) (h3 : ¬ 3 ∣ 64 * n) : n ∣ 8 := by
  have hle : n ≤ 24 := Nat.le_of_dvd (by decide) hn
  interval_cases n <;> norm_num at *

private noncomputable def planeAction (K : Subgroup G)
    (hKV : K ≤ normalizer (muPlane D e : Set G)) : K →* Perm (muPlane D e) :=
  (MulAut.toPerm (muPlane D e)).comp
    ((muPlane D e).normalizerMonoidHom.comp (inclusion hKV))

private theorem planeAction_ker (K : Subgroup G)
    (hKV : K ≤ normalizer (muPlane D e : Set G)) :
    (planeAction D e K hKV).ker = (muIntersection D e).subgroupOf K := by
  ext g
  change planeAction D e K hKV g = 1 ↔ (g : G) ∈ muIntersection D e
  rw [← muPlane_centralizer]
  constructor
  · intro hg x hx
    have he := congrArg (fun σ : Perm (muPlane D e) => (σ ⟨x, hx⟩ : G)) hg
    change (g : G) * x * (g : G)⁻¹ = x at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  · intro hg
    ext x
    change (g : G) * (x : G) * (g : G)⁻¹ = (x : G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hg _ x.property).symm

private theorem exists_three_in_mu_join (K : Subgroup G) (hQK : muIntersection D e ≤ K)
    (hKV : K ≤ normalizer (muPlane D e : Set G)) (hK : ¬ IsPGroup 2 K) :
    ∃ v : K, orderOf v = 3 := by
  let a := planeAction D e K hKV
  have hker := planeAction_ker D e K hKV
  have hcard : Nat.card a.ker = 64 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv, muIntersection_card]
  have hindex : a.ker.index ∣ 24 := by
    rw [index_ker]
    have h := card_subgroup_dvd_card a.range
    rwa [Nat.card_perm, muPlane_card] at h
  have hKcard : Nat.card K = 64 * a.ker.index := by
    rw [← a.ker.card_mul_index, hcard]
  have h3 : 3 ∣ Nat.card K := by
    by_contra hn
    apply hK
    apply IsPGroup.of_card_dvd_pow (n := 9)
    rw [hKcard] at hn ⊢
    have h := Nat.mul_dvd_mul_left 64 (divisor_twentyfour _ hindex hn)
    exact h
  exact exists_prime_orderOf_dvd_card' 3 h3

private def planeRep : Fin 4 → H := ![1, pi, mu, pi * mu]

private noncomputable def planePoint (i : Fin 4) : muPlane D e :=
  ⟨D.a10ModelEmbedding e (planeRep i), by
    rw [muPlane_mem]
    fin_cases i
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl (D.a10ModelEmbedding_central e))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (by
        change D.a10ModelEmbedding e (pi * mu) = _
        rw [map_mul, D.a10ModelEmbedding_central e]; rfl)))⟩

private theorem planePoint_bijective : Function.Bijective (planePoint D e) := by
  have hrep : Function.Injective planeRep := by decide +kernel
  apply Function.Injective.bijective_of_nat_card_le
  · intro i j hij
    exact hrep (D.a10ModelEmbedding_injective e
      (congrArg (fun x : muPlane D e => (x : G)) hij))
  · rw [muPlane_card, Nat.card_fin]

private noncomputable def planeEquiv : Fin 4 ≃ muPlane D e :=
  Equiv.ofBijective (planePoint D e) (planePoint_bijective D e)

private theorem three_perm_orientation (σ : Perm (Fin 4))
    (hσ : σ ^ 3 = 1) (h0 : σ 0 = 0) (hne : σ ≠ 1) :
    (σ 1 = 2 ∧ σ 2 = 3) ∨ (σ⁻¹ 1 = 2 ∧ σ⁻¹ 2 = 3) := by
  have h : ∀ σ : Perm (Fin 4), σ ^ 3 = 1 → σ 0 = 0 → σ ≠ 1 →
      (σ 1 = 2 ∧ σ 2 = 3) ∨ (σ⁻¹ 1 = 2 ∧ σ⁻¹ 2 = 3) := by decide +kernel
  exact h σ hσ h0 hne

/-- Held's order-three actor under the three contrary fusion assumptions.
The equations use the source convention x^v = v⁻¹*x*v. -/
public theorem exists_mu_three_actor
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) :
    ∃ v : G, v ∈ normalizer (ambientElementary D e 0 : Set G) ∧ orderOf v = 3 ∧
      v⁻¹ * D.z * v = D.a10NoncentralInvolution e ∧
      v⁻¹ * D.a10NoncentralInvolution e * v = D.z * D.a10NoncentralInvolution e := by
  obtain ⟨K, hQK, hKV, hKM, hK⟩ := exists_mu_join D e hmu hlam hno
  obtain ⟨v, hv⟩ := exists_three_in_mu_join D e K hQK hKV hK
  let a := planeAction D e K hKV
  let E := planeEquiv D e
  let b : K →* Perm (Fin 4) := E.symm.permCongrHom.toMonoidHom.comp a
  have hpoint (w : K) (i j : Fin 4) (hw : b w i = j) :
      a w (planePoint D e i) = planePoint D e j := by
    have hh := congrArg E hw
    exact (E.apply_symm_apply _).symm.trans hh
  have hcube : b v ^ 3 = 1 := by
    rw [← map_pow, ← hv, pow_orderOf_eq_one, map_one]
  have hzero : b v 0 = 0 := by
    apply E.injective
    change E (E.symm (a v (E 0))) = E 0
    rw [E.apply_symm_apply]
    apply Subtype.ext
    change (v : G) * D.a10ModelEmbedding e 1 * (v : G)⁻¹ = D.a10ModelEmbedding e 1
    simp
  have hne : b v ≠ 1 := by
    intro h
    have ha : a v = 1 := E.symm.permCongrHom.injective (h.trans (map_one _).symm)
    have hvmem : (v : G) ∈ muIntersection D e := by
      have hh : v ∈ a.ker := ha
      rw [planeAction_ker] at hh
      exact hh
    have hd := (muIntersection D e).orderOf_dvd_natCard hvmem
    rw [muIntersection_card, orderOf_coe, hv] at hd
    norm_num at hd
  have finish (w : K) (hw : orderOf w = 3)
      (h1 : b w 1 = 2) (h2 : b w 2 = 3) :
      ∃ v : G, v ∈ normalizer (ambientElementary D e 0 : Set G) ∧ orderOf v = 3 ∧
        v⁻¹ * D.z * v = D.a10NoncentralInvolution e ∧
        v⁻¹ * D.a10NoncentralInvolution e * v = D.z * D.a10NoncentralInvolution e := by
    refine ⟨(w : G)⁻¹, (normalizer _).inv_mem (hKM w.property), ?_, ?_, ?_⟩
    · rw [orderOf_inv, orderOf_coe, hw]
    · have hh := congrArg (fun x : muPlane D e => (x : G)) (hpoint w 1 2 h1)
      change (w : G) * D.a10ModelEmbedding e Coordinates.pi * (w : G)⁻¹ =
        D.a10NoncentralInvolution e at hh
      simpa only [D.a10ModelEmbedding_central e, inv_inv] using hh
    · have hh := congrArg (fun x : muPlane D e => (x : G)) (hpoint w 2 3 h2)
      change (w : G) * D.a10ModelEmbedding e mu * (w : G)⁻¹ =
        D.a10ModelEmbedding e (Coordinates.pi * mu) at hh
      have hm : D.a10ModelEmbedding e mu = D.a10NoncentralInvolution e := rfl
      simpa only [map_mul, D.a10ModelEmbedding_central e, hm, inv_inv] using hh
  rcases three_perm_orientation (b v) hcube hzero hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact finish v hv h1 h2
  · exact finish v⁻¹ (by rw [orderOf_inv, hv]) (by simpa using h1) (by simpa using h2)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
