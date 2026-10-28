module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Mathlib.GroupTheory.IndexNormal

/-!
# Order-64 centralizer overgroups in Held's S-normalizer argument

For the tau and pi-lambda alternatives, the local centralizers have order 32
and equal the source groups S⟨tau′⟩ and S⟨mu′xi⟩. Fusion with pi supplies
order-64 overgroups in the actual ambient centralizers. Such an overgroup
cannot join the displayed Sylow subgroup in a two-group.

The elementary-sixteen catalogue makes S the unique elementary sixteen in
C_H(tau). Consequently S is characteristic in that local centralizer, and
index-two normality shows that each order-64 overgroup normalizes S.
Characteristicity is relative to C_H(tau), not to the ambient group.

This module does not assert pi-lambda normalizer containment or classify
N_G(S)/S; those are separate remaining steps of the source argument.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.228.
The source convention is x^g = g⁻¹*x*g.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

/-- The two involutions excluded by the middle paragraph of Held 2.6. -/
@[expose] public def sCaseElement : Fin 2 → H := ![tau, pi * lam]

public abbrev sCaseCentralizer (i : Fin 2) : Subgroup H :=
  centralizer ({sCaseElement i} : Set H)

public theorem sCaseCentralizer_card (i : Fin 2) : Nat.card (sCaseCentralizer i) = 32 := by
  fin_cases i
  · exact involution_centralizer_cards.2.2.1
  · exact involution_centralizer_cards.2.2.2.2.1

public theorem modelS_le_sCaseCentralizer (i : Fin 2) : modelS ≤ sCaseCentralizer i := by
  have hx : sCaseElement i ∈ modelS := by
    fin_cases i
    · exact elementaryGenerators_mem 1 2
    · exact modelS.mul_mem (pi_mem_elementary 1) (elementaryGenerators_mem 1 3)
  intro y hy
  let := elementary_isElementaryAbelian 1
  exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hy hx)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem sCase_word_test : ∀ (i : Fin 2) (a : Code),
    word a * sCaseElement i = sCaseElement i * word a → a.2.2.2.1 = 0 := by
  decide +kernel

public theorem sCaseCentralizer_le_modelD (i : Fin 2) : sCaseCentralizer i ≤ modelD := by
  intro x hx
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  exact (word_mem_modelD a).mpr (sCase_word_test i a (mem_centralizer_singleton_iff.mp hx))

/-- The fifth generator in S⟨tau′⟩ and S⟨mu′xi⟩ from Held p.228. -/
@[expose] public def sCaseExtra : Fin 2 → H := ![taup, mup * xi]

public theorem sCaseExtra_mem (i : Fin 2) : sCaseExtra i ∈ sCaseCentralizer i := by
  apply mem_centralizer_singleton_iff.mpr
  revert i
  decide +kernel

public theorem sCaseExtra_not_mem_S (i : Fin 2) : sCaseExtra i ∉ modelS := by
  intro h
  obtain ⟨a, ha⟩ := (mem_elementary 1 _).mp h
  have hn : ∀ (j : Fin 2) (b : BaseCode), elementaryWord 1 b ≠ sCaseExtra j := by
    decide +kernel
  exact hn i a ha

/-- The two local order-32 groups are precisely the displayed source overgroups of S. -/
public theorem sCaseCentralizer_eq_sup (i : Fin 2) :
    sCaseCentralizer i = modelS ⊔ zpowers (sCaseExtra i) := by
  let K := modelS ⊔ zpowers (sCaseExtra i)
  have hK : K ≤ sCaseCentralizer i :=
    sup_le (modelS_le_sCaseCentralizer i) (zpowers_le.mpr (sCaseExtra_mem i))
  have hSK : modelS ≤ K := le_sup_left
  have hdvd : 16 ∣ Nat.card K := by
    rw [← elementary_card 1]
    exact card_dvd_of_le hSK
  have hlo : 16 < Nat.card K := by
    by_contra hn
    have he : modelS = K := eq_of_le_of_card_ge hSK (by
      rw [elementary_card 1]
      omega)
    exact sCaseExtra_not_mem_S i (he ▸
      (show sCaseExtra i ∈ K from (show zpowers (sCaseExtra i) ≤ K from le_sup_right) (mem_zpowers _)))
  have hhi : Nat.card K ≤ 32 := by
    have h := card_le_of_le hK
    rwa [sCaseCentralizer_card] at h
  have he : Nat.card K = 32 := by omega
  exact (eq_of_le_of_card_ge hK (by rw [he, sCaseCentralizer_card])).symm

/-- Among the four elementary sixteens in D only S centralizes tau. -/
public theorem tau_centralizer_unique_elementary_sixteen (A : Subgroup H)
    (hA : A ≤ sCaseCentralizer 0) (he : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 16) : A = modelS := by
  obtain ⟨k, rfl⟩ := model_elementary_sixteen A
    (hA.trans (sCaseCentralizer_le_modelD 0)) he hc
  fin_cases k
  · have h := mem_centralizer_singleton_iff.mp (hA (elementaryGenerators_mem 0 2))
    have hn : elementaryGenerators 0 2 * sCaseElement 0 ≠
        sCaseElement 0 * elementaryGenerators 0 2 := by decide +kernel
    exact (hn h).elim
  · rfl
  · have h := mem_centralizer_singleton_iff.mp (hA (elementaryGenerators_mem 2 3))
    have hn : elementaryGenerators 2 3 * sCaseElement 0 ≠
        sCaseElement 0 * elementaryGenerators 2 3 := by decide +kernel
    exact (hn h).elim
  · have h := mem_centralizer_singleton_iff.mp (hA (elementaryGenerators_mem 3 3))
    have hn : elementaryGenerators 3 3 * sCaseElement 0 ≠
        sCaseElement 0 * elementaryGenerators 3 3 := by decide +kernel
    exact (hn h).elim

/-- Characteristic means characteristic inside C_H(tau), not inside H. -/
public theorem modelS_characteristic_tau_centralizer :
    (modelS.subgroupOf (sCaseCentralizer 0)).Characteristic := by
  let Q := sCaseCentralizer 0
  let A := modelS.subgroupOf Q
  have hcA : Nat.card A = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (modelS_le_sCaseCentralizer 0)).toEquiv).trans
      (elementary_card 1)
  let := elementary_isElementaryAbelian 1
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (modelS_le_sCaseCentralizer 0)
  apply characteristic_iff_map_le.mpr
  intro a
  have hu : (A.map a.toMonoidHom).map Q.subtype = modelS := by
    apply tau_centralizer_unique_elementary_sixteen
    · exact map_subtype_le _
    · let := IsElementaryAbelian.map (p := 2) a.toMonoidHom (A := A)
      exact IsElementaryAbelian.map Q.subtype
    · rw [card_map_of_injective Q.subtype_injective,
        card_map_of_injective a.injective, hcA]
  intro x hx
  show (x : H) ∈ modelS
  rw [← hu]
  exact ⟨x, hx, rfl⟩

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

@[expose] public noncomputable def ambientSCaseCentralizer (i : Fin 2) : Subgroup G :=
  (sCaseCentralizer i).map (D.a10ModelEmbedding e)

public theorem ambientSCaseCentralizer_eq (i : Fin 2) :
    ambientSCaseCentralizer D e i = D.centralizer ⊓
      centralizer ({D.a10ModelEmbedding e (sCaseElement i)} : Set G) := by
  let f := D.a10ModelEmbedding e
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

public theorem ambientSCaseCentralizer_card (i : Fin 2) :
    Nat.card (ambientSCaseCentralizer D e i) = 32 := by
  rw [ambientSCaseCentralizer, card_map_of_injective (D.a10ModelEmbedding_injective e)]
  exact sCaseCentralizer_card i

public theorem ambientS_le_sCaseCentralizer (i : Fin 2) :
    ambientElementary D e 1 ≤ ambientSCaseCentralizer D e i :=
  map_mono (modelS_le_sCaseCentralizer i)

public theorem ambientSCaseCentralizer_le_ambientD (i : Fin 2) :
    ambientSCaseCentralizer D e i ≤ ambientD D e :=
  map_mono (sCaseCentralizer_le_modelD i)

variable [Finite G]

/-- Each fused case centralizer contains an order-64 overgroup of its local order-32 group. -/
public theorem exists_sCase_centralizer_overgroup (i : Fin 2)
    (hi : IsConj D.z (D.a10ModelEmbedding e (sCaseElement i))) :
    ∃ P : Subgroup G, Nat.card P = 64 ∧
      ambientSCaseCentralizer D e i ≤ P ∧
      P ≤ centralizer ({D.a10ModelEmbedding e (sCaseElement i)} : Set G) := by
  let C := centralizer ({D.a10ModelEmbedding e (sCaseElement i)} : Set G)
  let Q := ambientSCaseCentralizer D e i
  have hQC : Q ≤ C := by
    change ambientSCaseCentralizer D e i ≤ C
    rw [ambientSCaseCentralizer_eq]
    exact inf_le_right
  have hQ : Nat.card (Q.subgroupOf C) = 2 ^ 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, ambientSCaseCentralizer_card]
    norm_num
  have hd : 2 ^ 6 ∣ Nat.card C := by
    rw [centralizer_card_of_isConj D hi]
    norm_num
  obtain ⟨P, hP, hQP⟩ := Sylow.exists_subgroup_card_pow_prime_le 2 hd (Q.subgroupOf C) hQ
    (show 5 ≤ 6 by decide)
  refine ⟨P.map C.subtype, ?_, ?_, map_subtype_le _⟩
  · rw [card_map_of_injective C.subtype_injective, hP]
    norm_num
  · change Q ≤ P.map C.subtype
    rw [← map_subgroupOf_eq_of_le hQC]
    exact map_mono hQP

/-- The tau uniqueness statement transports to the actual ambient local centralizer. -/
public theorem ambient_tau_centralizer_unique_elementary_sixteen (A : Subgroup G)
    (hA : A ≤ ambientSCaseCentralizer D e 0) (he : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 16) : A = ambientElementary D e 1 := by
  obtain ⟨k, rfl⟩ := ambient_elementary_sixteen D e A
    (hA.trans (ambientSCaseCentralizer_le_ambientD D e 0)) he hc
  have ht (j : Fin 4) :
      elementaryGenerators k j * sCaseElement 0 =
        sCaseElement 0 * elementaryGenerators k j := by
    have hm := hA (show D.a10ModelEmbedding e (elementaryGenerators k j) ∈
      ambientElementary D e k from ⟨_, elementaryGenerators_mem k j, rfl⟩)
    rw [ambientSCaseCentralizer_eq] at hm
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hm.2
  fin_cases k
  · have hn : elementaryGenerators 0 2 * sCaseElement 0 ≠
        sCaseElement 0 * elementaryGenerators 0 2 := by decide +kernel
    exact (hn (ht 2)).elim
  · rfl
  · have hn : elementaryGenerators 2 3 * sCaseElement 0 ≠
        sCaseElement 0 * elementaryGenerators 2 3 := by decide +kernel
    exact (hn (ht 3)).elim
  · have hn : elementaryGenerators 3 3 * sCaseElement 0 ≠
        sCaseElement 0 * elementaryGenerators 3 3 := by decide +kernel
    exact (hn (ht 3)).elim

/-- The characteristic subgroup used in the tau case is relative to H ∩ C_G(tau). -/
public theorem ambientS_characteristic_tau_centralizer :
    ((ambientElementary D e 1).subgroupOf (ambientSCaseCentralizer D e 0)).Characteristic := by
  let Q := ambientSCaseCentralizer D e 0
  let A := (ambientElementary D e 1).subgroupOf Q
  have hcA : Nat.card A = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (ambientS_le_sCaseCentralizer D e 0)).toEquiv).trans
      (ambientElementary_card D e 1)
  let := ambientElementary_isElementaryAbelian D e 1
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.subgroupOf (ambientS_le_sCaseCentralizer D e 0)
  apply characteristic_iff_map_le.mpr
  intro a
  have hu : (A.map a.toMonoidHom).map Q.subtype = ambientElementary D e 1 := by
    apply ambient_tau_centralizer_unique_elementary_sixteen
    · exact map_subtype_le _
    · let := IsElementaryAbelian.map (p := 2) a.toMonoidHom (A := A)
      exact IsElementaryAbelian.map Q.subtype
    · rw [card_map_of_injective Q.subtype_injective,
        card_map_of_injective a.injective, hcA]
  intro x hx
  show (x : G) ∈ ambientElementary D e 1
  rw [← hu]
  exact ⟨x, hx, rfl⟩

/-- Every order-64 overgroup of the tau local centralizer normalizes S. -/
public theorem tau_overgroup_le_normalizer_S (P : Subgroup G)
    (hc : Nat.card P = 64) (hQP : ambientSCaseCentralizer D e 0 ≤ P) :
    P ≤ normalizer (ambientElementary D e 1 : Set G) := by
  let Q := ambientSCaseCentralizer D e 0
  have hindex : (Q.subgroupOf P).index = 2 := by
    have h := (Q.subgroupOf P).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv,
      ambientSCaseCentralizer_card, hc] at h
    omega
  have hQN : P ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQP).mp (normal_of_index_eq_two hindex)
  have hchar := ambientS_characteristic_tau_centralizer D e
  apply le_normalizer_iff.mpr
  intro g hg x hx
  let a := Q.normalizerMonoidHom ⟨g, hQN hg⟩
  have ha := characteristic_iff_le_comap.mp hchar a
    (show (⟨x, ambientS_le_sCaseCentralizer D e 0 hx⟩ : Q) ∈
      (ambientElementary D e 1).subgroupOf Q from hx)
  exact ha

/-- An order-64 centralizer overgroup cannot join the displayed Sylow in a two-group. -/
public theorem sCase_overgroup_sup_not_isPGroup (i : Fin 2) (P : Subgroup G)
    (hc : Nat.card P = 64)
    (hPC : P ≤ centralizer ({D.a10ModelEmbedding e (sCaseElement i)} : Set G)) :
    ¬ IsPGroup 2 (ambientD D e ⊔ P : Subgroup G) := by
  intro htwo
  have hjoin : ambientD D e ⊔ P = ambientD D e :=
    (ambientSylow D e).is_maximal' htwo le_sup_left
  have hPD : P ≤ ambientD D e := hjoin ▸ le_sup_right
  have hPQ : P ≤ ambientSCaseCentralizer D e i := by
    rw [ambientSCaseCentralizer_eq]
    refine le_inf ?_ hPC
    exact hPD.trans (by
      change modelD.map (D.a10ModelEmbedding e) ≤ D.centralizer
      rw [← D.a10ModelEmbedding_range e]
      exact map_le_range _ _)
  have hdvd := card_dvd_of_le hPQ
  rw [hc, ambientSCaseCentralizer_card] at hdvd
  norm_num at hdvd

/-- An order-64 centralizer overgroup inside N_G(S) makes that normalizer non-two. -/
public theorem sCase_overgroup_normalizer_not_isPGroup (i : Fin 2) (P : Subgroup G)
    (hc : Nat.card P = 64)
    (hPC : P ≤ centralizer ({D.a10ModelEmbedding e (sCaseElement i)} : Set G))
    (hPN : P ≤ normalizer (ambientElementary D e 1 : Set G)) :
    ¬ IsPGroup 2 (normalizer (ambientElementary D e 1 : Set G)) := by
  intro htwo
  exact sCase_overgroup_sup_not_isPGroup D e i P hc hPC
    (htwo.to_le (sup_le (ambientSylow_le_normalizer_S D e) hPN))

/-- The order-64 subgroup required by the source tau alternative, with all local premises proved. -/
public theorem exists_tau_overgroup_in_normalizer
    (htau : IsConj D.z (D.a10ModelEmbedding e tau)) :
    ∃ P : Subgroup G, Nat.card P = 64 ∧
      ambientSCaseCentralizer D e 0 ≤ P ∧
      P ≤ centralizer ({D.a10ModelEmbedding e tau} : Set G) ∧
      P ≤ normalizer (ambientElementary D e 1 : Set G) := by
  obtain ⟨P, hc, hQP, hPC⟩ := exists_sCase_centralizer_overgroup D e 0 htau
  exact ⟨P, hc, hQP, hPC, tau_overgroup_le_normalizer_S D e P hc hQP⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
