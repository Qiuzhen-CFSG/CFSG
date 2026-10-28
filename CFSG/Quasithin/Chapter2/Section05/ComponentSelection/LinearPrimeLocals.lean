module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearPrimeSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Projection
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import GorensteinWalter.PSL2Center
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Original prime-linear projection and local normalizers

The source marked automorphism of a PSL2 prime-field component is inner.
The model is centerless, so its inducing element is an involution. The
source fixed subgroup has characteristic two; actual conjugacy of all
model involutions carries that condition to every involution centralizer.
The prime-centralizer criterion then proves the local He condition for
every nontrivial two-subgroup normalizer, under the original embeddings.

The source mark lies in the saturated core and acts noncentrally; the
component projection theorem therefore makes D∩Q nontrivial. No matrix
centralizer assumption, innerness or nontriviality premise remains.

Source: Aschbacher--Smith 2.5.2(4) and 2.5.3(4), printed pp.551--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Chapter1.QuasisimpleInvolutions ComponentRefinement
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

omit [Finite G] in
private theorem prime_model_center {D : Subgroup H} {p : ℕ} [Fact p.Prime]
    (e : D ≃* PSL(2, ZMod p)) : center D = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hb : e a ∈ center (PSL(2, ZMod p)) := ((centerCongr e) ⟨a, ha⟩).property
  have hb1 : e a = 1 := by
    simpa only [GorensteinWalter.psl2_center_eq_bot (ZMod p), mem_bot] using hb
  exact mem_bot.mpr (e.injective (hb1.trans (map_one e).symm))

private theorem prime_marked_inner {D : Subgroup H} [IsQuasisimple D]
    {α : MulAut D} {P : Sylow 2 D} (d : MarkedInvolution α P)
    {p : ℕ} [Fact p.Prime] (hbig : 7 < p) (e : D ≃* PSL(2, ZMod p)) :
    α ∈ (MulAut.conj (G := D)).range := by
  let q : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq (prime_model_center e)).trans QuotientGroup.quotientBot
  exact (d.linear_two_prime_inner_and_center (Fact.out : p.Prime)
    ((Fact.out : p.Prime).odd_of_ne_two (by omega))
    ⟨ZMod p, inferInstance, inferInstance, by simp, ⟨q.trans e⟩⟩).1

/-- Innerness and noncentrality of the actual mark in the prime linear branch. -/
theorem linear_prime_inner_projection_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (p : ℕ) [Fact p.Prime] (hbig : 7 < p) (e : D ≃* PSL(2, ZMod p)) :
    (⟨z, h.mem_intersection.1⟩ : H) ∈ D ⊔ centralizer (D : Set H) ∧
      (⟨z, h.mem_intersection.1⟩ : H) ∉ centralizer (D : Set H) := by
  let : IsQuasisimple D := hD.2
  obtain ⟨_hout, α, P, ha, d, _hc⟩ := h.component_inputs D hD
  obtain ⟨t, rfl⟩ := prime_marked_inner d hbig e
  let zH : H := ⟨z, h.mem_intersection.1⟩
  have hconj (x : D) : zH * (x : H) * zH⁻¹ = (t : H) * x * (t : H)⁻¹ :=
    Subtype.ext (ha x).symm
  have hcentral : (t : H)⁻¹ * zH ∈ centralizer (D : Set H) := by
    intro x hx
    have he : ((t : H)⁻¹ * zH) * x * ((t : H)⁻¹ * zH)⁻¹ = x := by
      calc
        _ = (t : H)⁻¹ * (zH * x * zH⁻¹) * t := by group
        _ = x := by rw [hconj ⟨x, hx⟩]; group
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  refine ⟨?_, ?_⟩
  · have hz : zH = (t : H) * ((t : H)⁻¹ * zH) := by group
    change zH ∈ _
    rw [hz]
    exact mul_mem (mem_sup_left t.property) (mem_sup_right hcentral)
  · intro hz
    have he : MulAut.conj t = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change (t : H) * (x : H) * (t : H)⁻¹ = x
      rw [← hconj]
      have hcomm : (x : H) * zH = zH * x := hz x x.property
      rw [← hcomm]
      exact mul_inv_cancel_right _ _
    have hh := d.order_two
    simp [he] at hh

/-- Every nontrivial two-subgroup normalizer in the actual prime linear
component lies in He. Its involution centralizer is supplied by the original
mark and transported through genuine involution conjugacy. -/
theorem linear_prime_normalizer_mem_He_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (p : ℕ) [Fact p.Prime] (hbig : 7 < p) (e : D ≃* PSL(2, ZMod p))
    (R : Subgroup D) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    ((normalizer (R : Set D)).map D.subtype).map H.subtype ∈ Chapter1.He G := by
  let : IsQuasisimple D := hD.2
  obtain ⟨_hout, α, P, _ha, d, _hc⟩ := h.component_inputs D hD
  have hi := prime_marked_inner d hbig e
  have hn : α ≠ 1 := by intro hh; have htwo := d.order_two; simp [hh] at htwo
  obtain ⟨t, ht, _⟩ := exists_unique_inner_involution (prime_model_center e) α
    (d.order_two ▸ pow_orderOf_eq_one α) hn hi
  have hfixed : α.fixedSubgroup = centralizer ({t} : Set D) := by
    rw [← ht.1, MulAut.fixedSubgroup_conj]
  have htchar : centralizer (pCore 2 (centralizer ({t} : Set D)) :
      Set (centralizer ({t} : Set D))) ≤ pCore 2 (centralizer ({t} : Set D)) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (MulEquiv.subgroupCongr hfixed)).mp
      d.characteristic_two
  have hall : ∀ u : D, orderOf u = 2 →
      centralizer (pCore 2 (centralizer ({u} : Set D)) :
        Set (centralizer ({u} : Set D))) ≤ pCore 2 (centralizer ({u} : Set D)) := by
    intro u hu
    have hc : IsConj u t := by
      have hh := e.symm.toMonoidHom.map_isConj
        (Theory.PSL2.involutions_isConj (e u) (e t)
          ((e.orderOf_eq u).trans hu) ((e.orderOf_eq t).trans ht.2))
      simpa using hh
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    let f := MulAut.conj g
    have hf : f u = t := hg
    let j := (CentralizerSmallKernelTransport.centralizerEquiv f u).trans
      (MulEquiv.subgroupCongr (congrArg (fun v : D => centralizer ({v} : Set D)) hf))
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mpr htchar
  have hc := normalizer_core_selfCentralizing_of_prime_centralizers hall R hp hne
  apply Chapter1.mem_He_iff.mpr
  let j := (equivMapOfInjective (normalizer (R : Set D)) D.subtype D.subtype_injective).trans
    (equivMapOfInjective ((normalizer (R : Set D)).map D.subtype) H.subtype H.subtype_injective)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mp hc

/-- The original prime-linear source mark gives a nontrivial saturated component radical. -/
theorem linear_prime_component_intersection_ne_bot
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (p : ℕ) [Fact p.Prime] (hbig : 7 < p) (e : D ≃* PSL(2, ZMod p)) :
    D ⊓ (twoCore HU).subgroupOf H ≠ ⊥ := by
  obtain ⟨S, z, h, hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hp hBH hHnorm hpair hsat
  obtain ⟨hi, hn⟩ := linear_prime_inner_projection_of_source_marking h D hD p hbig e
  have hsatH : ∀ P : Subgroup H, IsPGroup 2 P →
      HU.subgroupOf H ≤ normalizer (P : Set H) → P ≤ (twoCore HU).subgroupOf H := by
    intro P hp hn x hx
    have hna : HU ≤ normalizer (P.map H.subtype : Set G) := by
      intro a ha
      exact P.le_normalizer_map H.subtype ⟨⟨a, hpair.2 ha⟩, hn ha, rfl⟩
    exact hsat _ (map_subtype_le P) (hp.map H.subtype) hna
      (mem_map_of_mem H.subtype hx)
  have hAQ : HU.subgroupOf H ≤ normalizer ((twoCore HU).subgroupOf H : Set H) := by
    intro a ha x
    exact le_normalizer_twoCore HU ha (x : G)
  obtain ⟨d, hd, hnc⟩ := hD.exists_noncentral_intersection_of_saturation
    (prime_model_center e ▸ IsPGroup.of_bot)
    (isPGroup_pCoreIn 2 HU).comap_subtype hAQ hsatH
    (show (⟨z, h.mem_intersection.1⟩ : H) ∈ (twoCore HU).subgroupOf H from (show z ∈ twoCore HU from map_subtype_le (center (twoCore HU)) hz))
    hi hn
  intro hb
  exact hnc ((mem_bot.mp (hb ▸ hd)).symm ▸ (centralizer (D : Set H)).one_mem)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
