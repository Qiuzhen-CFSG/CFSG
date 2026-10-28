module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticBinaryBorel
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RadicalEscape
public import Theory.SpecificGroups.AlternatingSix.LocalNormalizers
/-!
# The field-two symplectic escaping branch on original source data

The original empty-Γₑ₀ Borel theorem gives M∩D=S∩D for an A₆ component.
The marked involution's fixed subgroup lies there, and hence is a two-group.
The complete A₆ fixed-subgroup geometry forces its action to be inner; no
inner-action or diagram assumption is added. Saturation then supplies the
nontrivial component radical, whose actual normalizer has characteristic two.
The original escaping guard consequently preserves both star families.

Source: Aschbacher–Smith, 2.5.2(2) and 2.5.3(4), printed pp.551–553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Chapter1.QuasisimpleInvolutions
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}
theorem alternating_six_inner_projection_of_source_marking
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (e : D ≃* AlternatingSix.ShadowLocal.A6) :
    (⟨z, h.mem_intersection.1⟩ : H) ∈ D ⊔ centralizer (D : Set H) ∧
      (⟨z, h.mem_intersection.1⟩ : H) ∉ centralizer (D : Set H) := by
  let : IsQuasisimple D := hD.2
  obtain ⟨_hout, α, P, ha, d, _hcomm⟩ := h.component_inputs D hD
  have hI := alternating_six_intersection_eq_sylow_source hH hempty S h.mem_HeOver.2.2 D hD _hout e
  have hfix : GLS3.Chapter5.automorphismFixedSubgroup α ≤ (S : Subgroup H).subgroupOf D := by
    rw [← hI]
    intro x hx
    change α x = x at hx
    have he : z * (x : G) * z⁻¹ = (x : G) := (ha x).symm.trans
      (congrArg (fun a : D => ((a : H) : G)) hx)
    exact h.centralizer_le (mem_centralizer_singleton_iff.mpr
      ((mul_inv_eq_iff_eq_mul).mp he).symm)
  have hi : α ∈ (MulAut.conj (G := D)).range :=
    AlternatingSix.ShadowLocal.involution_inner_of_equiv_fixed_isTwoGroup e α d.order_two
      ((S.isPGroup'.comap_subtype).to_le hfix)
  obtain ⟨t, rfl⟩ := hi
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




theorem alternating_six_component_intersection_ne_bot
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (e : D ≃* AlternatingSix.ShadowLocal.A6) :
    D ⊓ (twoCore HU).subgroupOf H ≠ ⊥ := by
  obtain ⟨S, z, h, hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hp hBH hHnorm hpair hsat
  obtain ⟨hi, hn⟩ := alternating_six_inner_projection_of_source_marking hH hempty h D hD e
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
  have hc : center D = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have hb : e a ∈ center (alternatingGroup (Fin 6)) := ((centerCongr e) ⟨a,ha⟩).property
    have hb1 : e a = 1 := by
      rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6)),mem_bot] at hb
      exact hb
    exact mem_bot.mpr (e.injective (hb1.trans (map_one e).symm))
  obtain ⟨d, hd, hnc⟩ := hD.exists_noncentral_intersection_of_saturation
    (hc ▸ IsPGroup.of_bot)
    (isPGroup_pCoreIn 2 HU).comap_subtype hAQ hsatH
    (show (⟨z, h.mem_intersection.1⟩ : H) ∈ (twoCore HU).subgroupOf H from (show z ∈ twoCore HU from map_subtype_le (center (twoCore HU)) hz))
    hi hn
  intro hb
  exact hnc ((mem_bot.mp (hb ▸ hd)).symm ▸ (centralizer (D : Set H)).one_mem)


omit [Finite G] in
/-- The literal A₆ radical normalizer lies in He. -/
theorem alternating_six_radical_normalizer_mem_He
    (D : Subgroup H) (e : D ≃* alternatingGroup (Fin 6))
    (hne : D ⊓ (twoCore HU).subgroupOf H ≠ ⊥) :
    (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ∈ Chapter1.He G := by
  let Q := (twoCore HU).subgroupOf H
  let R := Q.subgroupOf D
  have hn : R ≠ ⊥ := by
    intro he
    have hm := congrArg (Subgroup.map D.subtype) he
    rw [subgroupOf_map_subtype, Subgroup.map_bot, inf_comm] at hm
    exact hne hm
  have hc := normalizer_core_selfCentralizing_of_equiv e R
    (AlternatingSix.ShadowLocal.normalizer_core_selfCentralizing (R.map e.toMonoidHom)
      ((isPGroup_pCoreIn 2 HU).comap_subtype.comap_subtype.map _)
      (fun hb => hn ((map_eq_bot_iff_of_injective _ e.injective).mp hb)))
  have hnorm : (normalizer (R : Set D)).map D.subtype = D ⊓ normalizer ((D ⊓ Q : Subgroup H) : Set H) := by
    have he : R = (D ⊓ Q).subgroupOf D := by ext x; simp [R]
    rw [he, ← subgroupOf_normalizer_eq (show D ⊓ Q ≤ D from inf_le_left),
      subgroupOf_map_subtype, inf_comm]
  apply Chapter1.mem_He_iff.mpr
  let j := (equivMapOfInjective (normalizer (R : Set D)) D.subtype D.subtype_injective).trans
    (equivMapOfInjective ((normalizer (R : Set D)).map D.subtype) H.subtype H.subtype_injective)
  have hh := (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mp hc
  rwa [hnorm] at hh
theorem alternating_six_escaping_source
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (D : Subgroup H) (hD : IsComponent H D)
    (e : D ≃* alternatingGroup (Fin 6))
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  have hn := alternating_six_component_intersection_ne_bot hG T₀ hM hT₀M hunique hH hempty
    B hp hBH hHnorm hpair hsat D hD e
  exact component_join_preserves_stars_of_escaping_radical hH hpair hbig hsat S hUS D hD hn
    (alternating_six_radical_normalizer_mem_He D e hn) hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
