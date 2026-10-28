module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderContainment
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Inner

/-!
# Full source Bender Sylow containment

Any saturated pair, rather than only a newly chosen maximal pair, admits
an original source Sylow and central involution in its two-core. The actual
1.1.5 component marking and proved Bender automorphism calculation supply
nontrivial inner action. The stabilizer-orbit projection then proves all
of 2.5.3(3), including components permuted by H_U. No classification,
inner-action, projection or Sylow-uniqueness certificate is assumed.

Source: Aschbacher--Smith 2.5.3(3), printed p.552, using 2.3.8--9 and
1.1.5. The argument retains the original normalizer-intersection family.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The actual saturated pair supplies the original ambient 1.1.5 mark. -/
theorem exists_marking_of_saturated_pair
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU) :
    ∃ (S : Sylow 2 H) (z : G), Chapter1.Lemma115Hypotheses H S M z ∧
      z ∈ (center (twoCore HU)).map (twoCore HU).subtype := by
  have hgamma : H ∈ gamma (Chapter1.He G) M :=
    hH.elim (fun hh => hh.1.1) (fun hh => hh.1)
  obtain ⟨P, hUP, hPb⟩ := beta_exists_sylow hpair.1.1 hpair.1.2.2.2.1
  obtain ⟨S, hPS, _hSb⟩ := beta_exists_sylow hPb ((map_subtype_le _).trans hpair.2)
  have hUS : U ≤ (S : Subgroup H).map H.subtype := hUP.trans hPS
  have hMe : M ∈ Chapter1.He G :=
    Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T₀ M hM hT₀M)
  obtain ⟨R, hRM, hSR, hZS, _hZC⟩ := lemma_2_3_9_3 T₀ hT₀M hunique hMe
    hH hpair S hUS
  have hRne : (R : Subgroup G) ≠ ⊥ := by
    intro hb
    exact hSR.not_ge (hb ▸ bot_le)
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot _).mpr hRne
  let : Nontrivial (center R) := R.isPGroup'.center_nontrivial
  have hd : 2 ∣ Nat.card (center R) :=
    ((R.isPGroup'.to_subgroup (center R)).card_eq_or_dvd.resolve_left
      (by have := Finite.one_lt_card (α := center R); omega))
  obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card' (G := center R) 2 hd
  let zG : G := ((z : R) : G)
  have hzR : zG ∈ (center (R : Subgroup G)).map (R : Subgroup G).subtype :=
    mem_map_of_mem _ z.property
  have hz2 : orderOf zG = 2 := by
    dsimp [zG]
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzo]
  have hSi := (lemma_2_3_8_1 T₀ hT₀M hunique hgamma hpair S hUS).2.2.2
  have hRi : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = (R : Subgroup G) := by
    refine ⟨R.subtype hRM, ?_⟩
    simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hRM]
  let d : SourceTuple M H ((S : Subgroup H).map H.subtype) (R : Subgroup G) zG :=
    ⟨hH, hSi, hRi, hZS, hSR, hz2, hzR⟩
  have hQS : twoCore HU ≤ (S : Subgroup H).map H.subtype :=
    (pCoreIn_le_sylow HU P).trans hPS
  have hzQ := SourceTuple.central_involution_mem_core_of_saturation d hG.evenCharacteristic
    hMe B hp hBH hHnorm hpair hQS hsat
  have hzcenter : zG ∈ (center (twoCore HU)).map (twoCore HU).subtype := by
    refine ⟨⟨zG, hzQ⟩, mem_center_iff.mpr ?_, rfl⟩
    intro q
    apply Subtype.ext
    change (q : G) * zG = zG * (q : G)
    exact congrArg (fun a : R => (a : G))
      (mem_center_iff.mp z.property ⟨q, hSR.le (hQS q.property)⟩)
  have hzc (x : G) (hx : x ∈ R) : x * zG = zG * x :=
    congrArg (fun a : R => (a : G)) (mem_center_iff.mp z.property ⟨x, hx⟩)
  have hMcentral : ∃ P : Sylow 2 M,
      ∀ x ∈ (P : Subgroup M).map M.subtype, x * zG = zG * x := by
    obtain ⟨P, hP⟩ := hRi
    exact ⟨P, fun x hx => hzc x (show x ∈ (R : Subgroup G) from hP ▸ hx)⟩
  exact ⟨S, zG, lemma_2_3_8_6 hG T₀ hM hT₀M hunique hH hpair S hUS hz2
    (hZS hzR) (fun x hx => hzc x (hSR.le hx)) hMcentral, hzcenter⟩

/-- The original marked component has nontrivial inner action when its
actual carrier is one of the three Bender models. -/
theorem bender_inner_projection_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : ClassificationModels.IsBenderModel D) :
    (⟨z, h.mem_intersection.1⟩ : H) ∈ D ⊔ centralizer (D : Set H) ∧
      (⟨z, h.mem_intersection.1⟩ : H) ∉ centralizer (D : Set H) := by
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hc := BenderFusion.OmegaNormalizerModels.centerless_of_bender_model hm
  let e : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  obtain ⟨_hout, α, P, ha, d, _hcomm⟩ := h.component_inputs D hD
  obtain ⟨t, rfl⟩ := d.bender_inner (hm.of_mulEquiv e)
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

/-- Full source 2.5.3(3), on the original pair and every actual Bender
component; all earlier marking and model-geometry inputs are discharged. -/
theorem lemma_2_5_3_three
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
    (hm : ClassificationModels.IsBenderModel D) :
    ∃ P : Sylow 2 D, ((P : Subgroup D).map D.subtype).map H.subtype =
      D.map H.subtype ⊓ twoCore HU := by
  obtain ⟨S, z, h, hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hp hBH hHnorm hpair hsat
  obtain ⟨hi, hn⟩ := bender_inner_projection_of_source_marking h D hD hm
  exact bender_component_sylow_intersection_of_inner hpair hsat D hD hm
    ⟨z, h.mem_intersection.1⟩ (map_subtype_le _ hz) hi hn

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
