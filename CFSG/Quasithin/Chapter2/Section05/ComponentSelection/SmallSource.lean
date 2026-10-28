module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.EscapingNormalizer
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderSource
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.LinearActions
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers

/-!
# Source construction of the small-component radical

For an actual PSL3(3) or M11 component, the original marked involution acts
nontrivially and innerly. The concrete Sylow-fixer and automorphism theorems
supply innerness; the actual source construction places the mark in O2(H_U).
The component-orbit projection therefore proves that the radical intersection
is nontrivial. The escaping-normalizer branch then preserves both stars,
with no marker, projection, local-core or characteristic-two certificate.

Source: Aschbacher--Smith 2.5.3(4), printed p.553, case 2.5.2(3).
The alternative in which the normalizer lies in M still requires the
component-removal induction. The full source component-model sieve remains
separate; this module uses the actual model isomorphism, not a reduced catalogue.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory

private theorem center_eq_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hb : e a ∈ center B := ((centerCongr e) ⟨a, ha⟩).property
  have hb1 : e a = 1 := by simpa only [h, mem_bot] using hb
  exact mem_bot.mpr (e.injective (hb1.trans (map_one e).symm))

private theorem small_center_eq_bot {A : Type*} [Group A]
    (hm : Nonempty (A ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (A ≃* Sporadic.Mathieu.M11)) :
    center A = ⊥ := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    exact center_eq_bot_transport (e.trans Matrix.PSL3Three.equiv.symm)
      Matrix.PSL3Three.center_eq_bot
  · obtain ⟨e⟩ := hm
    exact center_eq_bot_transport e Sporadic.Mathieu.m11_center_eq_bot

variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The genuine mark acts innerly and nontrivially on either small component. -/
theorem small_inner_projection_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11)) :
    (⟨z, h.mem_intersection.1⟩ : H) ∈ D ⊔ centralizer (D : Set H) ∧
      (⟨z, h.mem_intersection.1⟩ : H) ∉ centralizer (D : Set H) := by
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hc := small_center_eq_bot hm
  let e : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  obtain ⟨_hout, α, P, ha, d, _hcomm⟩ := h.component_inputs D hD
  have hi : α ∈ (MulAut.conj (G := D)).range := by
    rcases hm with hm | hm
    · obtain ⟨f⟩ := hm
      apply (d.linear_three_three_inner_and_center ?_).1
      exact ⟨ZMod 3, inferInstance, inferInstance, by norm_num, ⟨e.trans f⟩⟩
    · obtain ⟨f⟩ := hm
      obtain ⟨t, ht⟩ := Sporadic.Mathieu.automorphism_inner_of_equiv_m11 f α
      exact ⟨t, ht.symm⟩
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


/-- The actual saturated source pair has nontrivial intersection with each
PSL3(3) or M11 component, with all marking and projection inputs discharged. -/
theorem small_component_intersection_ne_bot
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
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11)) :
    D ⊓ (twoCore HU).subgroupOf H ≠ ⊥ := by
  obtain ⟨S, z, h, hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hp hBH hHnorm hpair hsat
  obtain ⟨hi, hn⟩ := small_inner_projection_of_source_marking h D hD hm
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
    (small_center_eq_bot hm ▸ IsPGroup.of_bot)
    (isPGroup_pCoreIn 2 HU).comap_subtype hAQ hsatH
    (show (⟨z, h.mem_intersection.1⟩ : H) ∈ (twoCore HU).subgroupOf H from (show z ∈ twoCore HU from map_subtype_le (center (twoCore HU)) hz))
    hi hn
  intro hb
  exact hnc ((mem_bot.mp (hb ▸ hd)).symm ▸ (centralizer (D : Set H)).one_mem)

/-- Original source hypotheses discharge every extra input in the small-model
escaping-normalizer branch; only the literal branch guard remains. -/
theorem small_component_escaping_source
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
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
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11))
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) :=
  small_component_join_preserves_stars_of_escaping_normalizer hH hpair hbig hsat S hUS D hD hm
    (small_component_intersection_ne_bot hG T₀ hM hT₀M hunique hH B hp hBH hHnorm
      hpair hsat D hD hm) hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
