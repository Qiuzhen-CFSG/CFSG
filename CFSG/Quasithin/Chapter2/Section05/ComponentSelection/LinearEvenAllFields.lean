module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearEvenSource
public import Theory.SpecificGroups.PSL3.EvenLocalNormalizers.AllFields
/-!
# The entire even PSL₃-cover escaping source family

The all-positive-fields local theorem fills the binary endpoint. The existing
source mark proves innerness and that the entire center is a two-group.
Saturation provides a noncentral radical element and contains the center.
The actual quotient normalizer therefore has characteristic two at every
field size, and the original escaping branch preserves Γ₀ and both stars.

Source: Aschbacher–Smith, 2.5.2(2) and 2.5.3(4), printed pp.551–553.
All older n≥2 declarations and central-cover conventions remain unchanged.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Chapter1.QuasisimpleInvolutions
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}
theorem linear_even_cover_radical_mem_He_all_fields
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (f : D →* PSL(3,F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hne : ((((twoCore HU).subgroupOf H).subgroupOf D).map f) ≠ ⊥) :
    (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ∈ Chapter1.He G := by
  let Q := (twoCore HU).subgroupOf H
  let R := Q.subgroupOf D
  have hker : f.ker ≤ R := (le_sSup ⟨inferInstance, hk⟩ : f.ker ≤ pCore 2 D).trans
    (component_twoCore_le_saturated_intersection hpair hsat D hD)
  have hc := Matrix.PSL3.EvenInnerCentralizers.cover_normalizer_core_selfCentralizing_of_positive F
    f hf hk hn hF R (isPGroup_pCoreIn 2 HU).comap_subtype.comap_subtype hker hne
  have hnorm : (normalizer (R : Set D)).map D.subtype = D ⊓ normalizer ((D ⊓ Q : Subgroup H) : Set H) := by
    have he : R = (D ⊓ Q).subgroupOf D := by ext x; simp [R]
    rw [he, ← subgroupOf_normalizer_eq (show D ⊓ Q ≤ D from inf_le_left),
      subgroupOf_map_subtype, inf_comm]
  apply Chapter1.mem_He_iff.mpr
  let j := (equivMapOfInjective (normalizer (R : Set D)) D.subtype D.subtype_injective).trans
    (equivMapOfInjective ((normalizer (R : Set D)).map D.subtype) H.subtype H.subtype_injective)
  have hh := (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mp hc
  rwa [hnorm] at hh

theorem linear_even_cover_radical_source_all_fields
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
    (F : Type) [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : D ⧸ center D ≃* PSL(3,F)) :
    D ⊓ (twoCore HU).subgroupOf H ≠ ⊥ ∧
    (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ∈ Chapter1.He G := by
  obtain ⟨S, z, h, hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hp hBH hHnorm hpair hsat
  obtain ⟨hi, hn, hcenter⟩ := linear_even_inner_projection_of_source_marking h D hD
    F (by omega) hF e
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
  have hZp : IsPGroup 2 (center D) := hcenter ▸ pCore_isPGroup
  obtain ⟨d, hd, hnc⟩ := hD.exists_noncentral_intersection_of_saturation hZp
    (isPGroup_pCoreIn 2 HU).comap_subtype hAQ hsatH
    (show (⟨z, h.mem_intersection.1⟩ : H) ∈ (twoCore HU).subgroupOf H from
      (show z ∈ twoCore HU from map_subtype_le (center (twoCore HU)) hz)) hi hn
  have hne : D ⊓ (twoCore HU).subgroupOf H ≠ ⊥ := by
    intro hb
    exact hnc ((mem_bot.mp (hb ▸ hd)).symm ▸ (centralizer (D : Set H)).one_mem)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center D))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_mk']
  have himage : (((twoCore HU).subgroupOf H).subgroupOf D).map f ≠ ⊥ := by
    intro hb
    have hx : f ⟨d, hd.1⟩ = 1 := mem_bot.mp (hb ▸ mem_map_of_mem f hd.2)
    have hz : (⟨d, hd.1⟩ : D) ∈ center D := hker ▸ (MonoidHom.mem_ker.mpr hx)
    apply hnc
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)
  exact ⟨hne, linear_even_cover_radical_mem_He_all_fields hpair hsat D hD F hk hF
    f hf (hker ▸ hZp) himage⟩

/-- The original source escaping branch for every marked binary PSL3 cover. -/
theorem linear_even_escaping_source_all_fields
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
    (F : Type) [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : D ⧸ center D ≃* PSL(3,F))
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  obtain ⟨hne, hNe⟩ := linear_even_cover_radical_source_all_fields hG T₀ hM hT₀M hunique hH
    B hp hBH hHnorm hpair hsat D hD F hk hF e
  exact component_join_preserves_stars_of_escaping_radical hH hpair hbig hsat S hUS D hD
    hne hNe hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
