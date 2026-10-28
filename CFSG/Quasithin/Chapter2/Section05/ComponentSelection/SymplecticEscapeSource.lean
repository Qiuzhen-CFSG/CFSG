module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticLocals
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RadicalEscape
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Inner

/-!
# The nonbinary symplectic escaping branch on original source hypotheses

The genuine marked Sylow fixer is inner and its action on the component is
nontrivial. Original component saturation therefore supplies a noncentral
element of D∩O₂(H_U). Its nontrivial image in Sp₄ lets the concrete local
normalizer theorem apply, including any two-primary cover kernel. The
original escaping-normalizer guard then preserves Γ₀ and both star families.

Source: Aschbacher–Smith, 2.5.2(2) and 2.5.3(4), printed pp.551–553.
The field-two derived carrier A₆ belongs to a separate source branch.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Chapter1.QuasisimpleInvolutions
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The genuine source marking supplies inner noncentral projection and the
full two-primary center, including the exceptional binary central cover. -/
theorem symplectic_inner_projection_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : D ⧸ center D ≃* ClassicalGroup.PSp 2 F) :
    (⟨z, h.mem_intersection.1⟩ : H) ∈ D ⊔ centralizer (D : Set H) ∧
      (⟨z, h.mem_intersection.1⟩ : H) ∉ centralizer (D : Set H) ∧
      center D = pCore 2 D := by
  let : IsQuasisimple D := hD.2
  obtain ⟨_hout, α, P, ha, d, _hc⟩ := h.component_inputs D hD
  have hi := d.symplecticFour_inner hn ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  have hcenter := MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hi d.inverts_odd_core
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
  refine ⟨?_, ?_, hcenter⟩
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

/-- Saturation and the original inner mark give the actual cover normalizer
in He and a nontrivial component radical. -/
theorem symplectic_cover_radical_source
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
    (F : Type) [Field F] [Finite F] {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : D ⧸ center D ≃* ClassicalGroup.PSp 2 F) :
    D ⊓ (twoCore HU).subgroupOf H ≠ ⊥ ∧
    (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ∈ Chapter1.He G := by
  obtain ⟨S, z, h, hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hp hBH hHnorm hpair hsat
  obtain ⟨hi, hn, hcenter⟩ := symplectic_inner_projection_of_source_marking h D hD
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
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let j := e.trans EvenProjective.equiv.symm
  let f := j.toMonoidHom.comp (QuotientGroup.mk' (center D))
  have hf : Function.Surjective f := j.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center D := by
    rw [MonoidHom.ker_comp_of_injective _ _ j.injective,
      QuotientGroup.ker_mk']
  have himage : (((twoCore HU).subgroupOf H).subgroupOf D).map f ≠ ⊥ := by
    intro hb
    have hx : f ⟨d, hd.1⟩ = 1 := mem_bot.mp (hb ▸ mem_map_of_mem f hd.2)
    have hz : (⟨d, hd.1⟩ : D) ∈ center D := hker ▸ (MonoidHom.mem_ker.mpr hx)
    apply hnc
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)
  exact ⟨hne, symplectic_cover_radical_mem_He hpair hsat D hD F hk hF
    f hf (hker ▸ hZp) himage⟩

/-- The original source escaping branch for every marked nonbinary symplectic cover. -/
theorem symplectic_escaping_source
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
    (F : Type) [Field F] [Finite F] {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : D ⧸ center D ≃* ClassicalGroup.PSp 2 F)
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  obtain ⟨hne, hNe⟩ := symplectic_cover_radical_source hG T₀ hM hT₀M hunique hH
    B hp hBH hHnorm hpair hsat D hD F hk hF e
  exact component_join_preserves_stars_of_escaping_radical hH hpair hbig hsat S hUS D hD
    hne hNe hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
