module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearEvenLocals
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RadicalEscape
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Inner

/-!
# The binary PSL3 escaping branch on original source hypotheses

The actual marked Sylow fixer is inner. Its odd-core inversion identifies
the component center with its two-core. Component projection saturation
then gives a noncentral element in the component radical, hence nontrivial
image in PSL3. The two-kernel local theorem applies to the actual normalizer,
including central two-covers. The escaping branch consequently preserves
Gamma0 and both stars without innerness, nontriviality or local He inputs.

Source: Aschbacher--Smith 2.5.2(2), 2.5.3(4), printed pp.551--553.
The contained branch's Borel-intersection identification remains separate.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Chapter1.QuasisimpleInvolutions
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The genuine source marking supplies inner noncentral projection and the
full two-primary center, including the exceptional binary central cover. -/
theorem linear_even_inner_projection_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : D ⧸ center D ≃* PSL(3,F)) :
    (⟨z, h.mem_intersection.1⟩ : H) ∈ D ⊔ centralizer (D : Set H) ∧
      (⟨z, h.mem_intersection.1⟩ : H) ∉ centralizer (D : Set H) ∧
      center D = pCore 2 D := by
  let : IsQuasisimple D := hD.2
  obtain ⟨_hout, α, P, ha, d, _hc⟩ := h.component_inputs D hD
  have hi := d.linearThree_inner hn ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
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
theorem linear_even_cover_radical_source
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
  exact ⟨hne, linear_even_cover_radical_mem_He hpair hsat D hD F hk hF
    f hf (hker ▸ hZp) himage⟩

/-- The original source escaping branch for every marked binary PSL3 cover. -/
theorem linear_even_escaping_source
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
    (e : D ⧸ center D ≃* PSL(3,F))
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  obtain ⟨hne, hNe⟩ := linear_even_cover_radical_source hG T₀ hM hT₀M hunique hH
    B hp hBH hHnorm hpair hsat D hD F hk hF e
  exact component_join_preserves_stars_of_escaping_radical hH hpair hbig hsat S hUS D hD
    hne hNe hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
