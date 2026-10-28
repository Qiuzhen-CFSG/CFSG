module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearEvenBorel

/-!
# Discharging the binary PSL3 contained-normalizer branch

The original source marking makes the actual central quotient map have a
two-group kernel. The proved empty-Gamma-even Borel theorem identifies the
intersection after Sylow alignment. The contained-normalizer reduction now
makes D intersect O2(H_U) Sylow without a Borel, diagram or local-action
premise. It includes the field-two endpoint and all binary central covers.

Source: Aschbacher--Smith 2.5.2(2) and 2.5.3(4), printed pp.551--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The literal source contained branch has no remaining Borel input. -/
theorem linear_even_contained_original_source_sylow
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
    (F : Type) [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : D ⧸ center D ≃* PSL(3,F))
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = D ⊓ (twoCore HU).subgroupOf H := by
  obtain ⟨S,z,h,_hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique hH
    B hp hBH hHnorm hpair hsat
  obtain ⟨hout, _α, _P, _ha, _d, _hc⟩ := h.component_inputs D hD
  obtain ⟨_hi,_hn,hcenter⟩ := linear_even_inner_projection_of_source_marking h D hD F hk hF e
  let f₀ := e.toMonoidHom.comp (QuotientGroup.mk' (center D))
  have hf₀ : Function.Surjective f₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f₀.ker = center D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkp : IsPGroup 2 f₀.ker := hker ▸ hcenter ▸ pCore_isPGroup
  obtain ⟨f,hf,hkf,_hU,hB,_hinterchange⟩ := exists_linear_even_borel_source hH hempty
    S h.mem_HeOver.2.2 D hD hout F (by omega) hF f₀ hf₀ hkp
  have hBmap : (((M.subgroupOf H).subgroupOf D).map f) = Matrix.PSL3.LinearThree.borel F := by
    rw [hB,map_comap_eq_self_of_surjective hf]
  exact linear_even_cover_contained_source_sylow hpair hsat D hD F (by omega) hF f hf
    (hkf ▸ hkp) hBmap hinside

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
