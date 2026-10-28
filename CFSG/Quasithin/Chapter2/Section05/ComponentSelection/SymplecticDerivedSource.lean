module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticContainedSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticBinaryBorel
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.GroupTheory.PCoreProduct

/-!
# The complete original derived-symplectic Borel source family

For n=1 the actual derived carrier is identified with A6 and the Borel is
self-normalizing Sylow. For n≥2 the proved root-generation equivalence
identifies the derived and full matrix carriers. The original source
intersection is therefore the component Sylow normalizer at every field
size, and its actual two-core is that Sylow subgroup. This discharges the
contained-normalizer branch for the entire original Sp4(2^n)' family.

Source: Aschbacher--Smith 2.5.2(2), 2.5.3(4), printed pp.551--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The complete source symplectic family, with the derived carrier at every
field size. The original intersection is the full Sylow normalizer and its
actual embedded two-core is the component Sylow. -/
theorem derived_symplectic_borel_of_source_marking
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e₀ : D ≃* commutator (Sp F)) :
    ((M.subgroupOf H).subgroupOf D) = normalizer ((S : Subgroup H).subgroupOf D : Set D) ∧
      ((M.subgroupOf H).subgroupOf D).pCoreIn 2 = (S : Subgroup H).subgroupOf D := by
  obtain ⟨hout,_α,_P,_ha,_d,_hc⟩ := h.component_inputs D hD
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  by_cases hn1 : n = 1
  · have hc : Nat.card F = 2 := by simpa [hn1] using hF
    have hI := symplectic_binary_derived_intersection_eq_sylow_source hH hempty S
      h.mem_HeOver.2.2 D hD hout F hc e₀
    let e := e₀.trans (Binary.derivedEquivAlternatingSix hc)
    refine ⟨?_, ?_⟩
    · rw [hI, ← hR]
      exact (Binary.ComponentActionGeometry.normalizer_sylow e R).symm
    · rw [hI]
      exact pCoreIn_eq_self_of_isPGroup 2 _ (hR ▸ R.isPGroup')
  · have hn2 : 2 ≤ n := by omega
    let : CharP F 2 := EvenProjective.charTwo_of_card hF
    have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn2
    let e' := e₀.trans (derivedEquivFull_of_card_gt_two (by omega : 2 < Nat.card F))
    obtain ⟨e,hU,hB,_hs⟩ := exists_symplectic_borel_source hH hempty
      h.intersection_characteristicTwo S h.mem_HeOver.2.2 D hD hout F hn2 hF e'
    have hpre : unipotent.comap e.toMonoidHom = (S : Subgroup H).subgroupOf D := by
      rw [← hU, Subgroup.comap_map_eq_self_of_injective e.injective]
    refine ⟨?_, ?_⟩
    · rw [hB, borel_eq_normalizer_unipotent,
        comap_normalizer_eq_of_surjective _ e.surjective, hpre]
    · apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_pCoreIn_of_injective 2 _ e.toMonoidHom e.injective, hB,
        map_comap_eq_self_of_surjective e.surjective, EvenBorelTorus.borel_twoCoreIn hF, hU]

/-- The full source contained-normalizer implication for the original
Sp4(2^n)' family, including its literal field-two endpoint. -/
theorem derived_symplectic_contained_original_source_sylow
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
    (F : Type*) [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : D ≃* commutator (Sp F))
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = D ⊓ (twoCore HU).subgroupOf H := by
  obtain ⟨S,z,h,_hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique hH
    B hp hBH hHnorm hpair hsat
  obtain ⟨_hB,hcore⟩ := derived_symplectic_borel_of_source_marking hH hempty h D hD F hk hF e
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  have hRQ : (R : Subgroup D) ≤ ((twoCore HU).subgroupOf H).subgroupOf D := by
    rw [hR, ← hcore]
    exact intersection_core_le_saturated_component_of_normalizer_le hpair hsat D hD hinside
  have heq : ((twoCore HU).subgroupOf H).subgroupOf D = (R : Subgroup D) :=
    R.is_maximal' (isPGroup_pCoreIn 2 HU).comap_subtype.comap_subtype hRQ
  refine ⟨R, ?_⟩
  rw [← heq, subgroupOf_map_subtype, inf_comm]
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
