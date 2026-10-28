module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearPrimeLocals
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RadicalEscape

/-!
# The original prime-linear escaping-normalizer branch

The genuine source marking supplies innerness, a nontrivial component
radical, and characteristic two of its full normalizer. Saturation supplies
the exact core and local orbit invariance. Therefore a normalizer escaping
M selects the component adjoined to the original Sylow, preserving Gamma0
and both starred conditions without additional model-action or local inputs.

Source: Aschbacher--Smith 2.5.3(4), printed p.553, case 2.5.2(4).
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- All source inputs to the prime-linear escaping-normalizer branch are constructed. -/
theorem linear_prime_escaping_source
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
    (p : ℕ) [Fact p.Prime] (hlarge : 7 < p) (e : D ≃* PSL(2, ZMod p))
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  have hne := linear_prime_component_intersection_ne_bot hG T₀ hM hT₀M hunique hH
    B hp hBH hHnorm hpair hsat D hD p hlarge e
  obtain ⟨S', z, h, _hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hp hBH hHnorm hpair hsat
  let Q := (twoCore HU).subgroupOf H
  let R := D ⊓ Q
  let N := D ⊓ normalizer (R : Set H)
  have hRD : R ≤ D := inf_le_left
  have hRp : IsPGroup 2 R := (isPGroup_pCoreIn 2 HU).comap_subtype.to_le inf_le_right
  have hneD : R.subgroupOf D ≠ ⊥ := by
    intro hb
    apply hne
    change R = ⊥
    rw [← map_subgroupOf_eq_of_le hRD, hb, Subgroup.map_bot]
  have hnormmap : (normalizer (R.subgroupOf D : Set D)).map D.subtype = N := by
    rw [← subgroupOf_normalizer_eq hRD, subgroupOf_map_subtype, inf_comm]
  have hNe : N.map H.subtype ∈ Chapter1.He G := by
    have hc := linear_prime_normalizer_mem_He_of_source_marking h D hD p hlarge e
      (R.subgroupOf D) hRp.comap_subtype hneD
    rwa [hnormmap] at hc
  exact component_join_preserves_stars_of_escaping_radical hH hpair hbig hsat S hUS D hD
    hne hNe hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
