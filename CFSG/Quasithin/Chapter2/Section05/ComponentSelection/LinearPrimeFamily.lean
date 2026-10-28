module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentFamilySource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearPrimeSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearPrimeEscape

/-!
# Removing the prime-linear component family

For all large Fermat/Mersenne prime PSL2 components with contained radical
normalizers, the actual source gives Sylow intersections. Their product is
characteristic by model invariance. The generic selected-family normalizer
therefore removes the entire family, retaining the normalizer presentation,
original Sylow and both stars. No individual component normality is assumed.

Source: Aschbacher--Smith 2.5.3(4), printed p.553, case 2.5.2(4).
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The large Fermat/Mersenne prime linear family occurring in source 2.5.2(4). -/
@[expose] def IsLargePrimeLinear (L : Type*) [Group L] : Prop :=
  ∃ p : ℕ, IsFermatOrMersennePrime p ∧ 7 < p ∧ Nonempty (L ≃* PSL(2, ZMod p))

/-- Model membership is preserved by the literal component isomorphism. -/
theorem IsLargePrimeLinear.of_mulEquiv {L L' : Type*} [Group L] [Group L']
    (h : IsLargePrimeLinear L) (e : L' ≃* L) : IsLargePrimeLinear L' := by
  obtain ⟨p, hp, hb, ⟨f⟩⟩ := h
  exact ⟨p, hp, hb, ⟨e.trans f⟩⟩

/-- All contained prime-linear components can be removed simultaneously. -/
theorem exists_linear_prime_family_replacement
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
    (hQS : (twoCore HU).subgroupOf H ≤ (S : Subgroup H))
    (hinside : ∀ D : Subgroup H, IsComponent H D → IsLargePrimeLinear D →
      (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
        H.subtype ≤ M) :
    ∃ (X : Subgroup G) (B' : Fin (n + 1) → Subgroup G),
      X ≤ H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      HU ≤ X ∧ (S : Subgroup H).map H.subtype ≤ X ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K →
        IsComponentIn (K.map X.subtype) H ∧
          ¬ IsLargePrimeLinear K := by
  let F : Set (Subgroup H) := {D | IsComponent H D ∧ IsLargePrimeLinear D}
  let E : Subgroup H := sSup F
  let : E.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro e
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro D hd
    exact map_le_iff_le_comap.mp (le_sSup
      ⟨hd.1.map_equiv e, hd.2.of_mulEquiv (e.subgroupMap D).symm⟩)
  have hcomp : ∀ D ∈ F, ∃ P : Sylow 2 D,
      (P : Subgroup D).map D.subtype ≤ (twoCore HU).subgroupOf H := by
    intro D hd
    obtain ⟨p, hp', hb, ⟨e⟩⟩ := hd.2
    let : Fact p.Prime := ⟨hp'.1⟩
    obtain ⟨P, hP⟩ := linear_prime_contained_source_sylow hG T₀ hM hT₀M hunique hH
      B hp hBH hHnorm hpair hsat D hd.1 p hp' hb e (hinside D hd.1 hd.2)
    exact ⟨P, hP.le.trans inf_le_right⟩
  obtain ⟨X, B', hXH, hX, hstar, hmax, hHUX, hSX, hp', hBX, hXnorm, hremain⟩ :=
    exists_component_family_source_replacement hH B hp hBH hHnorm hpair hbig hsat
      S hUS hQS F (fun _ h => h.1) hcomp
  refine ⟨X, B', hXH, hX, hstar, hmax, hHUX, hSX, hp', hBX, hXnorm, ?_⟩
  intro K hK
  obtain ⟨hKH, hKF⟩ := hremain K hK
  refine ⟨hKH, ?_⟩
  intro hmodel
  let D := (K.map X.subtype).subgroupOf H
  have hmap : D.map H.subtype = K.map X.subtype := map_subgroupOf_eq_of_le hKH.1
  let e : K ≃* D := (K.equivMapOfInjective X.subtype X.subtype_injective).trans
    (subgroupOfEquivOfLe hKH.1).symm
  exact hKF D ⟨hKH.2, hmodel.of_mulEquiv e.symm⟩ hmap.symm

/-- With no normalizer-placement assumption, either a prime-linear component
already supplies the required join or the source replacement excludes that
whole family. This is the complete large-prime branch of source 2.5.3(4). -/
theorem linear_prime_source_alternative
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
    (hQS : (twoCore HU).subgroupOf H ≤ (S : Subgroup H))
    :
    (∃ D : Subgroup H, IsComponent H D ∧ IsLargePrimeLinear D ∧
      let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
      X ∈ gammaZero (Chapter1.He G) M ∧
        (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
        (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M)) ∨
    (∃ (X : Subgroup G) (B' : Fin (n + 1) → Subgroup G),
      X ≤ H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      HU ≤ X ∧ (S : Subgroup H).map H.subtype ≤ X ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K →
        IsComponentIn (K.map X.subtype) H ∧
          ¬ IsLargePrimeLinear K) := by
  classical
  by_cases hinside : ∀ D : Subgroup H, IsComponent H D → IsLargePrimeLinear D →
      (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
        H.subtype ≤ M
  · exact Or.inr (exists_linear_prime_family_replacement hG T₀ hM hT₀M hunique hH
      B hp hBH hHnorm hpair hbig hsat S hUS hQS hinside)
  · push Not at hinside
    obtain ⟨D, hD, hm, hout⟩ := hinside
    have hmodel := hm
    obtain ⟨p, hp', hb, ⟨e⟩⟩ := hm
    let : Fact p.Prime := ⟨hp'.1⟩
    exact Or.inl ⟨D, hD, hmodel, linear_prime_escaping_source hG T₀ hM hT₀M hunique hH
      B hp hBH hHnorm hpair hbig hsat S hUS D hD p hb e hout⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
