module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlignedPairs
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderFamilySource

/-!
# Removing the Bender family while retaining the prescribed source Sylow

The maximal saturated pair is conjugated inside the actual intersection
H intersect M. The selected-family normalizer thus preserves the prescribed
Sylow, not merely the existence of some Sylow in the replacement. Every
replacement component remains an original non-Bender component.

Source: Aschbacher--Smith 2.5.3(4), printed p.552, first reduction.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

/-- The first source reduction preserves the particular original Sylow. -/
theorem exists_bender_free_source_replacement_prescribed_sylow
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M) :
    ∃ (X : Subgroup G) (B' : Fin (n + 1) → Subgroup G),
      X ≤ H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      (S : Subgroup H).map H.subtype ≤ X ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K →
        IsComponentIn (K.map X.subtype) H ∧ ¬ ClassificationModels.IsBenderModel K := by
  obtain ⟨U, HU, hpair, hUS, hQS, hbig, hsat⟩ := exists_saturated_pair_aligned hH S hSM
  have hQSi : (twoCore HU).subgroupOf H ≤ (S : Subgroup H) := by
    intro x hx
    obtain ⟨s, hs, he⟩ := hQS hx
    exact (Subtype.ext he : s = x) ▸ hs
  obtain ⟨X, B', hXH, hX, hstar, hmax, _hHU, hSX, hp', hBX, hXnorm, hcomp⟩ :=
    exists_bender_family_replacement hG T₀ hM hT₀M hunique hH B hp hBH hHnorm
      hpair hbig hsat S hUS hQSi
  exact ⟨X, B', hXH, hX, hstar, hmax, hSX, hp', hBX, hXnorm, hcomp⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
