module

public import ABG.ChapterII.Section1.ExtremalNormalizerControl
public import Theory.PGroupCore

/-!
# Extending an extremal normalizer action to its p-core

If X is extremal in a Sylow subgroup P, the ambient image R of
Oₚ(N_G(X)) contains X and lies in P. Every element normalizing X normalizes
R. Moreover, centricity passes from X to R. These facts permit extending
normalizer steps before applying the centric subgroup classification.

The Sylow containment uses the actual Sylow subgroup of N_G(X) provided by
extremality. No assertion that X is radical, or that R is extremal, is made.
This is the normal-core extension used with the Alperin fusion argument in
ABG Chapter II §1 and the order-64 case of Stellmacher (8.6)(a).
-/

namespace ABG

open BenderSuzuki.External

/-- A subgroup normalized by the whole chosen Sylow is extremal there. -/
public theorem extremal_of_sylow_le_normalizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (X : Subgroup G) (hXP : X ≤ (P : Subgroup G))
    (hPN : (P : Subgroup G) ≤ Subgroup.normalizer (X : Set G)) :
    HuppertExtremal P X := by
  refine ⟨hXP, ?_⟩
  rw [inf_eq_left.mpr hPN]
  have hP : (Nat.card (P : Subgroup G)).factorization p =
      (Nat.card G).factorization p := by
    rw [P.card_eq_multiplicity, Nat.factorization_pow_self Fact.out]
  apply le_antisymm
  · exact Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hPN) Nat.card_pos.ne' Nat.card_pos.ne'
  · rw [hP]
    exact Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_subgroup_dvd_card _) Nat.card_pos.ne' Nat.card_pos.ne'

/-- The p-core of the normalizer, viewed as an ambient subgroup. -/
@[expose] public def normalizerPCore
    {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) : Subgroup G :=
  (pCore p (Subgroup.normalizer (X : Set G))).map
    (Subgroup.normalizer (X : Set G)).subtype

/-- Normalizer actions extend to the normalizer's p-core. -/
public theorem normalizer_le_normalizerPCore_normalizer
    {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (normalizerPCore p X : Set G) := by
  have h := (pCore p (Subgroup.normalizer (X : Set G))).le_normalizer_map
    (Subgroup.normalizer (X : Set G)).subtype
  simpa only [normalizerPCore, Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] using h

/-- A p-subgroup is contained in the p-core of its normalizer. -/
public theorem le_normalizerPCore
    {G : Type*} [Group G] (p : ℕ) (X : Subgroup G)
    (hX : IsPGroup p X) : X ≤ normalizerPCore p X := by
  let N := Subgroup.normalizer (X : Set G)
  have hXN : X ≤ N := Subgroup.le_normalizer
  have hcore : X.subgroupOf N ≤ pCore p N :=
    le_sSup ⟨inferInstance, hX.comap_subtype⟩
  calc
    X = (X.subgroupOf N).map N.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hXN).symm
    _ ≤ normalizerPCore p X := Subgroup.map_mono (f := N.subtype) hcore

/-- Extremality places the whole normalizer p-core in the chosen Sylow. -/
public theorem normalizerPCore_le_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (X : Subgroup G) (hX : HuppertExtremal P X) :
    normalizerPCore p X ≤ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hX.exists_sylow_normalizer
  have hle := Subgroup.map_mono
    (pCore_isPGroup.le_sylow_of_normal Q)
    (f := (Subgroup.normalizer (X : Set G)).subtype)
  rw [hQ] at hle
  exact hle.trans inf_le_left

/-- The normalizer p-core of an extremal centric subgroup is again centric
in the same Sylow subgroup. -/
public theorem normalizerPCore_centric
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (X : Subgroup G) (hX : HuppertExtremal P X)
    (hc : subgroupCentralizerIn (P : Subgroup G) X ≤ X) :
    subgroupCentralizerIn (P : Subgroup G) (normalizerPCore p X) ≤
      normalizerPCore p X := by
  have hXR := le_normalizerPCore p X (IsPGroup.to_le P.isPGroup' hX.1)
  intro z hz
  apply hXR
  apply hc
  exact ⟨hz.1, fun x hx => hz.2 x (hXR hx)⟩

/-- Any relation controlled on the normalizer p-core is controlled on X.
The relation can, for example, compare membership in a normal transfer
subgroup of the Sylow group. -/
public theorem normalizer_relation_of_normalizerPCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (X : Subgroup G) (hX : HuppertExtremal P X)
    (r : P → P → Prop)
    (hR : ∀ g : G, g ∈ Subgroup.normalizer (normalizerPCore p X : Set G) →
      ∀ x y : P, (x : G) ∈ normalizerPCore p X →
        g⁻¹ * (x : G) * g = (y : G) → r x y)
    (g : G) (hg : g ∈ Subgroup.normalizer (X : Set G))
    (x y : P) (hx : (x : G) ∈ X)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) : r x y :=
  hR g (normalizer_le_normalizerPCore_normalizer p X hg) x y
    (le_normalizerPCore p X (IsPGroup.to_le P.isPGroup' hX.1) hx) hxy

end ABG
