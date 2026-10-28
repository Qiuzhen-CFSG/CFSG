module

public import Theory.Representation.QuadraticSemilinear
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner

/-!
# Quadratic outer actors at arbitrary nonbinary degrees

A quadratic subgroup outside a centric normal symplectic component injects
into the automorphism group of its coefficient field. A field-linear
quadratic element fixes a field line and lies in the component; an outer
actor therefore has a nontrivial twist, making all twist assignments distinct.

This is the degree-independent bound used before MS93 (3.4), p.868.
-/
public section

open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient
open SymplecticConjugatePair.Ambient.Normalizer

namespace SymplecticNaturalNormalizer
variable {F G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G]

theorem quadratic_card_le_ringAut_of_not_le_component
    (hF : 2 < Nat.card F) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (e : B ≃* Sp F) (ρ : Representation (ZMod 2) G (Vector F))
    (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (A : Subgroup G) (hq : IsQuadratic ρ A) (hAB : ¬ A ≤ B) : Nat.card A ≤ Nat.card (F ≃+* F) := by
  have hcard : 2 < Nat.card F := by omega
  have hsemi (a : G) : ∃ σ : F ≃+* F, ∀ (c : F) w, ρ a (c • w) = σ c • ρ a w :=
    exists_field_twist ⟨linearAction ρ a,operator_mem_naturalNormalizer B hcard e ρ hB a⟩
  obtain ⟨a,ha,haB⟩ := SetLike.not_le_iff_exists.mp hAB
  obtain ⟨σ,hσ⟩ := hsemi a
  have hn : σ ≠ RingEquiv.refl F := by
    intro he
    have hane : a ≠ 1 := fun hh => haB (hh ▸ B.one_mem)
    obtain ⟨w,hw⟩ : ∃ w, ρ a w ≠ w := by
      by_contra! h
      apply hane
      apply hfaith
      rw [map_one]
      apply LinearMap.ext
      intro w
      exact h w
    let v := ρ a w - w
    have hv : v ≠ 0 := sub_ne_zero.mpr hw
    have hfix (c : F) : ρ a (c • v) = c • v := by
      rw [hσ,he]
      exact congrArg (c • ·) (hq a ha a ha w)
    exact haB (mem_component_of_fixes_field_line B hcent hcard e ρ hB a v hv hfix)
  exact quadratic_card_le_ringAut_of_nontrivial_twist ρ A hq hfaith
    (fun a _ => hsemi a) ha hn hσ

theorem le_component_of_quadratic_ringAut_card_lt
    (hF : 2 < Nat.card F) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (e : B ≃* Sp F) (ρ : Representation (ZMod 2) G (Vector F))
    (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (A : Subgroup G) (hq : IsQuadratic ρ A) (hlarge : Nat.card (F ≃+* F) < Nat.card A) : A ≤ B := by
  by_contra hAB
  exact (not_le_of_gt hlarge)
    (quadratic_card_le_ringAut_of_not_le_component hF B hcent e ρ hfaith hB A hq hAB)

end SymplecticNaturalNormalizer
