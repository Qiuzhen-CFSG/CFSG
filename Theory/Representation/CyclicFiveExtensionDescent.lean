module

public import Theory.Representation.SemilinearDeterminant
public import Theory.Character.Integrality
public import Theory.FieldTheory.RationalDescent
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic

/-!
# Rational descent of normalized cyclic-five extensions

A quartic representation extending a rational-valued character has rational
character values if its character is unique among extensions with the same
restriction and determinant one on the complement. Coordinate semilinear
conjugation preserves both conditions. Uniqueness therefore fixes the character
under every field automorphism of `ℂ`; integrality of finite-group character
values and rational descent give rationality.

Character uniqueness is an explicit premise, independent of the construction
and rigidity of the extension. This is the descent step in Lyons,
*A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section

noncomputable section
namespace Representation

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A normalized quartic extension with a unique character descends to rational values. -/
theorem cyclicFive_character_rational_of_normalized_unique {K : Type*} [Group K] [Finite K]
    (α : Multiplicative (ZMod 5) →* MulAut K)
    (σ : Representation ℂ (K ⋊[α] Multiplicative (ZMod 5)) (Fin 4 → ℂ))
    (hrat : ∀ k, ∃ q : ℚ, character (σ.comp SemidirectProduct.inl) k = (q : ℂ))
    (hdet : ∀ t, LinearMap.det (σ (SemidirectProduct.inr t)) = 1)
    (huniq : ∀ τ : Representation ℂ (K ⋊[α] Multiplicative (ZMod 5)) (Fin 4 → ℂ),
      character (τ.comp SemidirectProduct.inl) = character (σ.comp SemidirectProduct.inl) →
      (∀ t, LinearMap.det (τ (SemidirectProduct.inr t)) = 1) → τ.character = σ.character) :
    ∀ x, ∃ q : ℚ, σ.character x = (q : ℂ) := by
  classical
  let : Finite (K ⋊[α] Multiplicative (ZMod 5)) :=
    Finite.of_equiv (K × Multiplicative (ZMod 5)) SemidirectProduct.equivProd.symm
  let : Fintype (K ⋊[α] Multiplicative (ZMod 5)) := Fintype.ofFinite _
  intro x
  apply Complex.exists_ratCast_of_isAlgebraic_of_fixed
  · exact (IsIntegral.tower_top (A := ℚ) (character_value_isIntegral σ x)).isAlgebraic
  · intro φ
    let τ := semilinearConjugate φ σ (coordinateSemilinearEquiv φ (Fin 4))
    have hchar : ∀ y, τ.character y = φ (σ.character y) :=
      character_semilinearConjugate φ σ _
    have hres : character (τ.comp SemidirectProduct.inl) =
        character (σ.comp SemidirectProduct.inl) := by
      funext k
      change τ.character (SemidirectProduct.inl k) = σ.character (SemidirectProduct.inl k)
      obtain ⟨q, hq⟩ := hrat k
      change σ.character (SemidirectProduct.inl k) = (q : ℂ) at hq
      rw [hchar, hq, map_ratCast]
    have hnorm : ∀ t, LinearMap.det (τ (SemidirectProduct.inr t)) = 1 := by
      intro t
      change LinearMap.det (semilinearConjugate φ σ
        (coordinateSemilinearEquiv φ (Fin 4)) (SemidirectProduct.inr t)) = 1
      rw [det_coordinateSemilinearConjugate, hdet, map_one]
    exact (hchar x).symm.trans (congrFun (huniq τ hres hnorm) x)

end Representation
