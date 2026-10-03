module

public import Theory.Character.Multiplicity
public import Theory.Character.Integrality

/-!
# The averaging step in the Brauer--Tuan intersection argument

A character averaged over a subgroup is a natural number. Consequently a
linear combination of characters with algebraic-integer coefficients has an
integral average. If this combination vanishes at all nonidentity elements of
the subgroup, its degree divided by the subgroup order is an algebraic integer.

This is the last step of Brauer--Tuan Lemma 3, applied to a Sylow subgroup
after block orthogonality has established vanishing.
Source: Brauer--Tuan, *On simple groups of finite order I*, Bull. AMS 51
(1945), equation (2.1) and the proof of Lemma 3 on p.765.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace BrauerTuan
variable {G : Type*} [Group G] [Finite G]

/-- The average of an ordinary character restricted to a subgroup is its
principal multiplicity. -/
theorem character_subgroup_average_eq_nat
    {χ : ConjClassFunction G} (hχ : IsConjCharacter χ) (H : Subgroup G) :
    ∃ n : ℕ, (∑ x : H, χ (ConjClasses.mk (x : G))) / (Nat.card H : ℂ) = n := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  obtain ⟨m, hm⟩ := IsCharacter.scalarProduct_eq_nat
    (show IsCharacter (Representation.character (ρ.comp H.subtype)) from ⟨n, ρ.comp H.subtype, rfl⟩)
    (principal_isCharacter (G := H))
  refine ⟨m, ?_⟩
  change (∑ x : H, ρ.character (x : G)) / (Nat.card H : ℂ) = (m : ℂ)
  simpa [scalarProduct, div_eq_mul_inv, mul_comm, Representation.character,
    MonoidHom.comp_apply] using hm

/-- An algebraic-integer combination of characters supported at the identity
of a subgroup has degree divisible by that subgroup order in the algebraic integers. -/
theorem isIntegral_degree_sum_div_card_of_vanishing
    {I : Type*} (s : Finset I) (χ : I → ConjClassFunction G)
    (hχ : ∀ i ∈ s, IsConjCharacter (χ i)) (a : I → ℂ)
    (ha : ∀ i ∈ s, IsIntegral ℤ (a i)) (H : Subgroup G)
    (hvanish : ∀ x : H, x ≠ 1 → ∑ i ∈ s, a i * χ i (ConjClasses.mk (x : G)) = 0) :
    IsIntegral ℤ ((∑ i ∈ s, a i * χ i (ConjClasses.mk 1)) / (Nat.card H : ℂ)) := by
  classical
  have havg (i : I) (hi : i ∈ s) :
      IsIntegral ℤ ((∑ x : H, χ i (ConjClasses.mk (x : G))) / (Nat.card H : ℂ)) := by
    obtain ⟨n, hn⟩ := character_subgroup_average_eq_nat (hχ i hi) H
    have hz := isIntegral_natCast (R := ℤ) (B := ℂ) n
    rw [← hn] at hz
    convert hz using 1
    congr 1
    apply Finset.sum_congr
    · ext; simp
    · intro x hx; rfl
  have hsum : (∑ x : H, ∑ i ∈ s, a i * χ i (ConjClasses.mk (x : G))) =
      ∑ i ∈ s, a i * χ i (ConjClasses.mk 1) := by
    rw [Finset.sum_eq_single (1 : H)]
    · rfl
    · intro x _ hx
      exact hvanish x hx
    · simp
  rw [← hsum, Finset.sum_comm, Finset.sum_div]
  simp only [← Finset.mul_sum, mul_div_assoc]
  exact IsIntegral.sum _ (fun i hi => (ha i hi).mul (havg i hi))

end BrauerTuan
