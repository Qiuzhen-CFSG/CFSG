module

public import Theory.Character.GaloisAction
public import Theory.Character.SimpleCriteria
public import Theory.Representation.CoefficientReduction

/-!
# Coprime power action on irreducible characters

If `e` is coprime to the order of a finite group, substituting `g ^ e` for `g`
preserves irreducible complex characters. Realize the substitution by a
cyclotomic Galois automorphism, apply that automorphism to representation
matrices, and use the character norm criterion. The norm is unchanged because
the power map permutes the group.

This is the argument of Peterfalvi (5.9), using the Galois action from (1.9),
as needed in Suzuki VI §2.2, Example 3.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

/-- A coprime power map permutes a finite group. -/
public theorem pow_bijective_of_coprime_natCard
    {G : Type*} [Group G] [Finite G] {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    Function.Bijective (fun g : G => g ^ e) :=
  he.symm.pow_left_bijective

/-- Every element of a finite group is a coprime power. -/
public theorem pow_surjective_of_coprime_natCard
    {G : Type*} [Group G] [Finite G] {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    Function.Surjective (fun g : G => g ^ e) :=
  (pow_bijective_of_coprime_natCard he).surjective

/-- Coprime power substitution preserves the scalar product of functions. -/
public theorem scalarProduct_argumentPow_eq_of_coprime_natCard
    {G : Type*} [Group G] [Finite G]
    {φ ψ : ClassFunction G} {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    scalarProduct G (fun g : G => φ (g ^ e)) (fun g : G => ψ (g ^ e)) =
      scalarProduct G φ ψ := by
  classical
  let pe : G ≃ G :=
    Equiv.ofBijective (fun g : G => g ^ e) (pow_bijective_of_coprime_natCard he)
  have hsum :
      ∑ g : G, φ (g ^ e) * star (ψ (g ^ e)) =
        ∑ g : G, φ g * star (ψ g) := by
    simpa [pe] using (Equiv.sum_comp pe (fun g : G => φ g * star (ψ g)))
  unfold scalarProduct
  rw [hsum]

/-- An irreducible complex character stays irreducible under a coprime power
substitution in its argument. -/
public theorem IsIrreducibleCharacter.argumentPow
    {G : Type*} [Group G] [Finite G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    {e : ℕ} (he : e.Coprime (Nat.card G)) :
    IsIrreducibleCharacter (fun g : G => χ (g ^ e)) := by
  classical
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  obtain ⟨τ, hτ⟩ := Section1.complex_galois_aut_pow_on_roots he
  let ρτ := Representation.mapCoefficients τ.toRingEquiv.toRingHom ρ
  have hchar (g : G) : ρτ.character g = ρ.character (g ^ e) := by
    calc
      ρτ.character g = τ (ρ.character g) :=
        Representation.mapCoefficients_trace τ.toRingEquiv.toRingHom ρ g
      _ = ρ.character (g ^ e) :=
        Section1.representation_character_apply_galois_eq_argumentPow hτ ρ dvd_rfl g
  refine ⟨n, ρτ, ?_, (funext hchar).symm⟩
  apply (irreducible_iff_character_norm_one ρτ).2
  have hnorm := (irreducible_iff_character_norm_one ρ).1 hρ
  change scalarProduct G ρτ.character ρτ.character = 1
  change scalarProduct G ρ.character ρ.character = 1 at hnorm
  rw [funext hchar, scalarProduct_argumentPow_eq_of_coprime_natCard he]
  exact hnorm
