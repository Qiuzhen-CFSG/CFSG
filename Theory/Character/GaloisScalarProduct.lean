module

public import Theory.Character.GaloisConjugation
public import Theory.Character.Induction
public import Theory.Representation.Induction

/-!
# Galois transport of character scalar products and induction

Field automorphisms commute with induction, whose formula uses only rational
coefficients. They also transport scalar products against irreducible characters:
complex conjugation of a finite-group character is evaluation at the inverse,
so no continuity or conjugation-preservation assumption on the automorphism is
needed. These identities allow rational generalized characters to distinguish
Galois-fixed irreducible constituents.

Source: ordinary character orthogonality and the induction formula; the Galois
argument is used in ABG III.2 Corollary 2.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Transport a scalar product by an arbitrary field automorphism of `ℂ`. -/
theorem IsIrreducibleCharacter.scalarProduct_comp_ringEquiv
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (σ : ℂ ≃+* ℂ) (f : ClassFunction G) :
    scalarProduct G (fun g => σ (f g)) (fun g => σ (χ g)) =
      σ (scalarProduct G f χ) := by
  have hinv {ψ : ClassFunction G} (hψ : IsIrreducibleCharacter ψ) (g : G) :
      star (ψ g) = ψ g⁻¹ := by
    obtain ⟨n, ρ, _, rfl⟩ := hψ
    exact (Representation.representation_character_inv_eq_star_character ρ g).symm
  simp only [scalarProduct, hinv hχ, hinv (hχ.comp_ringEquiv σ),
    map_mul, map_inv₀, map_natCast, map_sum]

/-- Field automorphisms commute with induction of class functions. -/
theorem ringEquiv_inducedClassFunction (σ : ℂ ≃+* ℂ) (H : Subgroup G) (f : ClassFunction H) (g : G) :
    σ (inducedClassFunction H f g) =
      inducedClassFunction H (fun h => σ (f h)) g := by
  classical
  simp only [inducedClassFunction, map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp
