module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.AlgebraicGroup.Morphism.FrobeniusPowerDescent

/-!
# Frobenius descent for incoming F4 isogenies

Coordinate Frobenius on the literal algebraic F4 carrier is a bijective point
endomorphism. If powers of the coordinates of a surjective source descend to
this carrier, taking roots of their polynomial coefficients constructs an
algebraic isogeny in the opposite direction. Its composite with the incoming
map is a power of coordinate Frobenius.

This establishes the reconstruction step needed for GLS3, Theorem 1.12.5(b)
(`refs/KGroup/GLS3/Chapter1.tex`). Deriving coordinate descent from the
fundamental-coroot torus isomorphism still requires triviality of the incoming
point kernel and the geometric purely inseparable descent theorem. Neither
premise is asserted by the construction below.
-/

public section

open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- Polynomial descent of powers of source coordinates constructs a reverse
isogeny on the actual F4 carrier, including inseparable incoming maps. -/
theorem f4_reverse_isogeny_of_coordinate_powers
    {H : Variety F} [AlgebraicGroup H]
    (φ : Morphism H (F4Chevalley.Carrier (k := F)))
    (hsurj : Function.Surjective φ.onPoints)
    (hpow : ∀ i : H.Coordinates, ∃ n : ℕ,
      ∃ q : MvPolynomial (F4Chevalley.Carrier (k := F)).Coordinates F,
        ∀ x : Variety.Point H,
          x.val i ^ (2 ^ n) = evalPolynomial (φ.onPoints x).val q) :
    ∃ ψ : Morphism (F4Chevalley.Carrier (k := F)) H,
      IsIsogeny ψ ∧ ∃ n : ℕ, (φ.comp ψ).onPoints = frobeniusEnd ^ n := by
  obtain ⟨n, hn⟩ := φ.toVariety.exists_uniform_coordinate_frobenius_power 2 hpow
  have hbij : Function.Bijective (frobeniusEnd (F := F) ^ n) := by
    clear hn
    induction n with
    | zero => exact Function.bijective_id
    | succ n ih =>
      rw [pow_succ']
      exact frobeniusEnd_bijective.comp ih
  obtain ⟨ψ, hψ, hcomp⟩ :=
    φ.exists_reverse_isogeny_of_coordinate_frobenius_powers 2 n hsurj
      (frobeniusEnd ^ n) hbij (frobeniusEnd_pow_coordinate n) hn
  exact ⟨ψ, hψ, n, hcomp⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
