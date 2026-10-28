module

public import Theory.AlgebraicGroup.Morphism.BijectiveCoordinatePowers.FlatOpen

/-!
# Coordinate powers for bijective morphisms with connected source

Over an algebraically closed field of characteristic two, every source
coordinate of a bijective algebraic-group morphism has a power `2 ^ n`
that is the pullback of a target polynomial. The exponent may depend on the
coordinate.

Connectedness and point bijectivity give a nonempty flat principal open.
Group translations extend this flatness globally, and point surjectivity
makes it faithful. Point injectivity makes the coordinate differences in
the relative tensor product nilpotent; taking powers of two kills these
differences, allowing faithfully flat descent.

This is the purely inseparable descent step used for isogenies in GLS3,
Chapter 1, Sections 1.10--1.12 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

/-- Powers of two of source coordinates descend through a bijective group
morphism with connected source. -/
public theorem Morphism.exists_coordinate_two_powers_of_bijective_of_connected
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hH : IsConnected (Set.univ : Set (Variety.Point H)))
    (hbij : Function.Bijective φ.onPoints) :
    ∀ i : H.Coordinates, ∃ n : ℕ, ∃ q : MvPolynomial G.Coordinates k,
      ∀ x : Variety.Point H,
        x.val i ^ (2 ^ n) = evalPolynomial (φ.onPoints x).val q := by
  exact φ.exists_coordinate_frobenius_powers_of_bijective_of_flat_localization hbij
    (φ.exists_flat_localization_of_bijective_of_connected hH hbij) 2

end Theory.AlgebraicGroup
