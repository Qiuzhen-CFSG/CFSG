module

public import Theory.AlgebraicGroup.Morphism.BijectiveCoordinatePowers
public import Theory.AlgebraicGroup.Morphism.BijectiveCoordinatePowers.Connected
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction

/-!
# Coordinate descent for incoming F4 isogenies

For an incoming F4 isogeny with connected source that is injective on points,
powers of every source coordinate descend to target polynomials. Connectedness
and point bijectivity supply a nonempty flat principal open, and group
translations extend flatness globally. The relative tensor product retains
the possible infinitesimal kernel; its coordinate differences are nilpotent,
and Frobenius kills them before faithfully flat descent.

This proves the coordinate descent step for GLS3, Theorem 1.12.5(b)
(`refs/KGroup/GLS3/Chapter1.tex`), with point injectivity as an explicit input.
The parent module supplies the reconstruction from the resulting equations.
-/

public section

open Theory.AlgebraicGroup

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The geometric descent conclusion from a supplied flat localization.
No separability or regular point inverse is assumed. -/
theorem f4_coordinate_powers_of_injective_isogeny_of_flat_localization
    {H : Variety F} [AlgebraicGroup H]
    (φ : Morphism H (F4Chevalley.Carrier (k := F)))
    (hφ : IsIsogeny φ) (hinj : Function.Injective φ.onPoints)
    (hlocal : ∃ c : Variety.PolynomialFunction (F4Chevalley.Carrier (k := F)), c ≠ 0 ∧
      RingHom.Flat (Localization.awayMap φ.toVariety.pullbackRingHom c)) :
    ∀ i : H.Coordinates, ∃ n : ℕ,
      ∃ q : MvPolynomial (F4Chevalley.Carrier (k := F)).Coordinates F,
        ∀ x : Variety.Point H,
          x.val i ^ (2 ^ n) = evalPolynomial (φ.onPoints x).val q := by
  exact φ.exists_coordinate_frobenius_powers_of_bijective_of_flat_localization
    ⟨hinj, hφ.1⟩ hlocal 2

/-- Coordinate powers descend through any incoming F4 isogeny with connected
source that is injective on points. This holds over any algebraically closed
field of characteristic two, including algebraic closures of finite fields. -/
theorem f4_coordinate_powers_of_injective_isogeny
    {H : Variety F} [AlgebraicGroup H]
    (φ : Morphism H (F4Chevalley.Carrier (k := F)))
    (hH : IsConnected (Set.univ : Set (Variety.Point H)))
    (hφ : IsIsogeny φ) (hinj : Function.Injective φ.onPoints) :
    ∀ i : H.Coordinates, ∃ n : ℕ,
      ∃ q : MvPolynomial (F4Chevalley.Carrier (k := F)).Coordinates F,
        ∀ x : Variety.Point H,
          x.val i ^ (2 ^ n) = evalPolynomial (φ.onPoints x).val q := by
  exact φ.exists_coordinate_two_powers_of_bijective_of_connected hH ⟨hinj, hφ.1⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
