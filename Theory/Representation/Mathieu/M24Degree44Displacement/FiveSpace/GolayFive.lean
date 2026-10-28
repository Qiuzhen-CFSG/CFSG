module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Exterior
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum

/-!
# Order-five fixed dimensions in the native Golay modules

The point-count identity for the cocode and the bound of four on fixed
points force its fixed dimension to be three. Cyclic code--cocode duality
gives the same dimension for the code. These are the original native
eleven-dimensional actions used in the exterior-square calculation.

Source: Aschbacher--Smith, H.13 and H.15.7; the application is
Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1, p.17.
-/

public section
namespace Representation.MathieuM24Degree44.FiveSpace
open Sporadic.Mathieu BinaryOffender

theorem cocode_five_fixed_finrank (x : M24) (hx : orderOf x = 5) :
    Module.finrank (ZMod 2) (fixedSpace MathieuCode.cocodeRepresentation
      (Subgroup.zpowers x)) = 3 := by
  have hc : Nat.card (Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hx]
  have hp := MathieuCode.m24_odd_prime_point_restriction (Subgroup.zpowers x)
    (by decide : Nat.Prime 5) (by decide : Odd 5) hc
  have he := MathieuCode.prime_cocode_fixed_point_equation (Subgroup.zpowers x)
    (by decide : Nat.Prime 5) (by decide : Odd 5) hc
  rcases hp with ⟨h, _⟩ | ⟨_, hp⟩ <;> omega

theorem code_five_fixed_finrank (x : M24) (hx : orderOf x = 5) :
    Module.finrank (ZMod 2) (fixedSpace MathieuCode.codeRepresentation
      (Subgroup.zpowers x)) = 3 :=
  (MathieuCode.code_cocode_fixed_finrank_cyclic (Subgroup.zpowers x)).trans
    (cocode_five_fixed_finrank x hx)

end Representation.MathieuM24Degree44.FiveSpace
