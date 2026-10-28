module

public import Theory.Representation.Mathieu.M24Degree44Displacement
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Sections
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.GolayFive

/-!
# Degree-44 fixed spaces from Golay exterior-square sections

The two genuine mathematical premises are universal placement of arbitrary
binary degree-44 irreducibles in the native Golay exterior squares, and the
order-five calculation on those exterior squares. Odd-order exactness and
binary divisibility then prove the requested bound and connect it to the
native involution-displacement consumer.

This conditional assembly does not assert either missing premise or export
the unconditional `fiveFixedSpaceBound`.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17.
-/

public section
namespace Representation.MathieuM24Degree44
open Sporadic.Mathieu BinaryOffender FiveSpace
universe v

/-- The two independent exterior-square calculations discharge the exact native contract. -/
theorem fiveFixedSpaceBound_of_golay_exterior
    (hplacement : GolayExteriorPlacement.{v}) (hexterior : GolayExteriorFiveBound) :
    FiveFixedSpaceBound.{v} := by
  intro V _ _ _ ρ hf hi hd x hx
  obtain ⟨hc, hcc⟩ := hexterior x hx
  rcases hplacement ρ hf hi hd with h | h
  · exact h.five_fixed_finrank_le_eight hd x hx hc
  · exact h.five_fixed_finrank_le_eight hd x hx hcc

/-- Actual source use: the section calculation gives eighteen moved dimensions
for every native involution, retaining the original vector space and action. -/
theorem native_displacement_of_golay_exterior
    (hplacement : GolayExteriorPlacement.{v}) (hexterior : GolayExteriorFiveBound)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M24 V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (hd : Module.finrank (ZMod 2) V = 44)
    (t : M24) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    18 ≤ fixedCodim ρ (Subgroup.zpowers t) :=
  native_displacement_of_fiveFixedSpaceBound
    (fiveFixedSpaceBound_of_golay_exterior hplacement hexterior) ρ hf hi hd t ht ht2

end Representation.MathieuM24Degree44
