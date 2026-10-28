module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetModule

/-!
# Excluding binary degree twelve from a concrete coset filtration

The central cubic recovers F₄ scalars on every faithful irreducible binary
module. This preserves irreducibility without claiming absolute
irreducibility. The universal central coset quotient and a checked
three-or-nine factor filtration would therefore exclude field dimension
six, and hence binary dimension twelve.

The finite filtration is explicit and remains a prerequisite. This module
does not assert its existence from the printed decomposition matrix.
Source: Aschbacher–Smith K.1.3, printed p.453, citing GM02 Theorem 6.2/Table 6.3.
-/

@[expose] public section
open Atlas.Codes
namespace Representation.Hexacode.TwelveDimensional

/-- The exact intrinsic degree exclusion follows from the specified finite
coset certificate. Both nonabsolute and absolute irreducibility cases are covered. -/
theorem finrank_ne_twelve_of_cosetFiltration (h : CosetFiltration)
    {V : Type*} [AddCommGroup V] [Module Bit V] [FiniteDimensional Bit V]
    (ρ : Representation Bit HexEvenAutomorphisms V)
    (hf : Function.Injective ρ) [IsIrreducible ρ] : Module.finrank Bit V ≠ 12 := by
  let hq := scalar_quadratic ρ hf
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  let := field_finite ρ hq
  let := fieldRepresentation_irreducible ρ hq
  have hn := field_finrank_ne_six_of_cosetFiltration h (fieldRepresentation ρ hq)
    (fieldRepresentation_scalar ρ hq)
  have hd := field_finrank ρ hq
  omega

end Representation.Hexacode.TwelveDimensional
