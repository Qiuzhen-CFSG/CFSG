module

public import CFSG.Quasithin.ChapterH.Section13To16.ModuleDuality
public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute

/-!
# H.13.2 for the eleven-dimensional Mathieu modules

The actual code and cocode quotient actions are absolutely irreducible for
both M₂₄ and its native M₂₃ point stabilizer. Irreducibility comes from the
order-23 dimension bound; Schur's finite endomorphism field and the prime
dimension give absolute irreducibility.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the two
eleven-dimensional cases of Proposition H.13.2, printed p.395.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode

/-- The M₂₄ and M₂₃ clauses of H.13.2 for the actual code and cocode actions. -/
theorem proposition_H_13_2_eleven_dimensional :
    codeRepresentation.IsAbsolutelyIrreducible ∧
      cocodeRepresentation.IsAbsolutelyIrreducible ∧
      m23CodeRepresentation.IsAbsolutelyIrreducible ∧
      m23CocodeRepresentation.IsAbsolutelyIrreducible :=
  ⟨code_isAbsolutelyIrreducible, cocode_isAbsolutelyIrreducible,
    m23Code_isAbsolutelyIrreducible, m23Cocode_isAbsolutelyIrreducible⟩

end CFSG.Quasithin.ChapterH.Section13To16
