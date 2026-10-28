module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces

/-!
# Duality of the eleven-dimensional Mathieu modules

The concrete intersection-parity pairing supplies equivariant identifications
of each code with the dual of its cocode, for the native M₂₄ action and the
native point-stabilizer restriction to M₂₃. The imported cyclic displacement
identities transfer numerical actor bounds between these actual modules.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
11-dimensional duality clause of H.13.1, printed p.395. Absolute
irreducibility (H.13.2) and the odd-prime classification (H.15.7) require
additional results and are not asserted here.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode

/-- The eleven-dimensional duality clause of H.13.1 for both native groups. -/
theorem lemma_H_13_1_eleven_dimensional_duality :
    Nonempty (codeRepresentation.Equiv cocodeRepresentation.dual) ∧
      Nonempty (m23CodeRepresentation.Equiv m23CocodeRepresentation.dual) :=
  ⟨⟨codeDuality⟩, ⟨m23CodeDuality⟩⟩

end CFSG.Quasithin.ChapterH.Section13To16
