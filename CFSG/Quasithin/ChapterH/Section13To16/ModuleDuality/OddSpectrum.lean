module

public import CFSG.Quasithin.ChapterH.Section13To16.ModuleDuality
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum

/-!
# The numerical odd-prime part of H.15.7(1)

For the actual eleven-dimensional cocode modules, an odd-prime actor has
displacement at least six.  If its fixed space has rank at least four, the
prime is three, the fixed space has rank five, and the native permutation
action has exactly six fixed points.  The separate six-point development
supplies the normalizer and module-model clauses of H.15.7(1).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.7(1)
and the beta table on printed pp.396 and 401–402.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu MathieuCode
open Representation.BinaryOffender

/-- The numerical H.15.7(1) conclusion for the native M₂₄ cocode. -/
theorem lemma_H_15_7_1_cocode_numeric_m24 (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hlarge : 4 ≤ Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D)) :
    p = 3 ∧ Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5 ∧
      Nat.card (MulAction.fixedPoints D (Fin 24)) = 6 :=
  large_cocode_fixed D hp ho hD hlarge

/-- The numerical H.15.7(1) conclusion for the native M₂₃ cocode. -/
theorem lemma_H_15_7_1_cocode_numeric_m23 (D : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hlarge : 4 ≤ Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation D)) :
    p = 3 ∧ Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation D) = 5 ∧
      Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6 :=
  m23_large_cocode_fixed D hp ho hD hlarge

/-- The beta value six is attained by a native order-three actor in M₂₄. -/
theorem beta_six_attained_m24_cocode :
    ∃ D : Subgroup M24, Nat.card D = 3 ∧
      fixedCodim cocodeRepresentation D = 6 :=
  exists_m24_cocode_displacement_six

/-- The beta value six is attained by a native order-three actor in M₂₃. -/
theorem beta_six_attained_m23_cocode :
    ∃ D : Subgroup M23, Nat.card D = 3 ∧
      fixedCodim m23CocodeRepresentation D = 6 :=
  exists_m23_cocode_displacement_six

end CFSG.Quasithin.ChapterH.Section13To16
