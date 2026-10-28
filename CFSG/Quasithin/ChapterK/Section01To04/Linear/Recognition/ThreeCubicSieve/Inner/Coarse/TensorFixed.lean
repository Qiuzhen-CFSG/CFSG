module

public import Theory.Representation.SL3.BinaryDefiningFactors.ParabolicFixed
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Coarse.WordArithmetic

/-!
# The root-plane half-degree bound for non-small SL₃ tensor words

The concrete polynomial restriction theorem bounds the common fixed space by
`2^(a+b)`. For two natural/dual factors or at least one adjoint factor, the word
has degree at least twice that number. Rank-nullity gives the half-degree
estimate on the literal root-plane fixed quotient.

This discharges the tensor estimate required by
`Inner.finrank_le_eight_mul_of_word_estimate`. Its owner supplies the repeated
word's length and factor-count hypotheses and carries out the offender and
Schur-field assembly. Both root-plane orientations and arbitrary coefficient
embeddings are included, without a restriction excluding the field of order two.

Source: Guralnick–Malle, *Classification of 2F-modules II*, author manuscript
Proposition 4.7, pp.25–26; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
noncomputable section
open Representation Representation.SL3.BinaryDefiningFactors
open Matrix.PSL3.RootPlaneGeometry

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner.Coarse

/-- The full root plane moves at least half the word space when the word has
at least two natural/dual factors or an adjoint factor. -/
theorem word_rootPlane_half_degree {F K : Type*} [Field F] [Field K]
    [Finite F] [CharP K 2] (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hlen : w.length = n)
    (hlarge : 2 ≤ naturalCount w ∨ 0 < adjointCount w) (side : Bool) :
    Module.finrank K (WordSpace K w) ≤ 2 * Module.finrank K
      (WordSpace K w ⧸ invariants ((wordRep ι w).comp (rootPlaneSL F side).subtype)) :=
  half_degree_of_word_fixed_bound ι w (rootPlaneSL F side) hlarge
    (ParabolicFixed.finrank_invariants_le ι n hcard w hlen side)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner.Coarse
