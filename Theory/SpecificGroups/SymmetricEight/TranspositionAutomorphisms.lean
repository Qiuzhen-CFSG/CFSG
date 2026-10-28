module

public import Theory.Alternating.Aut

/-!
# Lifting automorphisms centralizing a transposition of A₈

The conjugation map from S₈ to Aut(A₈) is bijective. Its surjectivity lifts
an automorphism of A₈ to a permutation, and its injectivity shows that a lift
of an automorphism commuting with conjugation by `(0 1)` commutes with `(0 1)`
itself.

This is the intrinsic automorphism fact used in the centralizer comparison
in Aschbacher–Smith, Lemma 2.5.26, printed p.569 of the combined 1 March 2004
manuscript. The general alternating-group automorphism theorem is proved in
`Theory.Alternating.Aut`, following GLS vol. 3, Theorem 5.2.1.
-/

namespace Theory.SpecificGroups.SymmetricEight

/-- Every automorphism of A₈ commuting with conjugation by `(0 1)` is induced
by a permutation of the eight points commuting with `(0 1)`. -/
public theorem lift_transpositionCentralizing_automorphism
    (f : MulAut (alternatingGroup (Fin 8)))
    (hf : Commute f (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1))) :
    ∃ q : Equiv.Perm (Fin 8), Commute q (Equiv.swap (0 : Fin 8) 1) ∧
      MulAut.conjNormal q = f := by
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    8 (by decide) (by decide)
  obtain ⟨q, rfl⟩ := hbij.2 f
  refine ⟨q, ?_, rfl⟩
  show q * Equiv.swap (0 : Fin 8) 1 = Equiv.swap (0 : Fin 8) 1 * q
  apply hbij.1
  simpa only [map_mul] using hf.eq

end Theory.SpecificGroups.SymmetricEight
