module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalReduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCore
public import Theory.GroupTheory.CharacteristicRestrictionInnerSquares

/-!
# Inner squares from the two-core of the J₄ involution centralizer

Let C be the literal involution centralizer and Q = O₂(C). An automorphism
of C restricts to a normalizer of the conjugation image of C in Aut(Q).
If this image is self-normalizing, the restriction is induced by an element
c of C. Correcting by c leaves an automorphism fixing Q pointwise. If C_C(Q)
lies in Q and has exponent two, the corrected automorphism has square one,
so the original square is inner.

The two local structural inputs remain explicit hypotheses. This module does
not yet prove `localNormalizerActionSquares`. Their intended source is the
2A centralizer in GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`; the literal matrix comparisons and
normalizer calculation must still be established. No global normalizer,
ambient implementation, or commutant premise is used in this reduction.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares

/-- Two local structure calculations imply inner squares for all
automorphisms of the actual centralizer. Both inputs remain to be proved. -/
theorem involutionCentralizer_automorphism_squares_of_twoCore
    (hcent : LocalTwoCoreCentralizerControl)
    (hnorm : LocalTwoCoreActionSelfNormalizer)
    (α : MulAut involutionCentralizer) :
    ∃ c : involutionCentralizer, α ^ 2 = MulAut.conj c :=
  Subgroup.square_inner_of_self_normalizing_conjNormal_range involutionTwoCore
    hcent.1 hcent.2 hnorm α

/-- The same two local inputs give the action required by `LocalReduction`.
Only an action on C is asserted, without membership of the ambient square. -/
theorem localNormalizerActionSquares_of_twoCore
    (hcent : LocalTwoCoreCentralizerControl)
    (hnorm : LocalTwoCoreActionSelfNormalizer) : LocalNormalizerActionSquares :=
  localNormalizerActionSquares_of_automorphism_squares
    (involutionCentralizer_automorphism_squares_of_twoCore hcent hnorm)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares
