module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.ResidualLift

/-!
# The minimal-parabolic reduction in Lemma 8.2.9

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.719–721 (PDF pp.736–738).

The current exports prove the lift from O²(H/O₂(H)) ≤ I⁺ to equality of the
embedded residuals, the literal product H = IT, and normalization of VA.
They also discharge this quotient containment when its residual has prime
order and |I⁺| has an odd prime divisor, and give the resulting contradiction
with the code-module nonnormalization assertion of 8.2.8(6).

The complete Lemma 8.2.9 remains to be assembled here. Missing branches are
the odd-prime rank bounds and minimal-parabolic sieve, the cocode U₃(4)
exclusion, and the chief-section/multiplicity/transvection exclusions of
Aut(L₃(2)) and L₂(31). The genuine setup and 8.2.2–8 are supplied by the
parent normalizer theorem, together with the full E.2.2 and B.6.8 inputs.
The quotient-cover premise is not asserted as a source theorem.
-/
