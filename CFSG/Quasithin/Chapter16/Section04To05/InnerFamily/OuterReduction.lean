module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CommutingConjugates
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Consequences

/-!
# Reduction of the empty inner-action family to exceptional outer actions

The completed part proves the whole assertion (+): a distinct commuting
L-conjugate rˡ normalizes K′, its centralizer in K′ has Sylow subgroup ⟨r⟩,
and the product r rˡ does not belong to L′. This uses tight embedding and
the transported order-two assertion, without assuming forbidden fusion.

The shared target `CommutingSylowDichotomy` keeps the actual PSL₃(4) and
M₂₂ quotients. Its construction, the centerless-model sieve, the PSL₃(4)
field/graph cover arguments, the four remaining cover-fusion arguments, and
the M₂₂ rank-six argument remain to be proved. The final exceptional-case
reduction is consequently not asserted here.

The built consequences already turn that dichotomy and the actual surviving
models into T_C = ⟨z⟩, and convert model fusion witnesses into contradictions
using (!) and the residual placement from 16.4.8. The central-twist lemma
retains the order-four inversion used in the cover argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed pp.1189–1191. Final discharge of the order-two premise
belongs to the assembly of 16.4.9.
-/
