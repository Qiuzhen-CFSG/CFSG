module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Reduction

/-!
# Postclassification deductions for B.5.1

`ExtensionConsequences.clause_three` proves the full homogeneity conclusion
on the literal quotient [V,L]/C_[V,L](L). The only exception is the specified
natural-plus-dual action in dimensions four and five.

`ExtensionConsequences.irreducible_or_split` proves that every other reducible
action alternative splits over C_V(G), and that G = L in that branch. The
three `irreducible_of_...` consumers consequently establish the irreducible
reduction needed for clauses (2), (4), and (5). In particular, the double-natural
SL₃ case includes every positive binary-field degree; at degree one its proof
uses the concrete offender exclusion rather than cohomology vanishing.

`ExtensionConsequences.linearThree_fixed_kernel` proves the literal L₃(2)
fixed-kernel condition of (5) after the whole-actor equality G = L. All these
results are proved without additional earlier-source parameters.

The full natural list in (2), the S₆/S₈ action and cardinality-two quotient in
(4), and the shortened natural list in (5) remain to be assembled from the
irreducible cohomology and outer-complement arguments. No unproved assertion
that the present module splits or belongs to those lists is an input here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99 and 102–103.
-/
