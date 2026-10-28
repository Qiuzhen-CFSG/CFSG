module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.InvariantSubgroups
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.SourceApplication

/-!
# Ree and Tits local rigidity in Lemma 14.2.21

This entry point preserves the intrinsic invariant-subgroup lemmas and
exports the completed local argument for the actual marked Ree and Tits
parabolics. The corrected core classification includes the additional
full-Ree omega subgroup and excludes it using characteristic centralizer
detection. Conjugation on the derived subgroup constructs the ambient
point-stabilizer action and forces core normality. The odd-residual and
involution-orbit calculation then excludes a proper Sylow-preserving
overgroup of characteristic two centralizing the marked involution.

`ree_rigidity` and `tits_rigidity` discharge every intermediate action,
core-containment, normality and quotient-centralizer premise.
`ree_eq_mc` and `tits_eq_mc` apply them to a literal marked isomorphism
onto H ≤ Mc = C_G(Z). `rigidity_and_factorization` also gives M = YT
from the earlier source centralizer decomposition. The parent proof retains
recognition and the earlier Hypothesis 14.2.1 inputs, as well as the other
four amalgam alternatives; these exports do not assert all of 14.2.21.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 14.2.21, printed pp.988--989, PDF pp.1005--1006.
Concrete calculations: Aschbacher, *The Tits groups as a standard subgroup*,
Math. Z. 181 (1982), Section 3, and the actual marked comparisons re-exported
by `Parabolics.MarkedComparison`.

The full-Ree second center is E, not F. The distinguished cyclic-four
centralizer belongs to the chosen five-complement, not the two-residual.
The actual Tits core has order 512 and quotient of order twenty. Residuals
are mapped through quotient homomorphisms; the local core is not silently
assumed contained in the local two-residual. All original public helper
statements remain unchanged.
-/
