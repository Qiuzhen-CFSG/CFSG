module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.Center
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.LocalSylow

/-!
# The factor-count argument in Section 15.4

This module collects proved steps for Aschbacher–Smith 15.4.14–15 and 15.4.18,
combined 1 March 2004 manuscript, printed pp.1161–1163.

The current proofs derive the center lower bound from the exact small-center
alternatives and the ordering maximality of 15.4.11. They derive central fixed
indices from single-factor indices or compatible swapped quotient coordinates,
then obtain order four and rank two. The mixed-factor calculation proves the
fixed-subgroup disjointness, the order-eight omega calculation, and nontrivial
common fixed subgroup under the displayed action inputs. The Sylow lemmas
promote a local Sylow witness using the actual Baumann subgroup and supply the
intermediate hypotheses of 1.1.5. Quotient isomorphisms and intersections are
transported into the generated group for the genuine Goldschmidt triple API.

Source assembly is still open: the 15.4.12 actions must produce the coordinate
and mixed-factor witnesses, the F.6.5 alternatives must give the at-most-one
restriction, and both generalized-Fitting branches of 15.4.18 must be eliminated.
No theorem here asserts the final universal conclusion `s(Y) = 2`.
-/
