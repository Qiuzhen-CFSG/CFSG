module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSevenCheck
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.CoverIntersections
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.MathieuEleven
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.Source

/-!
# Component refinement for Lemma 2.3.9(7)

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.525–526 (PDF pp.542–543).

The original Γ₀ setup now supplies the marked component action using the
universal A/B/C theorem, and all six 1.1.5 model families feed the actual
intersection calculations. The direct surviving models, alternating covers,
central two-covers and nontrivial PSL₄(2) diagram action are retained.

The explicit residual is a binary M₂₂ component; the quartic cover and all
seven discarded sporadic models are excluded. In that residual the selected
ambient Sylow has cyclic center, proved from its faithful central Omega
action. Excluding this binary cover is still necessary before asserting
Lemma 2.3.9(7) without a residual alternative. The earlier universal A/B/C
and local C.1.29 implications remain with their source assembly owners.
-/
