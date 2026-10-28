module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.Forms

/-!
# The monomial summands of the fixed Griess space

This interface realizes the diagonal `B_R`, the off-diagonal and two `w`
spans `B_E`, and the odd and two natural--half-spin spans `B_0` inside
`Sporadic.Monster.GriessSpace`. The comparison `NMonomial.griessSplitting`
is addition of these spaces and the existing octad span. Its images are
complementary and orthogonal for the existing Griess form.

The generator inclusions and restricted forms retain the source normalization,
in particular `wPlus = v+u` and `wMinus = v-u`. This geometric interface does
not yet assert the extended `N` representations or their cubic invariance;
those require the module comparisons and actions of Sections 29.5–29.11.

Source: Aschbacher, *Sporadic Groups*, 27.8(5), 29.1, printed pp. 150, 154.
-/
