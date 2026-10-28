module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.LocalTransfer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ActionGeneration
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.OffenderTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ResidualNormalizer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.SeedAction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.Selection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.SectionConstruction

/-!
# Component reduction in the extraspecial branch

This module assembles the proved local transfer and section-action algebra for
15.3.49(i)–(l). The literal conjugate spans remain `U_H = ⟨Z_S^H⟩` and
`V_H = ⟨V^H⟩`. The replacement keeps `L₀ = ⟨L^T⟩` separate from `L₀Y₀T`.
Conjugation preserves the selected quadratic best offender, and the actual
normalizer `N_G(Y₀) = M` gives the residual-normalizer step in (i).
After `Y₀ ≤ L = L₀` has been proved, the nontrivial offender implies
`L = [L,U_γ]`; this conclusion is derived from the reduced component data.
The seed argument for the larger-field exclusion is proved modulo `Z`,
including its fixed-space projection step.
Given (i), a component is selected and the replacement is proved to belong
to the genuine outside local family, with its theta and normality identities.
The actual faithful section action is reconstructed from the earlier
quotient-centralizer identity, including on smaller elementary conjugate spans.

Still required are the exclusion of the solvable B.5.6 factors, the proof of
`Y₀ ≤ L₀`, the larger-field module exclusion, and the precise model and
minimal-parabolic alternatives. The transfer lemmas do not assert those
conclusions or a strong offender. Final component assembly remains here;
the full extraspecial exclusion belongs to the parent development.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1144.
-/
