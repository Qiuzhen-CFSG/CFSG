module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Family
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Reduction

/-!
# Geometry and the Thompson branch of the A₅ centralizer reduction

The nonsingular-vector family uses the polar hyperplanes in the actual
marked A₅ module. These generate V. Moving singular seeds prove that
hypothetical relative normality of V_v lets G_v permute this family, hence
normalize V. A counterexample therefore gives relative nonnormality and
M_v < G_v, while the earlier normalizer identity makes M_v normalize V_v.

The downstream branch constructs the internal elementary module in Z(Q_v),
proves that both its literal centralizer quotient and G*_v have trivial
two-core, and carries out the Baumann–Frattini contradiction. From relative
nonnormality of V_v it obtains the nontrivial images of both J(T_v) and
J(G_v), and an actual faithful binary FF-module agreeing with starAction.

`geometric_thompson_reduction_of_localReductions` assembles these results
on the actual marked flag and earlier local configuration. It constructs
all geometric and Thompson/FF conclusions of the conditional reduction
13.6.8–9. The parent component-selection assembly still must supply the
earlier configuration, fusion 13.2.6(2) and characteristic two 13.6.6 from
the genuine source hypotheses.

Source: Aschbacher–Smith, combined manuscript, printed p.928.
-/
