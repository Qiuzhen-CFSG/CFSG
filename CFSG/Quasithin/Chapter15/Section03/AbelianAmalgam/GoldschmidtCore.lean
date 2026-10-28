module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Sylow
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.CoreReduction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Assembly

/-!
# The Goldschmidt configuration of Lemma 15.3.68

`exists_terminal_configuration` constructs the second singular line, the
literal local products, their symmetric quotients and intersection, and
clauses (1), (3), (4), and (5) of 15.3.68. The maximal-local Sylow condition
and the intrinsic Goldschmidt triple are derived from the local geometry.
The Thompson argument identifies the three-prime core with the two-core,
using the explicit earlier-source F.6.11(1) and B.2.16 witnesses.

The geometric seed `F = ⟨Z^{Y_F}⟩` is proved from the specified natural
orthogonal action. All normality in the core argument is relative to `G₀`.
The separate clause (2), `V ≤ Z(O₂(G₀))`, remains open; the weaker
`V ≤ O₂(G₀)` suffices for the other four clauses. The printed common-core
equality and even the proposed common-core containment have checked
obstructions, preserved in their existing modules. No full numbered
15.3.68 theorem is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1154–1155, PDF pp.1171–1172.
-/
