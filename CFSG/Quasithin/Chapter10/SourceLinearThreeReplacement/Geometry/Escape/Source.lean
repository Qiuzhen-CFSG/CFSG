module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Assembly
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion.WholeModule

/-!+# Escape of every original central involution centralizer

Assuming C_G(z) ≤ M, diagonal transitivity and pure-factor nonfusion give
M-control of fusion on the literal full module V. Point-centralizer control
and N_G(V) = M then make V a TI-subgroup by I.6.1(1). Its two natural
SL₃(2) factors have order eight, so w=2 supplies a faithful rank-four
offender with constant nonidentity fixed subgroups. The actual pair action
excludes that offender, proving C_G(z) is not contained in M.

This discharges `Geometry.EscapeAt` for every eligible z, retaining exactly
its earlier fixed-space and moved-factor TI premises. The fundamental setup
supplies the ambient simple QTKE hypothesis. Neither the centralizer two-core
argument nor the replacement theorem is used.

Source: Aschbacher--Smith, Lemma 10.3.2, printed p.756, PDF p.773 of
`refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
variable {G : Type*} [Group G] [Finite G]

/-- Source 10.3.2 on the original full module, with the diagonal-fusion and
rank-four offender arguments both discharged. -/
theorem escapeAt (T : Sylow 2 G) : EscapeAt T :=
  escape_of_wholeModuleTI (Fusion.wholeModuleTIAt T)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
