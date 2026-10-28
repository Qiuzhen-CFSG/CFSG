module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.HeldResidualAssembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.NormalRankTwoCore

/-!
# Partner-core assembly from the complete residual input

The component rows already identify the residual with the three-prime
residual.  In the remaining equality row, the normal rank-two core argument
puts the chosen module in the partner two-core directly.  Thus the actual
`ResidualInput` discharges the residual-equality premise of the older Held
assembly, while preserving its structural and Held branches.

Source: Aschbacher--Smith 15.2.12(4) and 15.2.27(2), printed pp.1111,
1118--1119.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Partner-core containment from an actual `ResidualInput`, with the
residual-equality premise discharged by the equality/non-equality split. -/
theorem source_chosen_partner_core_of_complete_residual_input
    {T : Sylow 2 G} {M Mc V H ZS B : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (hg : ChosenPlaneGeometry h H ZS)
    (d : ResidualInput h H B)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    V ≤ twoCoreIn Mc := by
  by_cases he : partnerSpan H Mc = residual H
  · exact d.partner_core_le_twoCore_of_eq hquotient he
  · exact source_chosen_partner_core_of_residual_input h hg d hMc hZ hquotient
      (d.residual_equality_of_ne he) hplane

end CFSG.Quasithin.Chapter15.Section02
