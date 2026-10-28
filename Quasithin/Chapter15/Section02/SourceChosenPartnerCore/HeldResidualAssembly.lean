module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.HeldResidual
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.NormalizerIrreducible
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Models

/-!
# Partner-core assembly with the retained Held residual row

The residual component reduction supplies either one of the three source
structural alternatives or the literal Held residual row.  The former is
discharged by the existing partner-core theorem; the latter is discharged by
the Held fixed-codimension argument in `HeldResidual`.  This is the narrow
Section 15.2 consumer that reconnects the retained model row to the original
15.2.27 conclusion.

Source: Aschbacher--Smith, 15.2.12(2) and 15.2.27(2), printed pp.1111,
1118--1119 (refs/quasithin.pdf pp.1128, 1135--1136).
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The literal residual input closes partner-core containment in both rows.

The only model-specific premise is the actual `HeldResidualCase`; no family
tag or unconditional Held exclusion is introduced. -/
theorem source_chosen_partner_core_of_residual_input
    {T : Sylow 2 G} {M Mc V H ZS B : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (hg : ChosenPlaneGeometry h H ZS)
    (d : ResidualInput h H B)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    V ≤ twoCoreIn Mc := by
  rcases d.structural_or_held with hs | hh
  · exact source_chosen_partner_core h hg hMc hZ hquotient hres hs hplane
  · exact source_chosen_partner_core_of_held h hg hMc hZ hquotient hres hh

end CFSG.Quasithin.Chapter15.Section02
