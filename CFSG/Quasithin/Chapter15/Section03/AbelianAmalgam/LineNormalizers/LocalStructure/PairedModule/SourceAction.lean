module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.CoreAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.SourceAction.Squares
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.SourceAction.FixedLifting
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.SourceAction.Cubic

/-!
# Action data from the original local hypotheses

This constructs the published `ActionData` for the original `U=V_E` and
`G_E=N_G(E)`, before the temporary replacement in the proof of 15.3.67.
Its inputs are the compatible natural action and the preceding local
outputs: the singular four-group, elementary four-group image of `T_E`,
centralizer-span and commutator identities, core containment, the marked
image of `Y_E`, and `τ ∉ S_E`.

The core acts trivially on `U/E`. A cubic generator lifts from `A₃ × 1`,
and `U=[U,Y_E]` gives its zero norm. Marked commutation propagates the
square-centralization of `T_E` on `V` to square-centralization of `τ` on
`U`. The four-group difference lemma then corrects every quotient-fixed
representative inside `E`, producing actual fixed lifts in `U`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.66(3)
and the proof of 15.3.67, printed pp.1152–1153, PDF pp.1169–1170.
The paired decomposition and final source-theorem assembly are separate.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule.SourceAction
open Descent.QuotientIdentification GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] {V M Y T E : Subgroup G}
variable [IsMulCommutative V] [IsElementaryAbelian 2 (lineV V E)]

/-- Construct all original action identities and actual fixed lifts from the
preceding local geometry. No splitting or fixed-lifting premise is assumed. -/
noncomputable def actionData (a : OrthogonalFourBinary.NaturalAction V M)
    (d : MarkedDecomposition Y T E)
    (hTM : T ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, a.singular ⟨e, hEV e.property⟩)
    (hfour : IsKleinFour (actionImage a (lineT T E)))
    (hspan : lineV V E = conjugateSpanBy V (lineC E))
    (hQS : lineQ E ≤ T ⊓ centralizer (E : Set G))
    (hVS : ⁅V, T ⊓ centralizer (E : Set G)⁆ = E)
    (hmove : lineV V E = ⁅lineV V E, lineY Y E⁆)
    (hY : ((lineY Y E).subgroupOf (lineNormalizer E)).map
      (d.equiv.toMonoidHom.comp (quotientMap E)) =
      (alternatingGroup (Fin 3)).prod ⊥)
    (htau : d.tau ∉ T ⊓ centralizer (E : Set G)) : ActionData V E d :=
  Classical.choice <| by
    let := hfour
    let : IsKleinFour E := Orthogonal.singularLine_isKleinFour a E hEV hcard hs
    have hcomm := core_commutator_le_line T V E hEV hspan hQS hVS.le
    obtain ⟨y, hy, hyorder, hysecond⟩ := exists_original_cubic d hY
    refine ⟨{
      y := y
      y_mem := hy
      y_order := hyorder
      y_second := hysecond
      tau_order := tau_first_order a d hTM hEV hQS htau
      norm_eq_zero := cubic_norm_eq_zero d hcomm hmove hY y hyorder hysecond
      fixedImage_eq := ?_ }⟩
    exact fixedImage_eq_of_square_centralizes V E
      (hEV.trans (le_conjugateSpanBy V (lineNormalizer E)))
      ⟨d.tau, d.tau_mem.2⟩ (tau_square_centralizes_span a d hTM hspan hQS)
      (fun hc => htau ⟨d.tau_mem.1, hc⟩)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule.SourceAction
