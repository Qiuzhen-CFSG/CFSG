module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination

/-!
# Marked exclusion with the corrected source FF convention

The A₇ component has order 2520, so its irreducible list cannot contain
an Â₆ action, whose component has order 1080. On this branch the corrected
projective-line contract therefore supplies the existing marked exclusion
without changing any action or offender clause. The full legacy classifier
is not needed. The residual required by that exclusion is derived from the
actual A₇ quotient before constructing its action input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99; final proof of 15.3.1, printed p.1155, PDF p.1172.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases
private theorem irreducible_of_component_card {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L I : Subgroup D}
    (hL : Nat.card L = 2520) (h : ProjectiveLine.IrreducibleActionCase ρ L I) :
    IrreducibleActionCase ρ L I := by
  cases h with
  | linearTwo F h e ho hr => exact .linearTwo F h e ho hr
  | linearThree F h e hr => exact .linearThree F h e hr
  | symplectic F hl h e hr => exact .symplectic F hl h e hr
  | symplecticTwo e hr => exact .symplecticTwo e hr
  | g2 F hl h e ho hr => exact .g2 F hl h e ho hr
  | g2Two e ho hr => exact .g2Two e ho hr
  | symmetric n hn e ho hr => exact .symmetric n hn e ho hr
  | alternatingSix h e ho hr => exact .alternatingSix h e ho hr
  | alternatingSeven h ht e hd ho hr => exact .alternatingSeven h ht e hd ho hr
  | tripleSix _ a _ =>
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [hL, Nat.card_congr a.quotientEquiv.toEquiv,
      Nat.card_congr a.centerEquiv.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd] at hc
  | binaryLinear n hn h e hr => exact .binaryLinear n hn h e hr
  | orthogonalSix h ht e ho hr => exact .orthogonalSix h ht e ho hr
  | symmetricEight ht e hr => exact .symmetricEight ht e hr
  | exteriorFive h ht e hd ho hr => exact .exteriorFive h ht e hd ho hr

private def quasisimple_of_component_card {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L : Subgroup D}
    (hL : Nat.card L = 2520) (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L) :
    QuasisimpleSourceConclusion ρ L :=
  { c with
    clause_one := by
      cases c.clause_one with
      | irreducible hi hf hir h he =>
        exact .irreducible hi hf hir (irreducible_of_component_card _ hL h) he
      | doubleThree F ht e ho hr => exact .doubleThree F ht e ho hr
      | naturalDual n hn ht h => exact .naturalDual n hn ht h
      | repeatedNatural n r hn hr hb ht h => exact .repeatedNatural n r hn hr hb ht h }

/-- The A₇ marked exclusion on the same original module, using the corrected
B.5.1 action witness and the residual derived from the actual quotient. -/
theorem source_alternatingSeven_excluded {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : Intersection.SourceInput V)
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup))
    (e : coreQuotient H ≃* alternatingGroup (Fin 7)) : False := by
  have hres := d.residual_eq_of_fitting_quotient hL
    (d.component_row_alternatingSeven hL e).2.2
  let a := d.toActionInput hres
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (coreQuotient H) := e.isSimpleGroup
  have ht : generalizedFitting (coreQuotient H) = ⊤ := by
    let := hL.simple
    let : Nontrivial (generalizedFitting (coreQuotient H)) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting (coreQuotient H)))).nontrivial
    exact (inferInstance : (generalizedFitting (coreQuotient H)).Normal).eq_bot_or_eq_top.resolve_left
      ((Subgroup.nontrivial_iff_ne_bot _).mp inferInstance)
  have hc : Nat.card (generalizedFitting d.offenderGroup) = 2520 := by
    rw [Nat.card_congr (d.offenderFittingEquiv hL).toEquiv, ht, Subgroup.card_top,
      Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact MarkedElimination.source_marked_cases_excluded a
    (.quasisimple (d.offender_fitting_quasisimple hL)
      (quasisimple_of_component_card d.offenderAction hc c)) (Or.inr ⟨e⟩)
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases
