module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.HeldResidualConsumer
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.Components

/-!
# Ambient exclusion of the retained Held residual

The Held residual quotient is quasisimple, whereas the original wreath
residual has elementary quotient of order nine. Thus the Held row is a
strict component row, where the literal prime-complement residual identity
has already been proved. The terminal chosen-action contradiction then
excludes Held under the actual ambient source hypotheses.

This supplies the short structural list without assuming a residual identity
or a Held exclusion. The preceding global H-star wreath quotients remain
explicit; no intrinsic exclusion from the local Held catalogue is asserted.

Source: Aschbacher--Smith, 15.2.12 and 15.2.27--28,
printed pp.1111,1119--1120.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1
open Chapter13.Section08.Components.Swapped.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- A Held residual cannot equal the original residual with its elementary
order-nine two-core quotient. -/
theorem ResidualInput.held_residual_ne {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (hh : HeldResidualCase T H Mc) :
    partnerSpan H Mc ≠ residual H := by
  intro he
  obtain ⟨P, _, _, _, hq, _⟩ := hh
  let : IsQuasisimple (XiQuotient (residual H)) := he ▸ hq
  let e := residualQuotientEquiv H d.quotient.some
  let : Group.IsPerfect WreathModel.cubicBase :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card WreathModel.cubicBase = 1 := Nat.card_unique
  rw [WreathModel.cubicBase_card] at hc
  exact (by decide : (9 : ℕ) ≠ 1) hc

/-- The ambient chosen-action hypotheses exclude the actual Held branch.
Its residual identity is proved from its strict component row. -/
theorem ResidualInput.held_excluded {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath)) : ¬ HeldResidualCase T H Mc := by
  intro hh
  exact source_chosen_contradiction_of_held_residual_input h d hquotient
    (d.residual_equality_of_ne (d.held_residual_ne hh)) hh

/-- Original 15.2.12(2) under the preceding global wreath recognition.
The additional Held alternative is discharged by the ambient terminal proof. -/
theorem ResidualInput.structural_of_wreath_quotients {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath)) : StructuralAlternatives T H Mc :=
  d.structural_of_held_exclusion (d.held_excluded hquotient)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
