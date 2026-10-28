module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.BinaryEndpoint

/-!
# Cover assembly for the classical field-pair fixer bounds

The faithful quotient action, component image, and central quotient comparison
reduce each field row to `ComponentFixerBound` on the actual projected subgroup.
The intrinsic PSL₂, PSL₃, and Sp₄ fixer calculations remain explicit inputs;
this conditional assembly does not assert that they have been proved.

The PSL₂ parameter restriction is unconditional: its field-order-two derived
endpoint is solvable and cannot be the central quotient of a component.

Source: Aschbacher–Smith, 16.1.7(3a) and 16.3.5, combined manuscript of
1 March 2004, printed pp.1172–1173 and 1178–1179.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical
open Subgroup Theory.GroupTheory
open CounterexampleGeometry.CoveredPersistence
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G}

/-- Conditional field-row assembly; the intrinsic component-fixer calculation
is the sole remaining premise beyond the source pair and its model endpoints. -/
theorem fieldBound_of_componentFixer {X : FieldFamily}
    (hmodel : ComponentFixerBound.{u} X)
    (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    {n : ℕ} (hn : 1 ≤ n)
    (hlarge : X.ModelAt (I ⧸ pCore 2 I) (2 ^ (2 * n)))
    (hsmall : X.DerivedAt (L ⧸ pCore 2 L) (2 ^ n)) :
    Nat.card (pairFixer L I) < 4 := by
  let e := MulEquiv.refl (I ⧸ pCore 2 I)
  let := h.component.quasisimple
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup (I ⧸ pCore 2 I) := (centerModelEquiv h hG e).symm.isSimpleGroup
  let : Group.IsPerfect (I ⧸ pCore 2 I) :=
    Group.IsPerfect.ofSurjective (f := (h.coreCover hG e).toMonoidHom)
      (h.coreCover hG e).surjective
  exact pairFixer_card_lt_of_cover (h.coreCover hG e) (h.coreCover_kernel hG e)
    (hmodel _ n hn hlarge (modelAction h hG e) (modelAction_order h hG e)
      (projected h hG e) (projected_component h hG e)
      (projected_center_isTwoGroup h hG e)
      (projected_derived h hG e X (2 ^ n) hsmall))

/-- The linear-two source pair automatically excludes the field-order-two endpoint. -/
theorem linearTwo_pair_parameter_gt_one
    (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    {n : ℕ} (hn : 1 ≤ n)
    (hsmall : FieldFamily.linearTwo.DerivedAt (L ⧸ pCore 2 L) (2 ^ n)) : 1 < n := by
  let := h.setup.component.quasisimple
  apply linearTwo_parameter_gt_one (P := L) hn
  obtain ⟨M, hM, hfin, hm, ⟨d⟩⟩ := hsmall
  exact ⟨M, hM, hfin, hm, ⟨(QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore h.setup.involution_t h.setup.component)).trans d⟩⟩

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical
