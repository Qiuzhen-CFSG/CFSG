module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Bounds
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# The distinguished involution and the embedded component in the Lie rows

The involution t acts by actual ambient conjugation on I. Faithfulness on E
preserves its order. Restricting the component of C_G(t) retains L both in
I ∩ C_G(t) and, intrinsically, in the fixed subgroup of this action on I.
These are embedding data for the model calculations, not fixer bounds.

Source: Aschbacher–Smith, 16.1.7(3) and 16.3.5, combined manuscript of
1 March 2004, printed pp.1172–1173 and 1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {E L I : Subgroup G} {t i : G}

/-- The actual action of the distinguished involution on the enlargement. -/
def PairContext.involutionAction (h : PairContext E L I t i) : MulAut I :=
  inducedAction E I h.normalizes ⟨t, h.t_mem⟩

/-- Faithfulness ensures that the action is itself an involution. -/
theorem PairContext.involutionAction_orderOf (h : PairContext E L I t i) :
    orderOf h.involutionAction = 2 := by
  rw [involutionAction, orderOf_injective _ h.faithful,
    ← orderOf_injective E.subtype E.subtype_injective]
  exact h.setup.involution_t

/-- The distinguished involution fixes every element of the actual embedded L. -/
theorem PairContext.involutionAction_fixes (h : PairContext E L I t i)
    (x : L.subgroupOf I) : h.involutionAction x = x := by
  apply Subtype.ext
  change t * (x : G) * t⁻¹ = (x : G)
  have hc := mem_centralizer_singleton_iff.mp (h.setup.component.1 x.property)
  change (x : G) * t = t * (x : G) at hc
  rw [← hc]
  simp [mul_assoc]

/-- Relative component membership in the actual ambient centralizer. -/
theorem PairContext.component_in_centralizer (h : PairContext E L I t i) :
    Theory.GroupTheory.IsComponentIn L (I ⊓ centralizer ({t} : Set G)) :=
  ComponentTransfer.IsComponentIn.restrict h.setup.component
    (le_inf h.proper.le h.setup.component.1) inf_le_right

/-- The same component retained inside the intrinsic fixed subgroup of I. -/
theorem PairContext.component_in_action_fixed (h : PairContext E L I t i) :
    Theory.GroupTheory.IsComponentIn (L.subgroupOf I) h.involutionAction.fixedSubgroup := by
  have hle : L.subgroupOf I ≤ h.involutionAction.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (h.involutionAction_fixes ⟨x, hx⟩)
  let φ : h.involutionAction.fixedSubgroup →* involutionCentralizer t :=
    { toFun := fun x => ⟨(x : I), by
        apply mem_centralizer_singleton_iff.mpr
        have hx := congrArg (fun y : I => (y : G))
          ((MulAut.mem_fixedSubgroup _ _).mp x.property)
        change t * (x : G) * t⁻¹ = (x : G) at hx
        exact ((mul_inv_eq_iff_eq_mul).mp hx).symm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨hle, ?_, ?_⟩
  · exact h.setup.component.2.1.comap φ
  · let := h.setup.component.quasisimple
    let : IsQuasisimple (L.subgroupOf I) := IsQuasisimple.of_mulEquiv
      (subgroupOfEquivOfLe h.proper.le).symm
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hle).symm

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
