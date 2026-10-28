module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.QuotientAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Transvections
public import Theory.GroupTheory.CComponent.Basic

/-!
# The solvable case has no nonidentity transvections

The universal implication in source 13.8.5(1) supplies a genuine
C-component of H when a nonidentity transvection occurs on U_H/V₁.
Such a component is nonsolvable, which excludes that action when H is
solvable. The source implication remains an explicit earlier input.
This does not yet transport the assertion to the other critical endpoint.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.5(1)
and the final five-primary argument in 13.8.13, printed pp.947 and 951.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]
variable [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]

/-- The C-component and generation consequences of 13.8.5(1).
The source product equality implies the join equality used here; this
predicate does not claim a converse or specify all of 13.8.5.
The nonidentity qualification excludes the identity transvection allowed
by Mathlib's definition. -/
def TransvectionComponentConclusion (a : StarAction H UH V₁) (T : Subgroup G) : Prop :=
  ∀ t : Source.Hstar H, a.action t ≠ 1 →
    CriticalGeometry.binaryLinear (a.action t) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (UH ⧸ V₁.subgroupOf UH)) →
    ∃ K : Subgroup H, K.IsCComponent ∧ H = K.map H.subtype ⊔ T

/-- In a solvable H the genuine 13.8.5(1) conclusion excludes every
nonidentity transvection on the literal tilde quotient. -/
theorem StarAction.eq_one_of_transvection_of_solvable
    (a : StarAction H UH V₁) (T : Subgroup G) (hs : Group.IsSolvable H)
    (h135 : TransvectionComponentConclusion a T) (t : Source.Hstar H)
    (ht : CriticalGeometry.binaryLinear (a.action t) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (UH ⧸ V₁.subgroupOf UH))) :
    a.action t = 1 := by
  by_contra hn
  obtain ⟨K, hK, _⟩ := h135 t hn ht
  let := hs
  exact hK.not_isSolvable inferInstance

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five

end
