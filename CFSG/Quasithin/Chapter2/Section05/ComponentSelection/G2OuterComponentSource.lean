module
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.OuterComponents
/-!
# The outer G₂ fixed-component row in original 2.5.19

The marked involution and its ordinary fixed component determine an actual
smaller binary coefficient field. The fixed group is full G₂ of that field;
the given component and its literal center quotient are the derived G₂ model.
This discharges the model-descent input of the containing-component census.
The original source proof still supplies the ordinary-component assertion and
uses its surviving smaller models for the final exclusions.

Source: Aschbacher--Smith 2.5.19, printed pp.562--563. The binary endpoint
retains G₂(2)′ for the component and full G₂(2) for the whole fixed group.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Atlas.G2 Atlas.G2.EvenFieldFixedResidual
/-- The G₂ outer-action row of original 2.5.19 for the actual fixed component.
The surrounding source proof supplies ordinary componenthood; no smaller-field
model, component quotient, or conjugator is assumed here. -/
theorem g2_outer_fixed_component
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card F = 2 ^ n) (a : MulAut (Model F)) (ha : orderOf a = 2)
    (hout : ∀ g : Model F, a ≠ MulAut.conj g)
    (D : Subgroup a.fixedSubgroup) (hD : IsComponent a.fixedSubgroup D) :
    ∃ (σ : F ≃+* F) (m : ℕ), 0 < m ∧ m < n ∧ n = 2 * m ∧
      Nat.card (fixedField σ) = 2 ^ m ∧ orderOf σ = 2 ∧
      (∃ c : Model F, a =
        MulAut.conj c * LieAutomorphismExtensions.fieldAction σ * (MulAut.conj c)⁻¹) ∧
      ∃ E : a.fixedSubgroup ≃* Model (fixedField σ),
        D.map E.toMonoidHom = commutator (Model (fixedField σ)) ∧
        center D = ⊥ ∧ Nonempty (D ≃* commutator (Model (fixedField σ))) ∧
        Nonempty ((D ⧸ center D) ≃* commutator (Model (fixedField σ))) := by
  have he : MulAut.congr (MulEquiv.refl (Model F)) a = a := by ext g; rfl
  simpa only [he] using outer_fixed_component_descent_of_equiv
    (MulEquiv.refl (Model F)) hn hc a ha hout D hD
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
