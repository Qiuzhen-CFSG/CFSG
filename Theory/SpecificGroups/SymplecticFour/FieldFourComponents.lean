module

public import Theory.SpecificGroups.SymplecticFour.FieldFourOddCore
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# No components in Sylow-central fixed groups of Sp₄(4)

The proved semilinear classification and pointwise Sylow calculation make
each such involution inner. The trivial center preserves the conjugator's
order. Its centralizer has self-centralizing two-core, so has no component.

Source: Aschbacher–Smith, the E.6.8 model inspection in E.6.22, printed p.254.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- No extra automorphism-coverage or centralizer premise is required. -/
theorem fieldFour_sylow_fixed_no_component (hF : Nat.card F = 4)
    (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)) (ha : orderOf a = 2)
    (hfix : ∀ x ∈ (S : Subgroup (Sp F)), a x = x)
    (D : Subgroup a.fixedSubgroup) : ¬ IsComponent a.fixedSubgroup D := by
  obtain ⟨z, _, hz⟩ := DiagramAutomorphisms.aut_fixing_sylow_inner
    (n := 2) hF (by decide)
    DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram S a hfix
  have hz2 : orderOf z = 2 := by
    rw [hz, MulAut.conj_orderOf_of_center_eq_bot EvenProjective.center_eq_bot] at ha
    exact ha
  have hcore := FieldFourOddCore.centralizer_selfCentralizing_core hF S z hz2
    (fun x hx => hz ▸ hfix x hx)
  have he : a.fixedSubgroup = centralizer ({z} : Set (Sp F)) := by
    rw [hz, MulAut.fixedSubgroup_conj]
  have hcore' : centralizer (pCore 2 a.fixedSubgroup : Set a.fixedSubgroup) ≤
      pCore 2 a.fixedSubgroup := he.symm ▸ hcore
  exact not_isComponent_of_twoCore hcore' D

end Theory.SpecificGroups.SymplecticFour
