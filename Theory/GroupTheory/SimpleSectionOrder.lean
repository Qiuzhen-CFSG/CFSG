module
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Mathlib.GroupTheory.Index

/-!
# Orders of simple quotients through solvable-kernel representations

A nonsolvable simple quotient survives removal of a solvable representation
kernel. Its order therefore divides the order of the concrete target, by
subgroup and quotient divisibility. Neither injectivity of the representation
nor a chosen family of models is assumed.
Source application: the parabolic inspection in Aschbacher--Smith 4.4.12,
printed pp.621--622.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.SimpleSection

/-- A solvable kernel cannot remove a nonsolvable simple quotient's order. -/
theorem card_dvd_of_solvable_representation
    {A S X : Type*} [Group A] [Group S] [IsSimpleGroup S] [Group X]
    (hS : ¬ Group.IsSolvable S) (π : A →* S) (hπ : Function.Surjective π)
    (r : A →* X) [Group.IsSolvable r.ker] : Nat.card S ∣ Nat.card X := by
  let m : Group.SolvableKernelModel A r.range := {
    kernel := r.ker
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := QuotientGroup.quotientKerEquivRange r }
  obtain ⟨U,f,hf⟩ := m.simple_section hS ⊤
    (π.comp (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
    (hπ.comp topEquiv.surjective)
  exact (card_dvd_of_surjective f hf).trans
    (U.card_subgroup_dvd_card.trans r.range.card_subgroup_dvd_card)


end Theory.GroupTheory.SimpleSection
