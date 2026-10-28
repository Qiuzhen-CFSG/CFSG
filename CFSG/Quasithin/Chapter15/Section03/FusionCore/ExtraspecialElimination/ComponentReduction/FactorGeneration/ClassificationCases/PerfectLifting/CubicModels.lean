module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting.Models
public import Theory.SpecificGroups.NoncentralCubic.Exceptional

/-!
# Cubic witnesses for every perfect FF model

Each B.5.6 constructor supplies a genuine multiplicative equivalence. Transport
of the concrete noncentral cubic through that equivalence proves the exact
witness used to exclude a component from M via theta(M ∩ H) = Y₀. SL₃ and PSL₃
use separate matrix theorems; the latter uses the actual central quotient.

These witnesses need no additional quasisimplicity, order, or simplicity
certification. The companion `CubicModels.ComponentApplication` applies them
to the existing component-commutator lemmas. Final component generation and
kernel absorption remain with the local source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6,
printed p.105, and the proof of 15.3.49(i), printed pp.1143–1144.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.NoncentralCubic
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting
variable {X : Type*} [Group X]

/-- Every actual single perfect actor has a noncentral element of order three. -/
theorem PerfectActorModel.exists_noncentral_cubic (h : PerfectActorModel X) :
    ∃ x : X, orderOf x = 3 ∧ x ∉ center X := by
  cases h with
  | @linear_two F _ _ _ n _ _ e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_projectiveSpecialLinear F (by decide : 2 ≤ 2))
  | @linear_three F _ _ _ n _ _ e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_specialLinear F (by decide : 2 ≤ 3))
  | @symplectic_four F _ _ _ n _ _ e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_symplecticFour F)
  | @g2 F _ _ _ n _ _ e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_g2 F)
  | alternating_six e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_alternating 6 (Or.inl rfl))
  | alternating_seven e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_alternating 7 (Or.inr rfl))
  | triple_cover e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      exists_noncentral_cubic_hexacode
  | g2_derived e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      exists_noncentral_cubic_g2Derived
  | binary_linear n hn _ e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_projectiveSpecialLinear (ZMod 2) (by omega : 2 ≤ n))

/-- Each actual perfect factor in the product catalogue has the required cubic. -/
theorem PerfectFactorModel.exists_noncentral_cubic (h : PerfectFactorModel X) :
    ∃ x : X, orderOf x = 3 ∧ x ∉ center X := by
  cases h with
  | @linear_two F _ _ _ n _ _ e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_projectiveSpecialLinear F (by decide : 2 ≤ 2))
  | @linear_three F _ _ _ n _ _ _ e =>
    obtain ⟨e⟩ := e
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_projectiveSpecialLinear F (by decide : 2 ≤ 3))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting
