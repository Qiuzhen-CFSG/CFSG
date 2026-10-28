module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Basic
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# Four sporadic exclusions in the field-component sieve

M₁₁ and M₁₂ have order prime to seven; J₁ has order not divisible by nine.
For M₂₃ every automorphism is inner, and every involution centralizer has a
proved self-centralizing normal two-subgroup. It therefore has no ordinary
component, despite having a PSL₃(2) quotient.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137; the complete
sporadic list in Theorem C(5), printed p.33; GLS3 Table 5.3d for M₂₃.
-/

public section

open Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

universe u
variable {S : Type u} [Group S] (s : SimpleInput S)
include s

/-- M₁₁ cannot contain the retained PSL₃(2) component. -/
theorem SimpleInput.not_m11 : ¬ Nonempty (S ≃* M11) := by
  rintro ⟨e⟩
  have h := s.seven_dvd_card
  rw [Nat.card_congr e.toEquiv, m11_order] at h
  norm_num at h

/-- M₁₂ cannot contain the retained PSL₃(2) component. -/
theorem SimpleInput.not_m12 : ¬ Nonempty (S ≃* M12) := by
  rintro ⟨e⟩
  have h := s.seven_dvd_card
  rw [Nat.card_congr e.toEquiv, m12_order] at h
  norm_num at h

/-- The rank-two hypothesis rules out J₁ before any centralizer analysis. -/
theorem SimpleInput.not_j1 [Finite S] : ¬ Nonempty (S ≃* Janko1.Model) := by
  rintro ⟨e⟩
  have h := s.nine_dvd_card
  rw [Nat.card_congr e.toEquiv, Janko1.card_model] at h
  norm_num at h

/-- M₂₃ has a PSL₃(2) section in its fixed subgroup but no ordinary component. -/
theorem SimpleInput.not_m23 : ¬ Nonempty (S ≃* M23) := by
  rintro ⟨e⟩
  obtain ⟨a, ha, D, hD, _⟩ := s.fixed_component_of_equiv e
  exact M23Geometry.InvolutionCentralizer.fixedSubgroup_no_component_of_inner
    a ha (m23_involution_automorphism_inner a ha) D hD

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
