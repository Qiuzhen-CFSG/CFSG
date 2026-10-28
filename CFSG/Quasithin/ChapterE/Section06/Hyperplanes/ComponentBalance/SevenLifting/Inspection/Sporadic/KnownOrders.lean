module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
/-!
# The M₁₁, M₁₂, M₂₃ and J₁ cases of the seven inspection

The orders of M₁₁, M₁₂ and J₁ exclude an A₇ subgroup or perfect central
triple cover outright. For M₂₃ the proved full automorphism innerness and
involution fusion identify every involutory fixed subgroup with the concrete
centralizer of order 2688. The order obstruction then excludes a seven
subgroup in the common fixed subgroup of every nontrivial two-actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inspection
in E.6.18, printed p.252, and Theorem C, printed p.33. The concrete orders
and automorphism calculations are imported from their model developments.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
open Sporadic.Mathieu

/-- M₁₁ has no embedded seven subgroup, by its actual order. -/
theorem m11 : SevenActionInspection M11 := by
  apply of_card
  rw [m11_order]
  norm_num

/-- M₁₂ has no embedded seven subgroup, by its actual order. -/
theorem m12 : SevenActionInspection M12 := by
  apply of_card
  rw [m12_order]
  norm_num

/-- J₁ has no embedded seven subgroup, by its actual order. -/
theorem janko_one : SevenActionInspection Janko1.Model := by
  apply of_card
  rw [Janko1.card_model]
  norm_num

/-- The M₂₃ involution-centralizer calculation controls every two-actor. -/
theorem m23 : SevenActionInspection M23 := by
  apply of_involution_fixed_card
  intro r hr
  obtain ⟨e⟩ := M23Geometry.InvolutionCentralizer.fixedSubgroup_equiv_representative_of_inner
    r hr (m23_involution_automorphism_inner r hr)
  rw [Nat.card_congr e.toEquiv]
  change ¬ 2520 ∣ Nat.card (centralizer ({M23Geometry.involutionRepresentative} : Set M23))
  rw [M23Geometry.involutionRepresentative_centralizer_card]
  norm_num
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
