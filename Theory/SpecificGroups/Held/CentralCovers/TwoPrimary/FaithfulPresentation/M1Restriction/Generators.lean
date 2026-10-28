module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.Setup
import Mathlib.Tactic.FinCases

/-!
# The marked generators of the abstract and concrete M₁

The three generators are the literal words in John Bray's `HeG1-P1.M`.
Their concrete images generate precisely the range of `m1Map`. This fixes
the marking for independent abstract upper and concrete lower bounds; it
does not identify the abstract subgroup with its image.

Source: `Held/Model/Source/HeG1-P1.M`, with `x^g = g⁻¹*x*g`.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction

def liftedGenerator : Fin 3 → Presentation
  | 0 => x
  | 1 => (y ^ 2)⁻¹ * x * y ^ 2
  | 2 => y ^ 2 * x * (y ^ 2)⁻¹

theorem m1_eq_closure_range : m1 = Subgroup.closure (Set.range liftedGenerator) := by
  unfold m1
  congr 1
  ext g
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [liftedGenerator]

theorem liftedGenerator_mem (i : Fin 3) : liftedGenerator i ∈ m1 := by
  rw [m1_eq_closure_range]
  exact Subgroup.subset_closure ⟨i, rfl⟩

def concreteGenerator (i : Fin 3) : He := presentationMap (liftedGenerator i)

theorem concreteGenerator_eq (i : Fin 3) : concreteGenerator i =
    (match i with
      | 0 => a
      | 1 => (b ^ 2)⁻¹ * a * b ^ 2
      | 2 => b ^ 2 * a * (b ^ 2)⁻¹) := by
  fin_cases i <;>
    simp only [concreteGenerator, liftedGenerator, x, y, map_mul, map_pow, map_inv,
      presentationMap_of, generator]

def concreteSubgroup : Subgroup He := Subgroup.closure (Set.range concreteGenerator)

theorem m1Map_range : m1Map.range = concreteSubgroup := by
  have he : m1Map = presentationMap.comp m1.subtype := by
    apply MonoidHom.ext
    intro g
    exact m1Map_apply g
  rw [he, MonoidHom.range_comp, Subgroup.range_subtype, m1_eq_closure_range,
    MonoidHom.map_closure, ← Set.range_comp]
  rfl

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
