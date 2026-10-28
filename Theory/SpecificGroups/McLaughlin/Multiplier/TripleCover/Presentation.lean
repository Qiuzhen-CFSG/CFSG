module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Marked words for the McLaughlin triple-cover construction

These are the fifteen relators in the ATLAS file `McLG1-P1.M`, including
its three redundant relators. The commutator convention in that file is
`x⁻¹ * y⁻¹ * x * y`. The target of `base` is the existing degree-275
permutation-generated carrier, with its existing left-action convention.

The map `base` is proved surjective from generation. Equality of its kernel
with the normal closure of these relators is deliberately not asserted here:
that is the presentation-completeness obligation for the construction.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/McLG1-P1 .
The original presentation and candidate lift matrices are retained in `source/`.
The application is the lower bound in Aschbacher–Smith I.1.4(2), p.408.
-/

@[expose] public section

namespace Theory.SpecificGroups.McLaughlin.Multiplier.TripleCover

abbrev Word := FreeGroup Bool

def a : Word := FreeGroup.of false
def b : Word := FreeGroup.of true

/-- ATLAS uses the inverse-first commutator convention. -/
def atlasCommutator {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- The literal ATLAS presentation, including R0, R1 and R2. -/
def relatorList : List Word :=
  [a ^ 2,
   b ^ 5,
   (atlasCommutator a b) ^ 5,
   (a * b) ^ 11,
   (a * b ^ 2) ^ 12,
   (atlasCommutator a (b ^ 2)) ^ 6,
   (a * b * a * b ^ (-2 : ℤ)) ^ 7,
   (atlasCommutator a (b ^ (-2 : ℤ) * a * b * a * b * a * b ^ 2)) ^ 2,
   atlasCommutator a
     (b ^ (-2 : ℤ) * a * b ^ 2 * a * b⁻¹ * a * b * (a * b ^ 2) ^ 2 * a * b * a * b⁻¹),
   (atlasCommutator a (b * (a * b ^ 2) ^ 3)) ^ 2,
   (atlasCommutator a (b ^ 2 * a * b * (a * b ^ 2) ^ 2)) ^ 2,
   a * b * a * b ^ 2 * a * b ^ (-2 : ℤ) * a * b * a * b⁻¹ * a * b ^ 2 *
     (a * b ^ (-2 : ℤ) * a * b) ^ 2 * (a * b ^ 2 * a * b ^ (-2 : ℤ) * a * b ^ 2) ^ 2,
   (atlasCommutator a (b ^ 2 * a * b ^ 2 * a * b⁻¹ * a * b ^ 2)) ^ 2,
   (atlasCommutator a (b ^ 2 * a * b)) ^ 4,
   (atlasCommutator a (b ^ 2 * a * b ^ 2)) ^ 4]

def relators : Set Word := {w | w ∈ relatorList}

/-- Evaluation preserves the ordered pair of standard generators. -/
def evaluate {H : Type*} [Group H] (A B : H) : Word →* H :=
  FreeGroup.lift (fun i => if i then B else A)

@[simp] theorem evaluate_a {H : Type*} [Group H] (A B : H) : evaluate A B a = A := by
  simp [evaluate, a]

@[simp] theorem evaluate_b {H : Type*} [Group H] (A B : H) : evaluate A B b = B := by
  simp [evaluate, b]

/-- Word evaluation on the literal degree-275 permutations. -/
def permutationEvaluation : Word →* Equiv.Perm (Fin 275) :=
  evaluate Sporadic.LeechRelated.McL.generatorA Sporadic.LeechRelated.McL.generatorB

theorem permutationEvaluation_range :
    permutationEvaluation.range = Sporadic.LeechRelated.McL.generated := by
  rw [permutationEvaluation, evaluate, FreeGroup.range_lift_eq_closure]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

/-- The literal word evaluation into the existing permutation carrier. -/
def base : Word →* Sporadic.LeechRelated.McL.Carrier :=
  permutationEvaluation.codRestrict _ (fun w => by
    rw [← permutationEvaluation_range]
    exact ⟨w, rfl⟩)

theorem base_surjective : Function.Surjective base := by
  intro x
  have hx : x.val ∈ permutationEvaluation.range := by
    rw [permutationEvaluation_range]
    exact x.property
  obtain ⟨w, hw⟩ := hx
  exact ⟨w, Subtype.ext hw⟩

end Theory.SpecificGroups.McLaughlin.Multiplier.TripleCover
