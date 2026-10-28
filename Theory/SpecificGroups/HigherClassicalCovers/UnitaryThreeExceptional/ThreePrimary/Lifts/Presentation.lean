module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.RootMatrices
public import Mathlib.GroupTheory.PresentedGroup

/-!
# A finite presentation map for the positive unitary subgroup

The six coordinate roots satisfy their cubic relations and fifteen descending
collection relations. Their presentation therefore maps to the literal positive
subgroup under the fixed coordinate projection. Bijectivity is a separate
normal-form obligation; no presentation equivalence is assumed as an instance.

Source: the antidiagonal SU₄(3) coordinates for Aschbacher--Smith I.1.4(5),
printed p.408, and the exceptional multiplier calculation cited in GLS3 §6.1.
-/
@[expose] public noncomputable section
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts

theorem rootSU_swap (i j : Fin 6) (hij : i < j) :
    rootSU j * rootSU i = rootSU i * rootSU j * swapTail rootSU i j := by
  apply Subtype.ext
  apply Units.ext
  let f : CoordinateSU →* Mat :=
    (Units.coeHom Mat).comp coordinateForm.specialSubgroup.subtype
  change f (rootSU j * rootSU i) = f (rootSU i * rootSU j * swapTail rootSU i j)
  rw [map_mul, map_mul, map_mul, map_swapTail]
  change rootMatrix j * rootMatrix i = rootMatrix i * rootMatrix j * swapTail rootMatrix i j
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> decide +kernel


/-- The descending swap relation, with its precise matrix-checked tail. -/
def swapRelator (i j : Fin 6) : FreeGroup (Fin 6) :=
  FreeGroup.of j * FreeGroup.of i *
    (FreeGroup.of i * FreeGroup.of j * swapTail FreeGroup.of i j)⁻¹

/-- Six cubes and the fifteen descending collection relations. -/
def relators : Set (FreeGroup (Fin 6)) :=
  Set.range (fun i : Fin 6 => FreeGroup.of i ^ 3) ∪
    {w | ∃ i j : Fin 6, i < j ∧ w = swapRelator i j}

abbrev Presentation := PresentedGroup relators

theorem root_swap (i j : Fin 6) (hij : i < j) :
    root j * root i = root i * root j * swapTail root i j := by
  unfold root
  simpa only [map_mul, map_swapTail] using
    congrArg coordinateProjection (rootSU_swap i j hij)

/-- Each generator lies in the literal marked positive subgroup. -/
def positiveRoot (r : Fin 6) : positive := ⟨root r, root_mem_positive r⟩

theorem positiveRoot_cube (r : Fin 6) : positiveRoot r ^ 3 = 1 :=
  Subtype.ext (root_cube r)

theorem positiveRoot_swap (i j : Fin 6) (hij : i < j) :
    positiveRoot j * positiveRoot i =
      positiveRoot i * positiveRoot j * swapTail positiveRoot i j := by
  apply Subtype.ext
  change root j * root i = root i * root j * positive.subtype (swapTail positiveRoot i j)
  rw [map_swapTail]
  exact root_swap i j hij

/-- The finite relations suffice to evaluate the presentation in any group. -/
theorem relators_vanish {H : Type*} [Group H] (x : Fin 6 → H)
    (hc : ∀ i, x i ^ 3 = 1)
    (hs : ∀ i j : Fin 6, i < j → x j * x i = x i * x j * swapTail x i j) :
    ∀ w ∈ relators, FreeGroup.lift x w = 1 := by
  intro w hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · simpa only [map_pow, FreeGroup.lift_apply_of] using hc i
  · simp only [swapRelator, map_mul, map_inv, FreeGroup.lift_apply_of, map_swapTail]
    rw [hs i j hij, mul_inv_cancel]

/-- The marked presentation homomorphism; normal-form completeness is not asserted here. -/
def presentationProjection : Presentation →* positive :=
  PresentedGroup.toGroup (relators_vanish positiveRoot positiveRoot_cube positiveRoot_swap)

theorem presentationProjection_of (r : Fin 6) :
    presentationProjection (PresentedGroup.of r) = positiveRoot r :=
  PresentedGroup.toGroup.of _

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
