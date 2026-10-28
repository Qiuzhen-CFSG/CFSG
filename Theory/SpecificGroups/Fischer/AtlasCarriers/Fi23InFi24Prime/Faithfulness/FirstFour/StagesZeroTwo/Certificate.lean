module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.FixedPoints
public import Theory.GroupAction.GeneratorStabilizerReduction
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Positive Schreier tables for the first two model stages

The next subgroup fixes the relevant point by the four concrete computations
in `FixedPoints`. Positive transitions suffice: a permutation of a finite set
has finite order, so iterating its positive transitions gives inverse steps.
No numerical generator order, orbit size, or subgroup order is assumed.

The remaining table obligations are genuine equalities in the full symmetric
group and separation of the base-returning representatives. They cannot be
replaced by equalities on the smaller orbit. `PositiveTable.certificate`
feeds the existing `reduction_of_certificate` consumer.

Source: Schreier rewriting for the ATLAS F24G1-p306936B0 model; GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo

/-- Every element of the proposed first stabilizer fixes the actual first point. -/
theorem stage_one_fixes (g : Equiv.Perm (Fin 306936)) (hg : g ∈ stage 1) :
    g (point 0) = point 0 := by
  have hle : stage 1 ≤ MulAction.stabilizer (Equiv.Perm (Fin 306936)) (point 0) := by
    have he : Subgroup.closure (Set.range (generators 1)) = stage 1 := stage_generated 1
    rw [← he]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    change generators 1 a (point 0) = point 0
    rw [point_zero]
    fin_cases a
    · exact word5_fixes_508
    · exact word8_fixes_508
  exact hle hg

/-- Every element of the proposed second stabilizer fixes the actual second point. -/
theorem stage_two_fixes (g : Equiv.Perm (Fin 306936)) (hg : g ∈ stage 2) :
    g (point 1) = point 1 := by
  have hle : stage 2 ≤ MulAction.stabilizer (Equiv.Perm (Fin 306936)) (point 1) := by
    have he : Subgroup.closure (Set.range (generators 2)) = stage 2 := stage_generated 2
    rw [← he]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    change generators 2 a (point 1) = point 1
    rw [point_one]
    fin_cases a
    · exact word11_fixes_509
    · exact word14_fixes_509
  exact hle hg

/-- The `next_fixes` field for both literal stages, with no certificate premise. -/
theorem next_fixes (i : Fin 2) (g : Equiv.Perm (Fin 306936))
    (hg : g ∈ stage (i.castAdd 2).succ) :
    g (point (i.castAdd 2)) = point (i.castAdd 2) := by
  fin_cases i
  · exact stage_one_fixes g hg
  · exact stage_two_fixes g hg

/-- Data still needed for a first-half Schreier reduction. In particular, `step`
is equality on all 306936 ambient letters, with a factor in the literal next
word-generated subgroup. The type of indices is unrestricted. -/
structure PositiveTable (i : Fin 2) (I : Type*) where
  representative : I → Equiv.Perm (Fin 306936)
  initial : I
  initial_eq : representative initial = 1
  step : ∀ a j, ∃ k, ∃ h : stage (i.castAdd 2).succ,
    generators (i.castAdd 2) a * representative j = representative k * h.val
  returns_base : ∀ j, representative j (point (i.castAdd 2)) = point (i.castAdd 2) →
    representative j = 1

private theorem PositiveTable.power_step {i : Fin 2} {I : Type*}
    (C : PositiveTable i I) (a : Fin 2) (n : Nat) (j : I) :
    ∃ k, ∃ h : stage (i.castAdd 2).succ,
      generators (i.castAdd 2) a ^ n * C.representative j = C.representative k * h.val := by
  induction n with
  | zero => exact ⟨j, 1, by simp⟩
  | succ n ih =>
    obtain ⟨k, h, he⟩ := ih
    obtain ⟨l, h', he'⟩ := C.step a k
    refine ⟨l, h' * h, ?_⟩
    change generators (i.castAdd 2) a ^ (n + 1) * C.representative j =
      C.representative l * (h'.val * h.val)
    rw [pow_succ', mul_assoc, he, ← mul_assoc, he', mul_assoc]

/-- Positive transitions provide the inverse transitions without checking a
second table or requiring the transition map to be a permutation. -/
def PositiveTable.certificate {i : Fin 2} {I : Type*} (C : PositiveTable i I) :
    Subgroup.GeneratorStabilizerReduction (generators (i.castAdd 2))
      (stage (i.castAdd 2).succ) (point (i.castAdd 2)) I where
  representative := C.representative
  initial := C.initial
  initial_eq := C.initial_eq
  step := C.step
  inv_step a j := by
    obtain ⟨n, hn, he⟩ := (isOfFinOrder_of_finite (generators (i.castAdd 2) a)).exists_pow_eq_one
    have hi : generators (i.castAdd 2) a ^ (n - 1) = (generators (i.castAdd 2) a)⁻¹ := by
      have hm : generators (i.castAdd 2) a ^ (n - 1) * generators (i.castAdd 2) a =
          (generators (i.castAdd 2) a)⁻¹ * generators (i.castAdd 2) a := by
        rw [pow_sub_one_mul (Nat.ne_of_gt hn), he, inv_mul_cancel]
      exact mul_right_cancel hm
    simpa only [hi] using C.power_step a (n - 1) j
  next_fixes h := next_fixes i h.val h.property
  returns_base := C.returns_base

/-- Application to the exact word-generated model subgroups. -/
theorem PositiveTable.reduction {i : Fin 2} {I : Type*} (C : PositiveTable i I)
    (g : Equiv.Perm (Fin 306936)) (hg : g ∈ stage (i.castAdd 2).castSucc)
    (hfix : g (point (i.castAdd 2)) = point (i.castAdd 2)) :
    g ∈ stage (i.castAdd 2).succ :=
  reduction_of_certificate C.certificate g hg hfix

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo
