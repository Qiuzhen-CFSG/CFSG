module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.FieldModel
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.SignedCoordinates
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The original anisotropic parameter in the quadratic coefficient field

An isomorphism from the original field to the actual Frobenius fixed field
supplies the coefficient embedding. The polynomial X² + X − parameter F is
irreducible by the definition of the original minus form. Its degree-two
root field embeds over F into GF(p^(2n)). Frobenius exchanges the two roots,
so the chosen root has conjugate −1−α and nonzero skew coordinate 2α+1.

This supplies the field and root data for the signed exterior realization
used in the dimension-six reduction of Aschbacher–Smith A.2.17, printed
pp.38–39; see also GLS3 §2.7. The parameter is never reselected after
passing to the fixed field.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison.Geometry
open Polynomial
variable (p n : ℕ) [Fact p.Prime] [NeZero n]
variable (F : Type) [Field F] [Finite F] (hcard : Nat.card F = p ^ n)

def coefficientEquiv : F ≃+* fixedField p n := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (fixedField p n) := Fintype.ofFinite _
  apply FiniteField.ringEquivOfCardEq
  simpa only [← Nat.card_eq_fintype_card] using hcard.trans (card_fixedField p n).symm

def coefficient : F →+* Extension p n :=
  (fixedField p n).subtype.comp (coefficientEquiv p n F hcard).toRingHom

theorem coefficient_fixed (x : F) :
    conjugation p n (coefficient p n F hcard x) = coefficient p n F hcard x :=
  (coefficientEquiv p n F hcard x).property

theorem exists_coefficient (x : Extension p n) (hx : conjugation p n x = x) :
    ∃ c : F, coefficient p n F hcard c = x := by
  obtain ⟨c, hc⟩ := (coefficientEquiv p n F hcard).surjective ⟨x, hx⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem exists_root : ∃ α : Extension p n,
    α ^ 2 + α = coefficient p n F hcard (parameter F) := by
  let ι := coefficient p n F hcard
  let : Algebra F (Extension p n) := ι.toAlgebra
  have hfin : Module.finrank F (Extension p n) = 2 := by
    apply Nat.pow_right_injective (by
      rw [← hcard]
      exact Finite.one_lt_card : 1 < p ^ n)
    change (p ^ n) ^ Module.finrank F (Extension p n) = (p ^ n) ^ 2
    rw [← hcard, ← Module.natCard_eq_pow_finrank, card_extension, hcard]
  let P : F[X] := X ^ 2 + X - C (parameter F)
  have hd : P.natDegree = 2 := by
    dsimp [P]
    rw [natDegree_sub_C, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp
  have hi : Irreducible P := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · simp [hd]
    · intro x hx
      apply parameter_spec F x
      simpa [P, IsRoot, sub_eq_zero] using hx
  let : Fact (Irreducible P) := ⟨hi⟩
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := F) (K := AdjoinRoot P) (L := Extension p n) (by
      rw [(AdjoinRoot.powerBasis hi.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hd, hfin])
  refine ⟨e (AdjoinRoot.root P), ?_⟩
  have h := AdjoinRoot.aeval_algHom_eq_zero P e
  simpa only [P, map_sub, map_add, map_pow, aeval_X, aeval_C, sub_eq_zero, RingHom.algebraMap_toAlgebra] using h

def root : Extension p n := (exists_root p n F hcard).choose

theorem root_equation : (root p n F hcard) ^ 2 + root p n F hcard =
    coefficient p n F hcard (parameter F) := (exists_root p n F hcard).choose_spec

theorem root_not_fixed : conjugation p n (root p n F hcard) ≠ root p n F hcard := by
  intro h
  obtain ⟨c, hc⟩ := exists_coefficient p n F hcard _ h
  apply parameter_spec F c
  apply (coefficient p n F hcard).injective
  simpa only [map_add, map_pow, hc] using root_equation p n F hcard

theorem root_conjugate : conjugation p n (root p n F hcard) = -1 - root p n F hcard := by
  have hr := root_equation p n F hcard
  have hc := congrArg (conjugation p n) hr
  simp only [map_add, map_pow, coefficient_fixed] at hc
  have hm : (conjugation p n (root p n F hcard) - root p n F hcard) *
      (conjugation p n (root p n F hcard) + root p n F hcard + 1) = 0 := by
    linear_combination hc - hr
  have hs := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr (root_not_fixed p n F hcard))
  linear_combination hs

theorem skew_ne_zero : 2 * root p n F hcard + 1 ≠ 0 := by
  intro h
  apply root_not_fixed p n F hcard
  rw [root_conjugate]
  linear_combination -h

end ClassicalOrthogonal.Minus.OddSixComparison.Geometry
