module

public import Theory.SpecificGroups.ReeTwo.CoreFrame
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Algebra of the four semilinear orbit words

Six commutators of four involutions determine the squares and commutators
of the candidate Ree frame. In a class-two group with involutory commutators,
bilinearity reduces these identities to cancellation in the center. The
pairing with the derived roots is trivial in this quotient.

This module proves only the word calculation; establishing its six input
commutators from intrinsic group hypotheses is a separate obligation.
The words and root convention follow Shinoda (1975), (2.3), pp.81–82.
-/

@[expose] public section
namespace ReeTwo
/-- The six orbit commutators, expressed in the four root displacements.
This is a calculation target, not an intrinsic hypothesis on a Ree extension. -/
structure OrbitCommutatorCoordinates {H : Type*} [Group H]
    (u : Fin 4 → H) (t : H) : Prop where
  comm01 : rightComm (u 0) (u 1) = rightComm (u 0) t * rightComm (u 1) t * rightComm (u 3) t
  comm02 : rightComm (u 0) (u 2) = rightComm (u 0) t * rightComm (u 1) t * rightComm (u 2) t
  comm03 : rightComm (u 0) (u 3) = rightComm (u 1) t * rightComm (u 2) t
  comm12 : rightComm (u 1) (u 2) = rightComm (u 0) t * rightComm (u 3) t
  comm13 : rightComm (u 1) (u 3) = rightComm (u 1) t * rightComm (u 2) t * rightComm (u 3) t
  comm23 : rightComm (u 2) (u 3) = rightComm (u 0) t * rightComm (u 2) t * rightComm (u 3) t

/-- Evaluate the sixteen binary words in a four-element family. -/
def binaryWord4 {H : Type*} [Group H] (d : Fin 4 → H) (e : Fin 4 → Fin 2) : H :=
  d 0 ^ (e 0).val * d 1 ^ (e 1).val * d 2 ^ (e 2).val * d 3 ^ (e 3).val
open Subgroup
open scoped IsMulCommutative
variable {H : Type*} [Group H]
variable (hc : ∀ x y : H, rightComm x y ∈ center H)
variable (he : ∀ x y : H, rightComm x y * rightComm x y = 1)
private def c (x y : H) : center H := ⟨rightComm x y, hc x y⟩
private theorem c_left (x y w : H) : c hc (x*y) w = c hc x w * c hc y w := by
  apply Subtype.ext
  change rightComm (x*y) w = rightComm x w * rightComm y w
  have hh := mem_center_iff.mp (hc x w) y
  calc
    _ = y⁻¹ * rightComm x w * y * rightComm y w := by simp [rightComm, mul_assoc]
    _ = _ := by rw [mul_assoc y⁻¹, ← hh]; simp
private theorem c_right (x y w : H) : c hc x (y*w) = c hc x y * c hc x w := by
  apply Subtype.ext
  change rightComm x (y*w) = rightComm x y * rightComm x w
  have hh := mem_center_iff.mp (hc x y) w
  calc
    _ = rightComm x w * (w⁻¹ * rightComm x y * w) := by simp [rightComm, mul_assoc]
    _ = rightComm x w * rightComm x y := by rw [mul_assoc w⁻¹, ← hh]; simp
    _ = _ := mem_center_iff.mp (hc x y) _
private theorem c_self (x : H) : c hc x x = 1 := by
  apply Subtype.ext
  simp [c, rightComm]
include he
private theorem c_symm (x y : H) : c hc x y = c hc y x := by
  apply Subtype.ext
  change rightComm x y = rightComm y x
  have hi : (rightComm x y)⁻¹ = rightComm x y := inv_eq_of_mul_eq_one_right (he x y)
  rw [← hi]
  simp [rightComm, mul_assoc]
private theorem c_cancel (x y : H) (w : center H) : c hc x y * (c hc x y * w) = w := by
  rw [← mul_assoc, show c hc x y * c hc x y = 1 from Subtype.ext (he x y), one_mul]
private theorem square_mul (x y : H) :
    (x*y)*(x*y) = (x*x)*(y*y)*(c hc x y : H) := by
  have hswap : y*x = x*y*rightComm y x := by simp [rightComm, mul_assoc]
  have hh := mem_center_iff.mp (hc y x) y
  calc
    _ = x*(y*x)*y := by group
    _ = x*(x*y*rightComm y x)*y := by rw [hswap]
    _ = (x*x)*(y*y)*rightComm y x := by
      simp only [mul_assoc]
      rw [← hh]
    _ = _ := by rw [← show rightComm x y = rightComm y x from congrArg Subtype.val (c_symm hc he x y)]; rfl

set_option linter.unusedSimpArgs false in
private theorem frame_of_commutators (u : Fin 4 → H) (t : H)
    (hu : ∀ i, u i * u i = 1) (ht : t*t = 1)
    (h01 : c hc (u 0) (u 1) = c hc (u 0) t * c hc (u 1) t * c hc (u 3) t)
    (h02 : c hc (u 0) (u 2) = c hc (u 0) t * c hc (u 1) t * c hc (u 2) t)
    (h03 : c hc (u 0) (u 3) = c hc (u 1) t * c hc (u 2) t)
    (h12 : c hc (u 1) (u 2) = c hc (u 0) t * c hc (u 3) t)
    (h13 : c hc (u 1) (u 3) = c hc (u 1) t * c hc (u 2) t * c hc (u 3) t)
    (h23 : c hc (u 2) (u 3) = c hc (u 0) t * c hc (u 2) t * c hc (u 3) t) :
    FrameCoordinates ![u 0, u 2*u 3*t, u 1*u 2*t, u 0*u 1*u 2*u 3] t 1 := by
  have h10 := (c_symm hc he (u 1) (u 0)).trans h01
  have h20 := (c_symm hc he (u 2) (u 0)).trans h02
  have h30 := (c_symm hc he (u 3) (u 0)).trans h03
  have h21 := (c_symm hc he (u 2) (u 1)).trans h12
  have h31 := (c_symm hc he (u 3) (u 1)).trans h13
  have h32 := (c_symm hc he (u 3) (u 2)).trans h23
  have hti (i : Fin 4) := c_symm hc he t (u i)
  have cs (x y : H) : c hc x y * c hc x y = 1 := Subtype.ext (he x y)
  have cr (x y : H) : rightComm x y = (c hc x y : H) := rfl
  have hz (x : H) (w : center H) : rightComm x w = 1 := by
    have hh := mem_center_iff.mp w.property x
    calc
      _ = (w*x)⁻¹*(x*w) := by simp [rightComm, mul_assoc]
      _ = 1 := by rw [hh, inv_mul_cancel]
  constructor
  · intro i
    fin_cases i <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, frameTail, square_mul hc he, hu, ht, one_mul, mul_one,
        cr, c_left, c_right, hti, c_self, h01, h02, h03, h12, h13, h23,
        mul_one, one_mul, ← Subgroup.coe_mul (H := center H), ← Subgroup.coe_one (H := center H)] <;>
      apply congrArg (fun w : center H => (w : H)) <;>
      try simp only [mul_assoc, mul_left_comm, mul_comm, c_cancel hc he, cs, mul_one, one_mul]
  case pairing =>
    intro i j
    simp only [ite_self]
    apply hz _ ⟨_, ?_⟩
    fin_cases j <;> exact hc _ _
  all_goals
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, frameTail, cr, c_left, c_right, hti, c_self,
      h01, h02, h03, h12, h13, h23, h10, h20, h30, h21, h31, h32,
      mul_one, one_mul, ← Subgroup.coe_mul (H := center H), ← Subgroup.coe_one (H := center H)]
  all_goals { apply congrArg (fun w : center H => (w : H)); simp only [mul_assoc, mul_left_comm, mul_comm, c_cancel hc he, cs,
    mul_one, one_mul] }
omit hc he in

/-- In a class-two group with involutory commutators, the orbit commutator
calculation yields all the required quotient frame relations. -/
theorem frameCoordinates_of_orbitCommutators
    (hc : ∀ x y : H, rightComm x y ∈ center H)
    (he : ∀ x y : H, rightComm x y * rightComm x y = 1)
    (u : Fin 4 → H) (t : H) (hu : ∀ i, u i * u i = 1) (ht : t*t = 1)
    (h : OrbitCommutatorCoordinates u t) :
    FrameCoordinates ![u 0, u 2*u 3*t, u 1*u 2*t, u 0*u 1*u 2*u 3] t 1 := by
  apply frame_of_commutators hc he u t hu ht
  · exact Subtype.ext h.comm01
  · exact Subtype.ext h.comm02
  · exact Subtype.ext h.comm03
  · exact Subtype.ext h.comm12
  · exact Subtype.ext h.comm13
  · exact Subtype.ext h.comm23

end ReeTwo

namespace ReeTwo
open Subgroup
open scoped commutatorElement
variable {K : Type*} [Group K]
private theorem rc_mem (x y : K) : rightComm x y ∈ commutator K := by
  simpa [rightComm, commutatorElement_def, _root_.commutator_def] using
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x⁻¹) (Subgroup.mem_top y⁻¹))
/-- If the derived subgroup is elementary and central modulo the center,
all commutators of the central quotient are central involutions. -/
theorem centralQuotient_rightComm_laws (D : Subgroup K) [IsElementaryAbelian 2 D]
    (hD : commutator K ≤ D) (hc : ⁅D, (⊤ : Subgroup K)⁆ ≤ center K) :
    (∀ x y : K ⧸ center K, rightComm x y ∈ center (K ⧸ center K)) ∧
    (∀ x y : K ⧸ center K, rightComm x y * rightComm x y = 1) := by
  let q := QuotientGroup.mk' (center K)
  have hm (x y : K) : q (rightComm x y) = rightComm (q x) (q y) := by
    simp [rightComm]
  constructor
  · intro x y
    induction x using QuotientGroup.induction_on with | H x =>
      induction y using QuotientGroup.induction_on with | H y =>
        change rightComm (q x) (q y) ∈ center (K ⧸ center K)
        rw [← hm]
        apply Subgroup.mem_center_iff.mpr
        intro w
        induction w using QuotientGroup.induction_on with | H w =>
          apply commutatorElement_eq_one_iff_mul_comm.mp
          change ⁅q w, q (rightComm x y)⁆ = 1
          rw [← map_commutatorElement]
          apply (QuotientGroup.eq_one_iff _).mpr
          apply hc
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator (mem_top w) (hD (rc_mem x y))
  · intro x y
    induction x using QuotientGroup.induction_on with | H x =>
      induction y using QuotientGroup.induction_on with | H y =>
        change rightComm (q x) (q y) * rightComm (q x) (q y) = 1
        rw [← hm, ← map_mul]
        have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2)
          (rightComm x y) (hD (rc_mem x y))
        rw [pow_two] at hh
        rw [hh, map_one]
end ReeTwo
