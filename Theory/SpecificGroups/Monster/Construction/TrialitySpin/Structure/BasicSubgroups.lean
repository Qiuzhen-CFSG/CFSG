module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.AxisOrbits
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.SignKernel
public import Mathlib.Data.Set.Card

/-!
# Elementary subgroup facts for the Parker triality action

All loop generators and the first standard-automorphism family centralize `z1`.
Consequently `Q1` and `K` lie in the source centralizer `N1`. The explicit
coordinate actions of `k1`, `k2`, and `k3` give the multiplication table and
prove that `K` has exactly four elements.

The source normal-form words are defined in `N1`, with factors reversed to
respect Lean's left-composition convention. Their existence and uniqueness as
normal forms require further theorems; those properties are not part of the
definitions.

Source: Aschbacher, *Sporadic Groups*, Lemmas 14.3–14.4, pp. 60–62, and
Lemma 14.6, pp. 62–63.
-/

@[expose] public section
noncomputable section

open Atlas.Fischer Atlas.Codes
namespace Sporadic.Monster.Construction.TrialitySpin

@[simp] theorem signZero_leftZero (d : ParkerLoop) (a : LoopZero) :
    signZero (leftZero d a) = leftZero d (signZero a) := by
  cases a with
  | none => rfl
  | some a => simp [parkerLoopMultiply_sign_right]

@[simp] theorem signZero_rightZero (d : ParkerLoop) (a : LoopZero) :
    signZero (rightZero d a) = rightZero d (signZero a) := by
  cases a with
  | none => rfl
  | some a => simp [parkerLoopMultiply_sign_left]

@[simp] theorem signZero_inverseZero (a : LoopZero) :
    signZero (inverseZero a) = inverseZero (signZero a) := by
  cases a with
  | none => rfl
  | some a => simp [loopInverse_sign]

@[simp] theorem signZero_optionMap (e : ParkerStandardGroup) (a : LoopZero) :
    signZero (a.map e.val) = (signZero a).map e.val := by
  cases a with
  | none => rfl
  | some a => simpa using congrArg some (parkerStandard_preserves_sign e 1 a).symm

theorem psi1N_mem_N1 (d : ParkerLoop) : psi1N d ∈ N1 := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi1 d (z1 (a,b,c)) = z1 (psi1 d (a,b,c))
  simp

theorem psi2N_mem_N1 (d : ParkerLoop) : psi2N d ∈ N1 := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi2 d (z1 (a,b,c)) = z1 (psi2 d (a,b,c))
  simp

theorem psi3N_mem_N1 (d : ParkerLoop) : psi3N d ∈ N1 := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi3 d (z1 (a,b,c)) = z1 (psi3 d (a,b,c))
  simp

/-- Standard automorphism generators inside the fixed generated group. -/
def psiAut1N (e : ParkerStandardGroup) : N := ⟨psiAut1 e.val, psiAut1_mem_N e.val e.prop⟩
def psiAut2N (e : ParkerStandardGroup) : N := ⟨psiAut2 e.val, psiAut2_mem_N e.val e.prop⟩
def psiAut3N (e : ParkerStandardGroup) : N := ⟨psiAut3 e.val, psiAut3_mem_N e.val e.prop⟩

theorem psiAut1N_mem_N1 (e : ParkerStandardGroup) : psiAut1N e ∈ N1 := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psiAut1 e.val (z1 (a,b,c)) = z1 (psiAut1 e.val (a,b,c))
  by_cases he : e.val parkerOmega = parkerOmega
  · simp [psiAut1,he,diagonal]
  · simp [psiAut1,he,diagonal,flip1]

theorem Q1_le_N1 : Q1 ≤ N1 := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨d,rfl⟩ | ⟨e,he,hg⟩)
  · exact psi1N_mem_N1 d
  · have hg' : g = psiAut1N ⟨e,he.1⟩ := Subtype.ext hg
    rw [hg']
    exact psiAut1N_mem_N1 _

theorem K_le_N1 : K ≤ N1 := by
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl | rfl | rfl)
  · exact N1.mul_mem (psi2N_mem_N1 _) (psi3N_mem_N1 _)
  · exact N1.mul_mem (psi3N_mem_N1 _) (psi1N_mem_N1 _)
  · exact N1.mul_mem (psi1N_mem_N1 _) (psi2N_mem_N1 _)

theorem k2_apply (a b c : LoopZero) :
    k2.val (a,b,c) =
      (rightZero (parkerSign 1 parkerOmega) a, signZero b, rightZero parkerOmega c) := by
  change psi3 (parkerSign 1 parkerOmega) (psi1 parkerOmega (a,b,c)) = _
  simp only [psi1_apply, psi3_apply, loopInverse_omega, loopInverse_signOmega,
    omega_sandwich, omega_mixed_sandwich, signOmega_commutes_zero,
    rightSignOmega_rightSignOmega]

theorem k3_apply (a b c : LoopZero) :
    k3.val (a,b,c) =
      (rightZero parkerOmega a, rightZero (parkerSign 1 parkerOmega) b, signZero c) := by
  change psi1 (parkerSign 1 parkerOmega) (psi2 parkerOmega (a,b,c)) = _
  simp only [psi1_apply, psi2_apply, loopInverse_omega, loopInverse_signOmega,
    omega_sandwich, omega_mixed_sandwich, signOmega_commutes_zero,
    rightSignOmega_rightSignOmega]

@[simp] theorem rightSignOmega_eq (a : LoopZero) :
    rightZero (parkerSign 1 parkerOmega) a = signZero (rightZero parkerOmega a) := by
  cases a with
  | none => rfl
  | some a => simp [parkerLoopMultiply_sign_right]

theorem k2_sq : k2 ^ 2 = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change k2.val (k2.val (a,b,c)) = (a,b,c)
  simp only [k2_apply, signZero_signZero, rightOmega_rightOmega,
    rightSignOmega_rightSignOmega]

theorem k3_sq : k3 ^ 2 = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change k3.val (k3.val (a,b,c)) = (a,b,c)
  simp only [k3_apply, signZero_signZero, rightOmega_rightOmega,
    rightSignOmega_rightSignOmega]

theorem k1_mul_k2 : k1 * k2 = k3 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change k1.val (k2.val (a,b,c)) = k3.val (a,b,c)
  simp [k1_apply,k2_apply,k3_apply]

theorem k2_mul_k1 : k2 * k1 = k3 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change k2.val (k1.val (a,b,c)) = k3.val (a,b,c)
  simp [k1_apply,k2_apply,k3_apply]

theorem k1_k2_k3 : k1 * k2 * k3 = 1 := by
  rw [k1_mul_k2, ← pow_two, k3_sq]

theorem k1_ne_one : k1 ≠ 1 := by
  intro h
  have he := congrArg (fun g : N => g.val (axis1 loopOne)) h
  have he' : parkerSign 1 loopOne = loopOne := by
    simpa [axis1,k1_apply] using he
  exact parkerSign_one_ne loopOne he'

theorem k2_ne_one : k2 ≠ 1 := by
  intro h
  have he := congrArg (fun g : N => g.val (axis2 loopOne)) h
  have he' : parkerSign 1 loopOne = loopOne := by
    simpa [axis2,k2_apply] using he
  exact parkerSign_one_ne loopOne he'

theorem k3_ne_one : k3 ≠ 1 := by
  intro h
  have he := congrArg (fun g : N => g.val (axis3 loopOne)) h
  have he' : parkerSign 1 loopOne = loopOne := by
    simpa [axis3,k3_apply] using he
  exact parkerSign_one_ne loopOne he'

theorem k1_ne_k2 : k1 ≠ k2 := by
  intro h
  have : k3 = 1 := by rw [← k1_mul_k2, h, ← pow_two,k2_sq]
  exact k3_ne_one this

theorem k1_ne_k3 : k1 ≠ k3 := by
  intro h
  have : k1 * k2 = k1 * 1 := by rw [k1_mul_k2, ← h, mul_one]
  exact k2_ne_one (mul_left_cancel this)

theorem k2_ne_k3 : k2 ≠ k3 := by
  intro h
  have : k2 * k1 = k2 * 1 := by rw [k2_mul_k1, ← h, mul_one]
  exact k1_ne_one (mul_left_cancel this)

private theorem kernel_four_closed {x y : N}
    (hx : x = 1 ∨ x = k1 ∨ x = k2 ∨ x = k3)
    (hy : y = 1 ∨ y = k1 ∨ y = k2 ∨ y = k3) :
    x * y = 1 ∨ x * y = k1 ∨ x * y = k2 ∨ x * y = k3 := by
  have h1 : k1*k1=1 := by simpa only [pow_two] using k1_sq
  have h2 : k2*k2=1 := by simpa only [pow_two] using k2_sq
  have h3 : k3*k3=1 := by simpa only [pow_two] using k3_sq
  have h13 : k1*k3=k2 := by rw [← k1_mul_k2,← mul_assoc,h1,one_mul]
  have h23 : k2*k3=k1 := by rw [← k2_mul_k1,← mul_assoc,h2,one_mul]
  have h31 : k3*k1=k2 := by rw [← k2_mul_k1,mul_assoc,h1,mul_one]
  have h32 : k3*k2=k1 := by rw [← k1_mul_k2,mul_assoc,h2,mul_one]
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    simp [h1,h2,h3,k1_mul_k2,k2_mul_k1,h13,h23,h31,h32]

theorem mem_K_iff (g : N) : g ∈ K ↔ g = 1 ∨ g = k1 ∨ g = k2 ∨ g = k3 := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl | rfl <;> simp
    | one => simp
    | mul x y hx hy ihx ihy => exact kernel_four_closed ihx ihy
    | inv x hx ihx =>
      have h1 : k1⁻¹=k1 := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using k1_sq)
      have h2 : k2⁻¹=k2 := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using k2_sq)
      have h3 : k3⁻¹=k3 := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using k3_sq)
      rcases ihx with rfl | rfl | rfl | rfl <;> simp [h1,h2,h3]
  · rintro (rfl | rfl | rfl | rfl)
    · exact K.one_mem
    all_goals apply Subgroup.subset_closure; simp

theorem K_card : Nat.card K = 4 := by
  classical
  have he : (K : Set N) = {1,k1,k2,k3} := by ext; simp [mem_K_iff]
  change Nat.card (K : Set N) = 4
  rw [he, Nat.card_coe_set_eq]
  simp [k1_ne_k2,k1_ne_k3,k2_ne_k3,
    Ne.symm k1_ne_one, Ne.symm k2_ne_one, Ne.symm k3_ne_one]

/-- The cyclic subgroup killed in the extraspecial quotient of `Q1`. -/
def K1 : Subgroup N := Subgroup.zpowers k1

/-- The subgroup generated by the two elements killed in the quadratic quotient. -/
def Q1CentralKernel : Subgroup N := Subgroup.closure {z1N, k1}

/-- The two-generator subgroup in the source orbit-kernel statement. -/
def J : Subgroup N :=
  Subgroup.closure {psi2N (parkerSign 1 parkerOmega), psi3N parkerOmega}

theorem K1_le_K : K1 ≤ K :=
  Subgroup.zpowers_le.mpr ((mem_K_iff k1).mpr (by simp))

theorem K1_card : Nat.card K1 = 2 := by
  rw [K1, Nat.card_zpowers]
  exact orderOf_eq_prime k1_sq k1_ne_one

theorem K1_le_J : K1 ≤ J := by
  apply Subgroup.zpowers_le.mpr
  exact J.mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

theorem J_le_N1 : J ≤ N1 := by
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl | rfl)
  · exact psi2N_mem_N1 _
  · exact psi3N_mem_N1 _

/-- A source normal-form word, translated from right to left composition. -/
def normalForm (d e : ParkerLoop) (α : ParkerStandardGroup) : N1 :=
  ⟨psiAut1N α * psi2N e * psi1N d,
    N1.mul_mem (N1.mul_mem (psiAut1N_mem_N1 α) (psi2N_mem_N1 e)) (psi1N_mem_N1 d)⟩

/-- The specialized normal-form words for the first local 2-subgroup. -/
def q1Word (d : ParkerLoop) (t : ParkerBit) (c : Cocode) : N1 :=
  normalForm d (0, t) (parkerCocodeStandard c)

end Sporadic.Monster.Construction.TrialitySpin
