module
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Central automorphisms from binary characters

A character into the cyclic group of order two, vanishing on a central
involution `z`, defines the involutory automorphism `x ↦ z^(χ x) * x`.
The displacement is central and squares to one; vanishing on `z` makes the
same formula its own inverse. The outer M₁₂ endpoint uses two such characters.
-/
@[expose] public section
namespace Theory.GroupTheory.CentralInvolutionTwist
abbrev C2 := Multiplicative (ZMod 2)
variable {G : Type*} [Group G]

theorem c2_cases (q : C2) : q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  have h : ∀ q : C2, q = 1 ∨ q = Multiplicative.ofAdd 1 := by decide +kernel
  exact h q

def powerHom (z : G) (hz : z * z = 1) : C2 →* G where
  toFun q := z ^ q.toAdd.val
  map_one' := by change z ^ 0 = 1; exact pow_zero z
  map_mul' q r := by
    rcases c2_cases q with rfl | rfl <;> rcases c2_cases r with rfl | rfl
    · change z ^ 0 = z ^ 0 * z ^ 0
      simp only [pow_zero, one_mul]
    · change z ^ 1 = z ^ 0 * z ^ 1
      simp only [pow_zero, one_mul]
    · change z ^ 1 = z ^ 1 * z ^ 0
      simp only [pow_zero, mul_one]
    · change z ^ 0 = z ^ 1 * z ^ 1
      simp only [pow_zero, pow_one, hz]

/-- An involutory central displacement gives an actual automorphism. -/
def ofDisplacement (f : G →* G) (hc : ∀ x, f x ∈ Subgroup.center G)
    (hff : ∀ x, f (f x) = 1) (hsq : ∀ x, f x * f x = 1) : MulAut G where
  toFun x := f x * x
  invFun x := f x * x
  left_inv x := by
    change f (f x * x) * (f x * x) = x
    rw [map_mul, hff, one_mul, ← mul_assoc, hsq, one_mul]
  right_inv x := by
    change f (f x * x) * (f x * x) = x
    rw [map_mul, hff, one_mul, ← mul_assoc, hsq, one_mul]
  map_mul' x y := by
    rw [map_mul]
    calc
      f x * f y * (x * y) = f x * (f y * x) * y := by simp only [mul_assoc]
      _ = f x * (x * f y) * y := by rw [(Subgroup.mem_center_iff.mp (hc y) x).symm]
      _ = (f x * x) * (f y * y) := by simp only [mul_assoc]

/-- Twist by a binary character that kills the central involution. -/
def ofCharacter (z : G) (hz : z * z = 1) (hc : z ∈ Subgroup.center G)
    (χ : G →* C2) (hχ : χ z = 1) : MulAut G :=
  ofDisplacement ((powerHom z hz).comp χ)
    (fun x => (Subgroup.center G).pow_mem hc _)
    (by
      intro x
      change powerHom z hz (χ (z ^ (χ x).toAdd.val)) = 1
      rw [map_pow, hχ, one_pow, map_one])
    (by
      intro x
      change powerHom z hz (χ x) * powerHom z hz (χ x) = 1
      rw [← map_mul]
      have h : ∀ q : C2, q * q = 1 := by decide +kernel
      rw [h, map_one])

theorem ofCharacter_apply (z : G) (hz : z * z = 1) (hc : z ∈ Subgroup.center G)
    (χ : G →* C2) (hχ : χ z = 1) (x : G) :
    ofCharacter z hz hc χ hχ x = z ^ (χ x).toAdd.val * x := rfl
end Theory.GroupTheory.CentralInvolutionTwist
