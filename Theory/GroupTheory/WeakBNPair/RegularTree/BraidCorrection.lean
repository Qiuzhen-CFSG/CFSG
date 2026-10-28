module
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# The cubic rank-one calculation behind apartment exchange

Two involutions whose product has order three satisfy the braid relation.
If their braid word differs from a half-apartment reflection by an element
of a local kernel, that correction centralizes both involutions: conjugation
preserves each root, and the roots meet the kernel trivially. A trivial
correction gives the exchange actor; otherwise the correction is a concrete
nonidentity common centralizer element. Normality is relative to the actual
actors, not asserted in the whole completion.

Source: DGS, *Groups and Graphs* (1985), Part II, the characteristic-two
calculation in (14.12), printed pp.217--218. This is the local inference;
constructing its small rank-one pairs remains a source obligation.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V]

/-- The cubic relation of two involutions implies the braid relation. -/
theorem braid_of_involutions_cube (x y : X) (hx : x*x=1) (hy : y*y=1)
    (hc : (x*y)^3=1) : x*y*x=y*x*y := by
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹=y := inv_eq_of_mul_eq_one_right hy
  have he : (x*y*x)*(y*x*y)=1 := by
    calc
      _ = (x*y)^3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hc
  calc
    _ = (y*x*y)⁻¹ := eq_inv_of_mul_eq_one_left he
    _ = y*x*y := by simp only [mul_inv_rev, hxi, hyi, mul_assoc]

/-- The braid word interchanges the two generating involutions. -/
theorem braid_conjugates (x y : X) (hx : x*x=1) (hy : y*y=1)
    (hb : x*y*x=y*x*y) :
    (x*y*x)⁻¹*x*(x*y*x)=y ∧ (x*y*x)⁻¹*y*(x*y*x)=x := by
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹=y := inv_eq_of_mul_eq_one_right hy
  have hxx (z : X) : x*(x*z)=z := by rw [← mul_assoc, hx, one_mul]
  have hyy (z : X) : y*(y*z)=z := by rw [← mul_assoc, hy, one_mul]
  constructor
  · calc
      _ = (x*y*x)*y*x := by simp only [mul_inv_rev, hxi, hyi, mul_assoc, hxx]
      _ = (y*x*y)*y*x := by rw [hb]
      _ = y := by simp only [mul_assoc, hyy, hx, mul_one]
  · calc
      _ = (y*x*y)⁻¹*y*(y*x*y) := by rw [hb]
      _ = (y*x*y)*x*y := by simp only [mul_inv_rev, hxi, hyi, mul_assoc, hyy]
      _ = (x*y*x)*x*y := by rw [← hb]
      _ = x := by simp only [mul_assoc, hxx, hy, mul_one]

/-- A kernel element preserving a root element centralizes it when the root embeds in the local quotient. -/
theorem commute_of_root_kernel (R Q : Subgroup X) (hRQ : R ⊓ Q = ⊥)
    {x h : X} (hx : x∈R) (hxn : x∈Subgroup.normalizer (Q : Set X))
    (hh : h∈Q) (hconj : h⁻¹*x*h∈R) : Commute x h := by
  have hm : x⁻¹*h⁻¹*x*h ∈ R ⊓ Q := by
    constructor
    · change x⁻¹*h⁻¹*x*h ∈ R
      simpa only [mul_assoc] using R.mul_mem (R.inv_mem hx) hconj
    · have hn := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Q : Set X)).inv_mem hxn) h⁻¹).mp (Q.inv_mem hh)
      simp only [inv_inv] at hn
      exact Q.mul_mem hn hh
  rw [hRQ] at hm
  have he : h⁻¹*x*h=x := by
    have hh' := congrArg (x * ·) (show x⁻¹*h⁻¹*x*h=1 from hm)
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using hh'
  show x*h=h*x
  have hh' := congrArg (h * ·) he
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh'

/-- The discrepancy between the braid word and the chosen reflection centralizes both roots. -/
theorem braid_correction_centralizes (R S Q : Subgroup X)
    (hRQ : R ⊓ Q = ⊥) (hSQ : S ⊓ Q = ⊥)
    {x y t : X} (hxR : x∈R) (hyS : y∈S)
    (hxn : x∈Subgroup.normalizer (Q : Set X))
    (hyn : y∈Subgroup.normalizer (Q : Set X))
    (hx : x*x=1) (hy : y*y=1) (hb : x*y*x=y*x*y)
    (hty : t*y*t⁻¹∈R) (htx : t*x*t⁻¹∈S)
    (hQ : (x*y*x)*t⁻¹∈Q) :
    Commute x ((x*y*x)*t⁻¹) ∧ Commute y ((x*y*x)*t⁻¹) := by
  have hw := braid_conjugates x y hx hy hb
  constructor
  · apply commute_of_root_kernel R Q hRQ hxR hxn hQ
    have he : ((x*y*x)*t⁻¹)⁻¹*x*((x*y*x)*t⁻¹) = t*y*t⁻¹ := by
      calc
        _ = t*((x*y*x)⁻¹*x*(x*y*x))*t⁻¹ := by group
        _ = t*y*t⁻¹ := by rw [hw.1]
    rwa [he]
  · apply commute_of_root_kernel S Q hSQ hyS hyn hQ
    have he : ((x*y*x)*t⁻¹)⁻¹*y*((x*y*x)*t⁻¹) = t*x*t⁻¹ := by
      calc
        _ = t*((x*y*x)⁻¹*y*(x*y*x))*t⁻¹ := by group
        _ = t*x*t⁻¹ := by rw [hw.2]
    rwa [he]

/-- The correction either supplies the exchange equation or witnesses a nontrivial common centralizer in the kernel. -/
theorem braid_exchange_or_centralizer (R S Q : Subgroup X)
    (hRQ : R ⊓ Q = ⊥) (hSQ : S ⊓ Q = ⊥)
    {x y t : X} (hxR : x∈R) (hyS : y∈S)
    (hxn : x∈Subgroup.normalizer (Q : Set X))
    (hyn : y∈Subgroup.normalizer (Q : Set X))
    (hx : x*x=1) (hy : y*y=1) (hb : x*y*x=y*x*y)
    (hty : t*y*t⁻¹∈R) (htx : t*x*t⁻¹∈S)
    (hQ : (x*y*x)*t⁻¹∈Q) {a b : V}
    (ht : t • a=b) (hxb : x • b=b) :
    y • (x • a)=b ∨ ∃ h∈Q, h≠1 ∧ Commute x h ∧ Commute y h := by
  classical
  by_cases he : (x*y*x)*t⁻¹=1
  · left
    have hw : x*y*x=t := mul_inv_eq_one.mp he
    calc
      y • (x • a) = (y*x) • a := (mul_smul _ _ _).symm
      _ = (x*t) • a := by
        congr 1
        rw [← hw]
        simp only [← mul_assoc, hx, one_mul]
      _ = b := by rw [mul_smul, ht, hxb]
  · exact Or.inr ⟨_, hQ, he,
      braid_correction_centralizes R S Q hRQ hSQ hxR hyS hxn hyn hx hy hb hty htx hQ⟩

end Theory.GroupTheory.WeakBNPair.RegularTree
