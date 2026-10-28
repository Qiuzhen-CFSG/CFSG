module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-!
# Eight relative Weyl representatives

The involution and fourth-power relations give the right multiplication
table of the eight dihedral words. No injectivity of these representatives
is assumed. These algebraic identities are used in the presentation's
Bruhat induction (Steinberg, Lectures on Chevalley Groups, Lemmas 22–25).
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation

/-- The eight relative Weyl words; s marks the plane and t the point. -/
inductive WeylWord
  | one | s | t | st | ts | sts | tst | longest
  deriving DecidableEq

namespace WeylWord
variable {G : Type*}
def eval [Monoid G] (s t : G) : WeylWord → G
  | .one => 1
  | .s => s
  | .t => t
  | .st => s*t
  | .ts => t*s
  | .sts => s*t*s
  | .tst => t*s*t
  | .longest => s*t*s*t

def rightS : WeylWord → WeylWord
  | .one => .s | .s => .one | .t => .ts | .st => .sts
  | .ts => .t | .sts => .st | .tst => .longest | .longest => .tst

def rightT : WeylWord → WeylWord
  | .one => .t | .s => .st | .t => .one | .st => .s
  | .ts => .tst | .sts => .longest | .tst => .ts | .longest => .sts

@[simp] theorem rightS_rightS (w : WeylWord) : w.rightS.rightS=w := by cases w <;> rfl
@[simp] theorem rightT_rightT (w : WeylWord) : w.rightT.rightT=w := by cases w <;> rfl

theorem braid [Group G] {s t : G} (hs : s*s=1) (ht : t*t=1) (hst : (s*t)^4=1) :
    s*t*s*t=t*s*t*s := by
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left hs
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left ht
  apply mul_inv_eq_one.mp
  simpa only [mul_inv_rev,hsi,hti,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hst

theorem eval_rightS [Group G] {s t : G} (hs : s*s=1) (ht : t*t=1) (hst : (s*t)^4=1)
    (w : WeylWord) : w.rightS.eval s t=w.eval s t*s := by
  have hb := braid hs ht hst
  cases w <;> simp only [rightS,eval,one_mul]
  · exact hs.symm
  · simp only [mul_assoc,hs,mul_one]
  · simp only [mul_assoc,hs,mul_one]
  · exact hb
  · rw [hb]
    simp only [mul_assoc,hs,mul_one]

theorem eval_rightT [Group G] {s t : G} (ht : t*t=1) (w : WeylWord) :
    w.rightT.eval s t=w.eval s t*t := by
  cases w <;> simp [rightT,eval,mul_assoc,ht]
theorem map_eval [Monoid G] {M : Type*} [Monoid M] (f : G →* M) (s t : G) (w : WeylWord) :
    f (w.eval s t)=w.eval (f s) (f t) := by
  cases w <;> simp only [eval,map_one,map_mul]
end WeylWord
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
