module
public import Theory.GroupTheory.Amalgam.RankTwo
public import Mathlib.Algebra.Group.End
/-!
# Compatible automorphisms of a marked rank-two amalgam

Compatible self-isomorphisms form a group by composing all three maps. The
multiplication convention agrees with the endpoint automorphism groups: the
right factor acts first. This preserves both marked inclusion squares and
supports the normal-base extension action in Goldschmidt (1980), (2.8).
-/

@[expose] public section
namespace Theory.GroupTheory.RankTwoAmalgam.Iso
variable {L D R L' D' R' : Type*} [Group L] [Group D] [Group R]
  [Group L'] [Group D'] [Group R']
  {α : RankTwoAmalgam L D R} {β : RankTwoAmalgam L' D' R'}

@[ext] theorem ext {e f : Iso α β} (hl : e.left = f.left)
    (hm : e.middle = f.middle) (hr : e.right = f.right) : e = f := by
  rcases e with ⟨⟨l,m,r⟩,hel,her⟩
  rcases f with ⟨⟨l',m',r'⟩,hfl,hfr⟩
  cases hl
  cases hm
  cases hr
  rfl

instance : Group (Iso α α) where
  mul e f := f.trans e
  one := Iso.refl α
  inv e := e.symm
  mul_assoc a b c := by
    apply ext <;> ext x <;> rfl
  one_mul a := by
    apply ext <;> ext x <;> rfl
  mul_one a := by
    apply ext <;> ext x <;> rfl
  inv_mul_cancel a := by
    apply ext <;> ext x
    · exact a.left.symm_apply_apply x
    · exact a.middle.symm_apply_apply x
    · exact a.right.symm_apply_apply x

@[simp] theorem mul_left (e f : Iso α α) : (e*f).left = e.left*f.left := rfl
@[simp] theorem mul_middle (e f : Iso α α) : (e*f).middle = e.middle*f.middle := rfl
@[simp] theorem mul_right (e f : Iso α α) : (e*f).right = e.right*f.right := rfl
@[simp] theorem one_left : (1 : Iso α α).left = 1 := rfl
@[simp] theorem one_middle : (1 : Iso α α).middle = 1 := rfl
@[simp] theorem one_right : (1 : Iso α α).right = 1 := rfl
@[simp] theorem inv_left (e : Iso α α) : e⁻¹.left = e.left⁻¹ := rfl
@[simp] theorem inv_middle (e : Iso α α) : e⁻¹.middle = e.middle⁻¹ := rfl
@[simp] theorem inv_right (e : Iso α α) : e⁻¹.right = e.right⁻¹ := rfl
end Theory.GroupTheory.RankTwoAmalgam.Iso
