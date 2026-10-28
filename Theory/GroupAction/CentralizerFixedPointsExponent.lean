module

public import Theory.GroupAction.CentralizerFixedPoints
public import Mathlib.GroupTheory.PGroup

/-!
# Exponent two in a centralizer fixed-point kernel

Suppose a faithful permutation action preserves a Boolean relation. If its
restrictions to the fixed points of an involution distinguish points up to
that involution, every element of the centralizer's fixed-point kernel fixes
or interchanges each two-point orbit. Commutation with the involution then
shows that each kernel element has square one, so the kernel is a 2-group.

This elementary criterion supports the concrete Fi22 calculation associated
with GLS3 Table 5.3t, without any centralizer identification or order assumption.
-/

public section

namespace Theory.GroupAction.CentralizerFixedPoints
variable {G X : Type*} [Group G]

/-- A centralizer kernel has exponent two if an invariant relation distinguishes
points up to the orbits of the central involution using its fixed points. -/
theorem isPGroup_two_of_separating_relation
    (ρ : G →* Equiv.Perm X) (hρ : Function.Injective ρ) (t : G)
    (ht : t ^ 2 = 1) (R : X → X → Bool)
    (hinv : ∀ (g : G) (x y : X), R (ρ g x) (ρ g y) = R x y)
    (hsep : ∀ x y : X, (∀ f : Points ρ t, R x f.val = R y f.val) →
      y = x ∨ y = ρ t x) :
    IsPGroup 2 (action ρ t).ker := by
  intro g
  refine ⟨1, ?_⟩
  suffices hg : g.val.val ^ 2 = (1 : G) by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hg
  apply hρ
  rw [map_pow, map_one]
  apply Equiv.ext
  intro x
  have hfix (f : Points ρ t) : ρ g.val.val f.val = f.val := by
    have h := congrArg (fun p : Equiv.Perm (Points ρ t) => (p f).val) g.property
    simpa only [action_apply, Equiv.Perm.one_apply] using h
  have horbit (y : X) : ρ g.val.val y = y ∨ ρ g.val.val y = ρ t y := by
    apply hsep y (ρ g.val.val y)
    intro f
    simpa only [hfix] using (hinv g.val.val y f.val).symm
  have hcomm (y : X) : ρ g.val.val (ρ t y) = ρ t (ρ g.val.val y) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp g.val.property
    simpa only [map_mul, Equiv.Perm.mul_apply] using
      congrArg (fun a : G => ρ a y) h
  change ρ g.val.val (ρ g.val.val x) = x
  rcases horbit x with hx | hx
  · rw [hx, hx]
  · rw [hx, hcomm, hx]
    have h := congrArg (fun a : G => ρ a x) ht
    simpa only [map_pow, pow_two, map_mul, map_one, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply] using h
end Theory.GroupAction.CentralizerFixedPoints
