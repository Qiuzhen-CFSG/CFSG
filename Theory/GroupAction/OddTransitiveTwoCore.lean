module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Trivial two-core in a faithful transitive odd-degree action

A normal two-group has a fixed point on an odd set. Normality and
transitivity make every point fixed, and faithfulness makes the group
trivial. This is used on the nine-root action in Aschbacher--Smith F.5.4(4).
-/

public section
open Subgroup
namespace MonoidHom
variable {G X : Type*} [Group G]

theorem twoCore_eq_bot_of_transitive_odd (f : G →* Equiv.Perm X)
    (hf : Function.Injective f) (hodd : ¬ 2 ∣ Nat.card X)
    (ht : ∀ x y : X, ∃ g : G, f g x = y) : pCore 2 G = ⊥ := by
  let : MulAction G X := MulAction.compHom X f
  obtain ⟨x,hx⟩ := (pCore_isPGroup (p := 2) (G := G)).nonempty_fixed_point_of_prime_not_dvd_card X hodd
  apply bot_unique
  intro a ha
  change a = 1
  apply hf
  apply Equiv.ext
  intro y
  obtain ⟨g,hg⟩ := ht x y
  have hy : y ∈ MulAction.fixedPoints (pCore 2 G) X := by
    rw [← hg]
    exact smul_mem_fixedPoints_of_normal g hx
  simpa only [map_one,Equiv.Perm.one_apply] using (show f a y = y from hy ⟨a,ha⟩)

end MonoidHom
