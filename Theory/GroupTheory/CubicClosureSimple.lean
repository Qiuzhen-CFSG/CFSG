module

public import Theory.GroupTheory.CubicClosureTwoKernel
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.IsPerfect

/-!
# Cubic generation in a simple group

In a finite simple group whose order is divisible by three, the elements
of order three generate the group. Their generated subgroup is normal
and Cauchy's theorem makes it nontrivial. If the simple group is also
perfect, this cubic closure is not solvable.

The source application is the SL₄(2) quotient of the actual centralizer
residual in Aschbacher--Smith 15.2.23, printed p.1117. Together with
cubic-closure transport through a two-group kernel, it excludes that
section inside a group with solvable cubic closure.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- A nontrivial cubic conjugacy class generates a finite simple group. -/
theorem cubic_closure_eq_top_of_simple (hd : 3 ∣ Nat.card G) :
    closure {x : G | orderOf x = 3} = ⊤ := by
  let C := closure {x : G | orderOf x = 3}
  have hn : (⊤ : Subgroup G) ≤ normalizer (C : Set G) := by
    apply le_normalizer_closure_iff.mpr
    intro g _ x hx
    exact subset_closure ((MulAut.conj g).orderOf_eq x |>.trans hx)
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  rcases (inferInstance : C.Normal).eq_bot_or_eq_top with hb | ht
  · obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
    have hm : x ∈ C := subset_closure hx
    rw [hb,mem_bot] at hm
    simp [hm] at hx
  · exact ht

/-- The cubic closure of a perfect simple group with three dividing its
order cannot be solvable. -/
theorem cubic_closure_not_solvable_of_simple [Group.IsPerfect G]
    (hd : 3 ∣ Nat.card G) :
    ¬ Group.IsSolvable (closure {x : G | orderOf x = 3}) := by
  rw [cubic_closure_eq_top_of_simple hd]
  intro hs
  let := hs
  have hg : Group.IsSolvable G := Group.isSolvable_of_surjective
    (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) topEquiv.surjective
  exact Group.IsPerfect.not_isSolvable G hg

end Theory.GroupTheory
