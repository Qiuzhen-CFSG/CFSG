module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.UniqueInvolution

/-!
# A normal cyclic four inside a normal group with a unique involution

A normal subgroup `C` of a finite two-group, of order at least four and
with a unique involution, contains a cyclic subgroup of order four normal
in the entire two-group. First choose a normal subgroup of order four
using the normal p-subgroup chain theorem. It is abelian by its order,
and is cyclic because it inherits uniqueness of involutions from `C`.

This gives the normal cyclic subgroup used by Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined 1 March 2004 manuscript,
p.569, immediately after Lemma 2.5.27. Normality is in the specified
two-group; it is not asserted in any larger ambient group.
-/

namespace IsPGroup

open Subgroup

/-- A normal rank-one two-subgroup of order at least four contains a cyclic
four normal in the given two-group. Uniqueness is expressed on actual
elements of `C`; no classification conclusion or invariant subgroup is assumed. -/
public theorem exists_normal_cyclicFour_of_unique_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (C : Subgroup P) [C.Normal] (hcard : 4 ≤ Nat.card C)
    (hunique : ∀ x y : C, orderOf x = 2 → orderOf y = 2 → x = y) :
    ∃ V : Subgroup P, V.Normal ∧ V ≤ C ∧
      Nonempty (V ≃* Multiplicative (ZMod 4)) := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  obtain ⟨n, hn⟩ := (hP.to_subgroup C).exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 0 ∨ n = 1 := by omega
    rw [hn] at hcard
    rcases this with rfl | rfl <;> norm_num at hcard
  obtain ⟨V, hVn, hVC, hVcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal C inferInstance hn 2 hn2
  let i : V →* C := inclusion hVC
  have hi : Function.Injective i := inclusion_injective hVC
  have hvunique : ∀ x y : V, orderOf x = 2 → orderOf y = 2 → x = y := by
    intro x y hx hy
    apply hi
    exact hunique _ _ ((orderOf_injective i hi x).trans hx)
      ((orderOf_injective i hi y).trans hy)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 (by rw [hVcard]; decide)
  let : IsMulCommutative V := IsPGroup.isMulCommutative_of_card_eq_prime_sq hVcard
  let : IsCyclic V := (hP.to_subgroup V).isCyclic_of_unique_involution_of_isMulCommutative
    ⟨z, hz, fun y hy => hvunique y z hy hz⟩
  exact ⟨V, hVn, hVC, ⟨mulEquivOfCyclicCardEq (by simpa using hVcard)⟩⟩

end IsPGroup
