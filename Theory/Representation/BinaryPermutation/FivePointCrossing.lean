module
public import Theory.Representation.BinaryPermutation.FivePointCentralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic
/-!
The point-centralizer obstruction to two disjoint, nontrivial normal actors
on the binary five-point core. The original crossing argument uses C_S(L)
and V for these two actors. Every nonzero point of the first actor has
centralizer normalizing the second; the support-transposition bound then
contradicts their disjoint displacement spaces.
-/
public section
open Subgroup
open scoped commutatorElement
namespace BinaryPermutation.FivePointCore
open FiveCentralizerGeometry
variable {G : Type*} [Group G] (N : Subgroup G)
  (q : N →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
  (m : Multiplicative (core (Fin 5)) →* G) (hm : Function.Injective m)
  (he : ∀ (g : N) (x : core (Fin 5)),
    (g : G) * m (Multiplicative.ofAdd x) * (g : G)⁻¹ =
      m (Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g) x)))
include he
private theorem displacement_mem (A : Subgroup G)
    (hA : ⁅A,m.range⁆ ≤ A) (a : N) (ha : (a:G) ∈ A) (x : core (Fin 5)) :
    m (Multiplicative.ofAdd (coreRepresentation (Fin 5) (q a) x - x)) ∈ A := by
  rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,←he]
  exact hA (commutator_mem_commutator ha ⟨Multiplicative.ofAdd x,rfl⟩)
include hm hq

theorem no_disjoint_moving_actors (A B : Subgroup G)
    (hA : ⁅A,m.range⁆ ≤ A) (hB : ⁅B,m.range⁆ ≤ B)
    (hAB : Disjoint A B) (hBC : B ≤ centralizer (A : Set G))
    (hP : IsPGroup 2 B) (hBN : B ≤ N)
    (hcontrol : ∀ x ∈ A, x ≠ 1 → centralizer ({x} : Set G) ≤ normalizer (B : Set G))
    (a b : N) (ha : (a:G) ∈ A) (hb : (b:G) ∈ B)
    (haq : q a=Equiv.swap 0 1 ∨ q a=Equiv.swap 2 3 ∨ q a=Equiv.swap 0 1 * Equiv.swap 2 3)
    (hbq : q b=Equiv.swap 0 1 ∨ q b=Equiv.swap 2 3 ∨ q b=Equiv.swap 0 1 * Equiv.swap 2 3) : False := by
  have hd : ∀ x y : core (Fin 5),
      coreRepresentation (Fin 5) (q a) x - x = coreRepresentation (Fin 5) (q b) y - y →
      coreRepresentation (Fin 5) (q a) x - x = 0 := by
    intro x y hxy
    have hma := displacement_mem N q m he A hA a ha x
    have hmb := displacement_mem N q m he B hB b hb y
    rw [←hxy] at hmb
    have hh := disjoint_def.mp hAB hma hmb
    exact Multiplicative.ofAdd.injective (hm (hh.trans (map_one m).symm))
  rcases distinct_supports_of_disjoint_displacements (q a) (q b) haq hbq hd with h | h
  · let y : core (Fin 5) := ⟨![1,0,0,0,1],by rw [mem_core]; decide⟩
    have hy : coreRepresentation (Fin 5) (Equiv.swap 0 1) y - y = v := by decide +kernel
    have hx : m (Multiplicative.ofAdd v) ∈ A := by
      have hh := displacement_mem N q m he A hA a ha y
      rwa [h.1,hy] at hh
    have hxne : m (Multiplicative.ofAdd v) ≠ 1 := by
      intro hh
      exact v_ne_zero (Multiplicative.ofAdd.injective (hm (hh.trans (map_one m).symm)))
    have hbfix : B ≤ centralizer ({m (Multiplicative.ofAdd v)} : Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (hBC hb _ hx).symm
    have hbim := normal_two_point_image N q hq m hm he B hP hBN hbfix (hcontrol _ hx hxne)
    have ht := hbim (mem_map_of_mem q (show b ∈ B.subgroupOf N from hb))
    rw [h.2,mem_zpowers_iff_mem_range_orderOf] at ht
    rw [show orderOf (Equiv.swap (0:Fin 5) 1) = 2 from
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)] at ht
    rcases Finset.mem_image.mp ht with ⟨i,hi,heq⟩
    have hi2 : i < 2 := Finset.mem_range.mp hi
    interval_cases i <;> revert heq <;> decide +kernel
  · let y : core (Fin 5) := ⟨![0,0,1,0,1],by rw [mem_core]; decide⟩
    have hy : coreRepresentation (Fin 5) (Equiv.swap 2 3) y - y = second := by decide +kernel
    have hx : m (Multiplicative.ofAdd second) ∈ A := by
      have hh := displacement_mem N q m he A hA a ha y
      rwa [h.1,hy] at hh
    have hxne : m (Multiplicative.ofAdd second) ≠ 1 := by
      intro hh
      have heq := Multiplicative.ofAdd.injective (hm (hh.trans (map_one m).symm))
      exact (by decide : second ≠ 0) heq
    have hbfix : B ≤ centralizer ({m (Multiplicative.ofAdd second)} : Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (hBC hb _ hx).symm
    have hbim := normal_two_second_point_image N q hq m hm he B hP hBN hbfix (hcontrol _ hx hxne)
    have ht := hbim (mem_map_of_mem q (show b ∈ B.subgroupOf N from hb))
    rw [h.2,mem_zpowers_iff_mem_range_orderOf] at ht
    rw [show orderOf (Equiv.swap (2:Fin 5) 3) = 2 from
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)] at ht
    rcases Finset.mem_image.mp ht with ⟨i,hi,heq⟩
    have hi2 : i < 2 := Finset.mem_range.mp hi
    interval_cases i <;> revert heq <;> decide +kernel
end BinaryPermutation.FivePointCore
