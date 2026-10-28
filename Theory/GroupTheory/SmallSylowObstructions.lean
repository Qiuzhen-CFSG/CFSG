module

public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.Sylow

/-!
# Small elementary Sylow obstructions

A Sylow two-subgroup of order at most eight excludes divisibility of the
ambient order by sixteen. An elementary Sylow excludes elements of order
four, by placing their cyclic subgroups in a conjugate Sylow subgroup.
These tests filter the actual group models in Aschbacher–Smith F.6.17–18,
printed pp.309–310.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow bound retains the ambient two-part divisibility obstruction. -/
theorem not_sixteen_dvd_of_sylow_le_eight (P : Sylow 2 G) (hP : Nat.card P ≤ 8) :
    ¬ 16 ∣ Nat.card G := by
  intro hd
  have h := P.pow_dvd_card_of_pow_dvd_card (n := 4) hd
  have hp := Nat.le_of_dvd (Nat.card_pos (α := P)) h
  omega

/-- Every two-element lies in an elementary Sylow, so order four is impossible. -/
theorem elementary_sylow_no_order_four (P : Sylow 2 G) [IsElementaryAbelian 2 P]
    (x : G) : orderOf x ≠ 4 := by
  intro hx
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, hx]
    decide)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  let e := P.equiv S
  let : IsElementaryAbelian 2 S := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (S : Subgroup G))
    x (hS (mem_zpowers x))
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [hx] at hd
  norm_num at hd
end Theory.GroupTheory
