module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Representatives for the seven conjugacy classes of A₆

The representatives have cycle types 1, 2²1², 31³, 3², 42, 51 and 51.
The last two are a five-cycle and its square. Small kernel-checked finite
calculations give the orders and centralizer sizes. The only conjugacy
search is over the 360 even permutations, after rewriting `IsConj` as
existence of a group element (avoiding enumeration of pairs of units).
The class-size argument establishing completeness is in the parent module.

Source: standard alternating-group conjugacy calculations, as used in
Janko, *A characterization of the Mathieu simple groups, I* (1968), §6.
-/

@[expose] public section
namespace AlternatingSix.GoldenClassGeometry

open Equiv

-- Use the direct permutation enumeration, without transporting through `Fin`.
local instance : Fintype (Perm (Fin 6)) := fintypePerm

abbrev A6 := alternatingGroup (Fin 6)

def a2 : A6 := ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

def a3 : A6 := ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

def a33 : A6 := ⟨swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5), by
  rw [Perm.mem_alternatingGroup]; decide⟩

def a4 : A6 := ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, by
  rw [Perm.mem_alternatingGroup]; decide⟩

def a5 : A6 := ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, by
  rw [Perm.mem_alternatingGroup]; decide⟩

def rep : Fin 7 → A6 := ![1, a2, a3, a33, a4, a5, a5 ^ 2]

def orders : Fin 7 → ℕ := ![1, 2, 3, 3, 4, 5, 5]

def cents : Fin 7 → ℕ := ![360, 8, 9, 9, 4, 5, 5]

theorem rep_orders (i : Fin 7) : orderOf (rep i) = orders i := by
  apply (orderOf_eq_iff (by fin_cases i <;> decide)).mpr
  fin_cases i <;> decide +kernel

private theorem cent_card (x : A6) : Nat.card (Subgroup.centralizer ({x} : Set A6)) =
    Fintype.card {g : A6 // g * x = x * g} := by
  classical
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun g => Subgroup.mem_centralizer_singleton_iff)

private theorem count2 : Fintype.card {g : A6 // g * a2 = a2 * g} = 8 := by
  decide +kernel

private theorem count3 : Fintype.card {g : A6 // g * a3 = a3 * g} = 9 := by
  decide +kernel

private theorem count33 : Fintype.card {g : A6 // g * a33 = a33 * g} = 9 := by
  decide +kernel

private theorem count4 : Fintype.card {g : A6 // g * a4 = a4 * g} = 4 := by
  decide +kernel

private theorem count5 : Fintype.card {g : A6 // g * a5 = a5 * g} = 5 := by
  decide +kernel

private theorem count52 : Fintype.card {g : A6 // g * (a5 ^ 2) = (a5 ^ 2) * g} = 5 := by
  decide +kernel

theorem rep_cents (i : Fin 7) : Nat.card (Subgroup.centralizer ({rep i} : Set A6)) = cents i := by
  fin_cases i
  · have h : Subgroup.centralizer ({(1 : A6)} : Set A6) = ⊤ := by
      ext g
      simp [Subgroup.mem_centralizer_singleton_iff]
    change Nat.card (Subgroup.centralizer ({(1 : A6)} : Set A6)) = 360
    rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · exact (cent_card _).trans count2
  · exact (cent_card _).trans count3
  · exact (cent_card _).trans count33
  · exact (cent_card _).trans count4
  · exact (cent_card _).trans count5
  · exact (cent_card _).trans count52

theorem five_nonsquare : ¬ IsConj a5 (a5 ^ 2) := by
  rw [isConj_iff]
  decide +kernel

/-- The two order-three representatives already have different S₆ cycle types. -/

theorem three_not_conj : ¬ IsConj a3 a33 := by
  intro h
  have he := Perm.isConj_iff_cycleType_eq.mp
    ((alternatingGroup (Fin 6)).subtype.map_isConj h)
  exact (by decide +kernel : (a3 : Perm (Fin 6)).cycleType ≠
    (a33 : Perm (Fin 6)).cycleType) he

/-- The even permutation (14)(23) inverts the marked five-cycle. -/

def inverter : A6 := ⟨swap 1 4 * swap 2 3, by
  rw [Perm.mem_alternatingGroup]; decide⟩

theorem five_inverse : IsConj a5 a5⁻¹ :=
  isConj_iff.mpr ⟨inverter, by decide +kernel⟩

theorem five_square_inverse : IsConj (a5 ^ 2) (a5 ^ 2)⁻¹ := by
  simpa only [inv_pow] using IsConj.pow 2 five_inverse

theorem five_square_nonsquare : ¬ IsConj (a5 ^ 2) ((a5 ^ 2) ^ 2) := by
  intro h
  have h' := IsConj.pow 3 h
  have h1 : (a5 ^ 2) ^ 3 = a5 := by decide +kernel
  have h2 : ((a5 ^ 2) ^ 2) ^ 3 = a5 ^ 2 := by decide +kernel
  rw [h1, h2] at h'
  exact five_nonsquare h'

end AlternatingSix.GoldenClassGeometry
