module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.NormNum

/-!
# Solvability of groups of order twenty

Sylow's counting theorems make the Sylow 5-subgroup unique: its number divides
four and is congruent to one modulo five. The resulting normal subgroup has
order five and the quotient order four. Both are nilpotent, so their extension
is solvable.

This elementary consequence of Sylow's theorems supplies the degenerate
`Sz(2)` case in the Suzuki matrix-group construction.
-/

namespace Group

/-- Every group of order twenty is solvable. -/
public theorem isSolvable_of_card_twenty {G : Type*} [Group G] (hcard : Nat.card G = 20) :
    Group.IsSolvable G := by
  let : Finite G := Nat.finite_of_card_ne_zero (by omega)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 G := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hcard]
    rw [show 20 = 2 ^ 2 * 5 from rfl, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_five.factorization]
    norm_num
  have hindex : (P : Subgroup G).index = 4 := by
    have h := (P : Subgroup G).card_mul_index
    rw [hP, hcard] at h
    omega
  have hcount : Nat.card (Sylow 5 G) = 1 := by
    have hd := P.card_dvd_index
    rw [hindex] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hm := card_sylow_modEq_one 5 G
    change Nat.card (Sylow 5 G) % 5 = 1 % 5 at hm
    omega
  let : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let : (P : Subgroup G).Normal := P.normal_of_subsingleton
  have hquot : Nat.card (G ⧸ (P : Subgroup G)) = 4 := hindex
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have htwo : IsPGroup 2 (G ⧸ (P : Subgroup G)) :=
    IsPGroup.of_card (n := 2) (by simpa using hquot)
  let : Group.IsNilpotent (G ⧸ (P : Subgroup G)) := htwo.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (P : Subgroup G)).2
    ⟨inferInstance, inferInstance⟩

end Group
