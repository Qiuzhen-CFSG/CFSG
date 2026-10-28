module

public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.SymplecticFour.Sylow.FlagCounts
public import Mathlib.GroupTheory.Sylow

/-!
# The symplectic four-space unipotent flag

The determinant characters identify the local factors and separate the
unipotent subgroup from the torus-bearing Borel. The two incident parabolics
are proper, distinct, and generate the symplectic group; each is the join of
its local factor with the Borel. Recovering the point and plane from the
unipotent fixed-vector filtration identifies its full normalizer with the
Borel.

The coordinate counts give |U| = q⁴ and |B| = q⁴(q−1)². The ambient
order gives [Sp₄ : U] = (q²−1)(q⁴−1), which is odd when q = 2ⁿ,
n ≥ 1. Thus U is an actual Sylow 2-subgroup. The exported Sylow object
has underlying subgroup definitionally equal to the given `unipotent`.
The cardinality hypothesis alone suffices, so no separate characteristic
assumption is needed.

Source: the concrete Sp₄ flag amalgam underlying Aschbacher--Smith,
F.1.12(I)(2), printed pp.262--264.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F]

/-- The index of the concrete unipotent subgroup in the actual matrix group. -/
theorem index_unipotent : (unipotent (F := F)).index =
    ((Nat.card F)^2 - 1) * ((Nat.card F)^4 - 1) := by
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := F)) 4)
  rw [← card_unipotent, Subgroup.card_mul_index, card_sp, card_unipotent, mul_assoc]

/-- The determinant-one flag subgroup is a 2-group over a field of 2-power order. -/
theorem isPGroup_unipotent {n : ℕ} (hF : Nat.card F = 2^n) :
    IsPGroup 2 (unipotent (F := F)) := by
  apply IsPGroup.of_card (n := n * 4)
  rw [card_unipotent, hF, pow_mul]

/-- The unipotent subgroup contains the full 2-part of the symplectic group order. -/
theorem two_not_dvd_index_unipotent {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n) :
    ¬ 2 ∣ (unipotent (F := F)).index := by
  rw [index_unipotent]
  have hq : 2 ∣ Nat.card F := by
    rw [hF]
    exact dvd_pow_self 2 (by omega)
  have hp (k : ℕ) (hk : k ≠ 0) : ¬ 2 ∣ (Nat.card F)^k - 1 := by
    intro hd
    have hdq : 2 ∣ (Nat.card F)^k := hq.trans (dvd_pow_self _ hk)
    have hpos : 1 ≤ (Nat.card F)^k := Nat.one_le_pow k _ (Nat.card_pos (α := F))
    have h := Nat.dvd_sub hdq hd
    have heq : (Nat.card F)^k - ((Nat.card F)^k - 1) = 1 := by omega
    rw [heq] at h
    norm_num at h
  exact fun h => (Nat.prime_two.dvd_mul.mp h).elim (hp 2 (by decide)) (hp 4 (by decide))

/-- The standard Sylow 2-subgroup of the symplectic four-space matrix group. -/
@[expose] noncomputable def unipotentSylow {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 ≤ n) : Sylow 2 (Sp F) :=
  (isPGroup_unipotent hF).toSylow (two_not_dvd_index_unipotent hF hn)

@[simp] theorem coe_unipotentSylow {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n) :
    (unipotentSylow hF hn : Subgroup (Sp F)) = unipotent := rfl

end Theory.SpecificGroups.SymplecticFour
