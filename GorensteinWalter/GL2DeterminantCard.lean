module
public import Theory.SpecificGroups.GL2.DeterminantTwoPowerIndex
public import GorensteinWalter.PSL2Cardinality

/-!
# Cardinality of the GL2 determinant levels

If 2^m divides |F|-1 for a finite field F, the actual determinant level m
has order 2^m*|F|*(|F|^2-1). Its zero level is the actual SL2 group, with
index 2^m in level m. Multiplying the proved index by the exact SL2 order
gives the formula.

This supplies the order comparison for the linear wreathed and semidihedral
Sylow constructions in ABG II.2 Lemma1, article p17. It assumes no Sylow
shape or abstract matrix-group identification. The assembly stays at the
layer of its existing SL2 cardinality prerequisite.
-/

namespace Matrix.GeneralLinearGroup

public theorem determinantTwoPower_card (F : Type*) [Field F] [Finite F] (m : ℕ)
    (hd : 2 ^ m ∣ Nat.card F - 1) :
    Nat.card (determinantTwoPower F m) = 2 ^ m * Nat.card F * (Nat.card F ^ 2 - 1) := by
  let D := determinantTwoPower F m
  let L := determinantTwoPower F 0
  have hle : L ≤ D := determinantTwoPower_mono (Nat.zero_le m)
  have h := (L.subgroupOf D).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  change Nat.card L * L.relIndex D = Nat.card D at h
  rw [determinantTwoPower_zero_relIndex F m hd,
    Nat.card_congr (determinantTwoPowerZeroEquivSL F).toEquiv,
    GorensteinWalter.sl2_card_formula] at h
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h.symm

end Matrix.GeneralLinearGroup

