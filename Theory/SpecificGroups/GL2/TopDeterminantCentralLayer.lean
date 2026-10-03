module
public import Theory.SpecificGroups.GL2.DeterminantCenter
public import Theory.SpecificGroups.GL2.DeterminantTwoPowerCentralProduct
public import Theory.SpecificGroups.GL2.DeterminantTwoPowerIndex

/-!
# Common center beneath the top determinant level

Let F be a finite field whose unit group has exact two-part 2^m, with
m at least one. The determinant levels m and m-1 have exactly the same
center after their actual subtype inclusions into GL2(F). Joining this
common center with the determinant-one level gives level m-1, which has
relative index two in level m. The endpoint m=1 is included.

The scalar-center formula reduces equality of centers to the assertion
that 2^(m+1)-st roots of unity already have order dividing 2^m. For such
a root u, the element u^(2^m) has both square one and an odd power one,
so it is one. The lower-level scalar decomposition supplies the join,
and the established determinant filtration index formula supplies index
two. The divisibility assumption forces odd field order.

Source: Alperin--Brauer--Gorenstein II.2 Lemma 1(v), article pp17–18,
and the full linear-model extension in II.3 Proposition 3, article p26.
The result concerns the actual matrix subgroups and is independent of
abstract Q-group recognition.
-/

namespace Matrix.GeneralLinearGroup

private theorem roots_top_two_power (F : Type*) [Field F] [Finite F]
    (m : ℕ) (hd : 2 ^ m ∣ Nat.card F - 1)
    (ho : Odd ((Nat.card F - 1) / 2 ^ m)) :
    rootsOfUnity (2 ^ (m + 1)) F = rootsOfUnity (2 ^ m) F := by
  apply le_antisymm
  · intro u hu
    change u ^ (2 ^ (m + 1)) = 1 at hu
    change u ^ (2 ^ m) = 1
    apply (pow_eq_one_iff_of_coprime ho.coprime_two_left).mp
    constructor
    · simpa only [← pow_mul, ← pow_succ] using hu
    · rw [← pow_mul, Nat.mul_div_cancel' hd]
      simpa only [Nat.card_units] using (pow_card_eq_one' (x := u))
  · exact rootsOfUnity_le_of_dvd (pow_dvd_pow 2 (Nat.le_succ m))

/-- The full two-primary determinant level and its predecessor share their
center, and the predecessor is the central join of level zero of index two. -/
public theorem top_determinant_central_layer
    (F : Type*) [Field F] [Finite F] (m : ℕ) (hm : 1 ≤ m)
    (hd : 2 ^ m ∣ Nat.card F - 1)
    (ho : Odd ((Nat.card F - 1) / 2 ^ m)) :
    let D := determinantTwoPower F m
    let B := determinantTwoPower F (m - 1)
    let C := (Subgroup.center D).map D.subtype
    C = (Subgroup.center B).map B.subtype ∧
      C ⊔ determinantTwoPower F 0 = B ∧ B.relIndex D = 2 := by
  dsimp only
  have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hodd : Odd (Nat.card F) := by
    have htwo : 2 ∣ Nat.card F - 1 :=
      (dvd_pow_self 2 (by omega : m ≠ 0)).trans hd
    obtain ⟨k, hk⟩ := htwo
    refine ⟨k, ?_⟩
    have hpos : 0 < Nat.card F := Nat.card_pos
    omega
  have hc : (Subgroup.center (determinantTwoPower F m)).map
      (determinantTwoPower F m).subtype =
      (rootsOfUnity (2 ^ m) F).map (scalar (Fin 2)) := by
    rw [center_determinantTwoPower_map, roots_top_two_power F m hd ho]
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, center_determinantTwoPower_map, hpred]
  · rw [hc, determinantTwoPower_zero]
    have hgen := determinantTwoPower_eq_scalar_sup_kernel F hodd (m - 1)
      (by simpa only [hpred] using hd)
    simpa only [hpred] using hgen.symm
  · simpa only [hpred] using determinantTwoPower_successor_relIndex F (m - 1)
      (by simpa only [hpred] using hd)
end Matrix.GeneralLinearGroup
