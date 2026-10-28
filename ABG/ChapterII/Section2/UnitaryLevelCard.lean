module
public import ABG.ChapterII.Section2.UnitaryDeterminantIndex
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import GorensteinWalter.PSL2Cardinality

/-!
# Cardinality of the actual unitary determinant levels

For odd prime p, nonzero n, and 2^m dividing p^n+1, the actual unitary
level m has order 2^m times the order p^n((p^n)^2-1) of SL2(GF(p^n)).
This includes q=3 and q=9. The result supplies the ambient order used to
certify the explicit unitary monomial subgroup as a Sylow subgroup.

The original determinant-one subgroup is identified with actual special
unitary, then with SL2 by the proved change-of-basis equivalence. Its order
is therefore the existing SL2 cardinal formula. The previously computed
relative index is 2^m; multiplying order by index gives the result. No
ambient unitary order formula or assumed recognition is used.

Source: ABG II.2 Lemma 1 proof, article page 17, used in the concrete
unitary Sylow construction and II.3 Proposition 3's model comparison.
-/

namespace ABG

public theorem SU2Level_card
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0) (m : ℕ)
    (hd : 2 ^ m ∣ p ^ n + 1) :
    Nat.card (SU2Level p n hn m) = 2 ^ m * p ^ n * ((p ^ n) ^ 2 - 1) := by
  let D := SU2Level p n hn m
  let K := SU2Level p n hn 0
  let eK := (SU2LevelZeroEquivSpecial p n hn).trans
    (specialUnitaryTwo_equiv_sl2 p n hp hn)
  have hK : Nat.card K = p ^ n * ((p ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr eK.toEquiv, GorensteinWalter.sl2_card_formula,
      GaloisField.card p n hn]
  let e := Subgroup.subgroupOfEquivOfLe (SU2Level_mono p n hn (Nat.zero_le m))
  have hmul := (K.subgroupOf D).card_mul_index
  change Nat.card (K.subgroupOf D) * K.relIndex D = Nat.card D at hmul
  rw [Nat.card_congr e.toEquiv, hK, SU2Level_zero_relIndex p n hn m hd] at hmul
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul.symm

end ABG

