module
public import ABG.ChapterII.Section2.UnitaryDeterminantCenter
public import ABG.ChapterII.Section2.UnitaryDeterminantIndex

/-!
# The central layer in the full unitary determinant model

Let q = p^n for an odd prime p and a nonzero n, and suppose 2^m is the
exact two-part of q+1, with m at least one. The centers of the actual
Hermitian determinant levels m and m-1 have the same image in GU2. This
common center, joined with the determinant-one level, is exactly level
m-1, which has index two in level m. The case m=1 remains included.

The exact center theorem reduces the comparison to scalar roots. A scalar
in GU2 satisfies the norm-one equation c^(q+1)=1. Its 2^m-th power has
square one and also has odd order dividing (q+1)/2^m, so it is one. Thus
the scalar centers stabilize between the last two determinant levels.
Scalar generation at the predecessor level and the determinant index
formula give the other two assertions. Using the norm equation is essential:
the multiplicative group of GF(q^2) can have a larger two-part.

Source: Alperin--Brauer--Gorenstein II.2 Lemma 1, article page 17, and the
full unitary model L* in II.3 Proposition 3, article page 26. This result
supplies the actual central subgroup and index-two layer for comparing L*
with the abstract group in that proposition.
-/

namespace ABG
open Matrix.GeneralLinearGroup

private theorem scalar_top_stabilizes
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ)
    (hd : 2 ^ (m + 1) ∣ p ^ n + 1)
    (ho : Odd ((p ^ n + 1) / 2 ^ (m + 1))) :
    SU2ScalarLevel p n hn (m + 1) = SU2ScalarLevel p n hn m := by
  apply le_antisymm
  · intro A hA
    obtain ⟨c, hc, heq⟩ := hA
    change scalar (Fin 2) c = A.val at heq
    have hnorm : c ^ (p ^ n + 1) = 1 :=
      (scalar_mem_GU2_iff p n hn c).mp (heq.symm ▸ A.property)
    change c ^ (2 ^ (m + 1 + 1)) = 1 at hc
    have hc2 : (c ^ (2 ^ (m + 1))) ^ 2 = 1 := by
      simpa only [← pow_mul, ← pow_succ] using hc
    have hco : (c ^ (2 ^ (m + 1))) ^ ((p ^ n + 1) / 2 ^ (m + 1)) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' hd]
      exact hnorm
    obtain ⟨k, hk⟩ := ho
    rw [hk, pow_add, pow_mul, hc2, one_pow, pow_one, one_mul] at hco
    exact ⟨c, hco, heq⟩
  · rintro A ⟨c, hc, heq⟩
    refine ⟨c, ?_, heq⟩
    change c ^ (2 ^ (m + 1 + 1)) = 1
    rw [pow_succ, pow_mul, hc, one_pow]

public theorem SU2Level_top_central_layer
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (hd : 2 ^ m ∣ p ^ n + 1)
    (ho : Odd ((p ^ n + 1) / 2 ^ m)) :
    let D := SU2Level p n hn m
    let L := SU2Level p n hn (m - 1)
    let C := (Subgroup.center D).map D.subtype
    C = (Subgroup.center L).map L.subtype ∧
      C ⊔ SU2Level p n hn 0 = L ∧ L.relIndex D = 2 := by
  dsimp only
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] at *
  change (Subgroup.center (SU2Level p n hn (k + 1))).map
      (SU2Level p n hn (k + 1)).subtype =
      (Subgroup.center (SU2Level p n hn k)).map (SU2Level p n hn k).subtype ∧
    (Subgroup.center (SU2Level p n hn (k + 1))).map
      (SU2Level p n hn (k + 1)).subtype ⊔ SU2Level p n hn 0 =
      SU2Level p n hn k ∧
    (SU2Level p n hn k).relIndex (SU2Level p n hn (k + 1)) = 2
  rw [SU2Level_center_map p n hp hn (k + 1), SU2Level_center_map p n hp hn k]
  have hC := scalar_top_stabilizes p n hn k hd ho
  refine ⟨hC, ?_, SU2Level_successor_relIndex p n hn k hd⟩
  rw [hC]
  exact (SU2Level_eq_scalar_sup_zero p n hn hp.pow k hd).symm

end ABG
