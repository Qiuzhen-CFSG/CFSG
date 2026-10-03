module
public import ABG.ChapterII.Section2.UnitaryScalarGeneration
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import Theory.SpecificGroups.GL2.DeterminantCenter

/-!
# Exact centers of the unitary determinant levels

For odd p and nonzero n, the center of every actual SU2Level m, mapped
into the original GU2, is exactly SU2ScalarLevel m. No divisibility bound
on m is needed; the scalar subgroup already imposes the unitary norm
condition. In particular, levels zero and fields of orders three and nine
remain included.

The determinant-one level is noncommutative through the actual SU2--SL2
equivalence and the proved linear transvections. Its inclusion makes every
level noncommutative. The faithful GL2 image then has only scalar
centralizers. The determinant equation for cI is c squared, giving exactly
the roots of order dividing 2^(m+1). Conversely these actual unitary scalars
belong to the level and commute with it.

Source: Alperin--Brauer--Gorenstein II.2 Lemma 1(v) and II.3 Proposition 3,
article page 26. This identifies the actual central kernel for the unitary
model comparison; coefficient compatibility is established separately.
-/

namespace ABG
open Matrix.GeneralLinearGroup

private theorem level_noncommutative
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0) (m : ℕ) :
    ¬ IsMulCommutative (SU2Level p n hn m) := by
  intro h
  let e := (SU2LevelZeroEquivSpecial p n hn).trans
    ((specialUnitaryTwo_equiv_sl2 p n hp hn).trans
      (determinantTwoPowerZeroEquivSL (GaloisField p n)).symm)
  let j : SU2Level p n hn 0 →* SU2Level p n hn m :=
    Subgroup.inclusion (SU2Level_mono p n hn (Nat.zero_le m))
  apply determinantTwoPower_not_isMulCommutative (GaloisField p n) 0
  apply IsMulCommutative.of_comm
  intro a b
  apply e.symm.injective
  simp only [map_mul]
  apply Subgroup.inclusion_injective (SU2Level_mono p n hn (Nat.zero_le m))
  exact (map_mul j _ _).trans
    (((isMulCommutative_iff.mp h) (j (e.symm a)) (j (e.symm b))).trans
      (map_mul j _ _).symm)

public theorem SU2Level_center_map
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0) (m : ℕ) :
    (Subgroup.center (SU2Level p n hn m)).map (SU2Level p n hn m).subtype =
      SU2ScalarLevel p n hn m := by
  let U := (unitaryForm 2 p n hn).unitarySubgroup
  let D := (SU2Level p n hn m).map U.subtype
  let e := (SU2Level p n hn m).equivMapOfInjective U.subtype U.subtype_injective
  have hD : ¬ IsMulCommutative D := by
    intro h
    apply level_noncommutative p n hp hn m
    apply IsMulCommutative.of_comm
    intro a b
    apply e.injective
    simpa only [map_mul] using (isMulCommutative_iff.mp h) (e a) (e b)
  ext A
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haC : a.val.val ∈ Subgroup.centralizer (D : Set (GL (Fin 2) (GaloisField p (2 * n)))) := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro _ ⟨b, hb, rfl⟩
      exact congrArg (fun x : SU2Level p n hn m => x.val.val)
        (Subgroup.mem_center_iff.mp ha ⟨b, hb⟩)
    obtain ⟨c, hc⟩ := centralizer_le_scalar_of_noncommutative D hD haC
    refine ⟨c, ?_, hc⟩
    have hdet := (mem_SU2Level_iff p n hn m a.val).mp a.property
    rw [← hc, det_scalar, Fintype.card_fin] at hdet
    change c ^ (2 ^ (m + 1)) = 1
    rw [pow_succ', pow_mul]
    exact hdet
  · rintro ⟨c, hc, hca⟩
    change scalar (Fin 2) c = A.val at hca
    have hA : A ∈ SU2Level p n hn m := by
      apply (mem_SU2Level_iff p n hn m A).mpr
      rw [← hca, det_scalar, Fintype.card_fin, ← pow_mul, ← pow_succ']
      exact hc
    refine ⟨⟨A, hA⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change b.val.val * A.val = A.val * b.val.val
    rw [← hca]
    exact (scalar_commute c b.val.val).symm

end ABG

