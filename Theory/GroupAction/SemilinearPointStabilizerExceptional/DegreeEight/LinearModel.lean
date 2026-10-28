module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.DegreeEight.Permutations
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# The matrix model of the marked degree-eight subgroup

The marked permutations are the literal images of the two generators of
PSL₂(7). Its faithful projective action identifies their generated subgroup
with PSL₂(7), and the checked action on the eight Singer subgroups identifies
that group with SL₃(2), hence GL₃(2). Equality of orders is used only after
these genuine action comparisons.

This is the model comparison for GLS, Volume 4, Chapter 1, Theorem 3.2 and
the degree-eight endpoint of Lemma 3.9 (`refs/KGroup/GLS4/Chapter1.tex`).
The imported ATLAS comparison retains its attribution and license.
-/

public section
namespace MulAction.SemilinearPointStabilizer.DegreeEight

open Atlas.Comparisons.Exceptional

/-- The projective permutation representation has precisely the marked image. -/
theorem projective_range_eq_seed : Seven.permutation.range = linearSeed := by
  have hgen : Seven.permutation '' Seven.generators = ({cycle, inversion} : Set Perm) := by
    change Seven.permutation '' Seven.generators = {Seven.translation, Seven.inversion}
    rw [Seven.generators, Set.image_pair, Seven.permutation_upper, Seven.permutation_inversion]
  rw [linearSeed, ← hgen, ← MonoidHom.map_closure, Seven.psl_generated,
    ← MonoidHom.range_eq_map]

/-- A genuine isomorphism from the marked permutation subgroup to GL₃(2). -/
noncomputable def linearSeedEquiv :
    linearSeed ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
  (MulEquiv.subgroupCongr projective_range_eq_seed.symm).trans
    ((MonoidHom.ofInjective Seven.permutation_injective).symm.trans
      (psl2SevenEquivSl3Two.trans Matrix.PSL3Two.equivGL))

theorem card_linearSeed : Nat.card linearSeed = 168 := by
  rw [← projective_range_eq_seed,
    ← Nat.card_congr (MonoidHom.ofInjective Seven.permutation_injective).toEquiv]
  exact psl2Seven_card

/-- Once the marked generators occur in the actor, its order bound makes the
actual inclusion an equality and supplies the matrix equivalence. -/
theorem equiv_of_seed_le (U : Subgroup Perm) (hcard : Nat.card U ∣ 168)
    (hseed : linearSeed ≤ U) :
    Nonempty (U ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  have he : linearSeed = U := Subgroup.eq_of_le_of_card_ge hseed (by
    rw [card_linearSeed]
    exact Nat.le_of_dvd (by decide) hcard)
  exact ⟨(MulEquiv.subgroupCongr he.symm).trans linearSeedEquiv⟩

end MulAction.SemilinearPointStabilizer.DegreeEight
