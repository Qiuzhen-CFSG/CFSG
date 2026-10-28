module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Lifts
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Entries

/-!
# Extending centralization from the base field

Every simple D4 root matrix has degree at most two in its parameter. In odd
characteristic its values at 1 and -1, together with the identity, span all
values of the curve. Thus commuting with the value at 1 forces commutation
with the entire root curve, even when the base field has order three.
Transvection generation extends centralization of SL₂(GF(q)) to the full
split SL₂(GF(q³)).

This removes any small-field exception from the split-centralizer reduction.
Sources: the integral root curves of GLS3 §2.4 and the common-lattice subsystem
construction of Proposition 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup RootPairing.IntegralGeckConstruction
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
open Parabolics Parabolics.RankOneMatrices
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

private theorem commute_quadratic {F n : Type*} [Field F] [Fintype n] [DecidableEq n]
    (h2 : (2 : F) ≠ 0) (X A B : Matrix n n F)
    (hp : Commute X (1 + (1 : F) • A + (1 : F) ^ 2 • B))
    (hm : Commute X (1 + (-1 : F) • A + (-1 : F) ^ 2 • B)) (t : F) :
    Commute X (1 + t • A + t ^ 2 • B) := by
  have he : 1 + t • A + t ^ 2 • B =
      (1 - t ^ 2) • (1 : Matrix n n F) +
        ((t ^ 2 + t) / 2) • (1 + (1 : F) • A + (1 : F) ^ 2 • B) +
        ((t ^ 2 - t) / 2) • (1 + (-1 : F) • A + (-1 : F) ^ 2 • B) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [he]
  exact ((Commute.one_right X).smul_right _).add_right (hp.smul_right _) |>.add_right
    (hm.smul_right _)

private theorem two_ne_zero (P : Parameters) (hp : Odd P.prime) :
    (2 : ExtensionField P) ≠ 0 := by
  intro h
  have hd : P.prime ∣ 2 := (CharP.cast_eq_zero_iff (ExtensionField P) P.prime 2).mp h
  have he : P.prime = 2 := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left
    P.prime_prime.ne_one
  exact (by decide : ¬Odd (2 : ℕ)) (he ▸ hp)

private theorem positive_quadratic (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    positiveMatrix (typeDRootPairing_baseEquiv 2 i) t =
      1 + t • (eDividedPower (typeDRootPairing_baseEquiv 2 i) 1).map
        (Int.castRingHom (ExtensionField P)) +
      t ^ 2 • (eDividedPower (typeDRootPairing_baseEquiv 2 i) 2).map
        (Int.castRingHom (ExtensionField P)) := by
  have h3 : eDividedPower (typeDRootPairing_baseEquiv 2 i) 3 = 0 := by
    ext r s
    obtain ⟨r, rfl⟩ := (flatEquiv i).surjective r
    obtain ⟨s, rfl⟩ := (flatEquiv i).surjective s
    exact eThree_entry i r s
  simp only [positiveMatrix_formula, h3, Matrix.map_zero, map_zero, smul_zero, add_zero]

private theorem negative_quadratic (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    negativeMatrix (typeDRootPairing_baseEquiv 2 i) t =
      1 + t • (fDividedPower (typeDRootPairing_baseEquiv 2 i) 1).map
        (Int.castRingHom (ExtensionField P)) +
      t ^ 2 • (fDividedPower (typeDRootPairing_baseEquiv 2 i) 2).map
        (Int.castRingHom (ExtensionField P)) := by
  have h3 : fDividedPower (typeDRootPairing_baseEquiv 2 i) 3 = 0 := by
    ext r s
    obtain ⟨r, rfl⟩ := (flatEquiv i).surjective r
    obtain ⟨s, rfl⟩ := (flatEquiv i).surjective s
    exact fThree_entry i r s
  simp only [negativeMatrix_formula, h3, Matrix.map_zero, map_zero, smul_zero, add_zero]

/-- A single nontrivial positive root value determines its matrix centralizer. -/
theorem commute_positiveRoot_of_one {P : Parameters} (hp : Odd P.prime)
    (g : SplitGroup P) (i : Fin 4) (h : Commute g (positiveRoot P i 1))
    (t : ExtensionField P) : Commute g (positiveRoot P i t) := by
  have hm : Commute g (positiveRoot P i (-1)) := by
    have he : positiveRoot P i (-1) = (positiveRoot P i 1)⁻¹ := by
      apply Subtype.ext
      exact (positiveUnit_inv _ _).symm
    exact he.symm ▸ h.inv_right
  have hp' : Commute g.val.val (positiveMatrix (typeDRootPairing_baseEquiv 2 i) 1) :=
    congrArg (fun x : SplitGroup P => x.val.val) h.eq
  have hm' : Commute g.val.val (positiveMatrix (typeDRootPairing_baseEquiv 2 i) (-1)) :=
    congrArg (fun x : SplitGroup P => x.val.val) hm.eq
  rw [positive_quadratic] at hp' hm'
  apply Subtype.ext
  apply Units.ext
  change Commute g.val.val (positiveMatrix (typeDRootPairing_baseEquiv 2 i) t)
  rw [positive_quadratic]
  exact commute_quadratic (two_ne_zero P hp) _ _ _ hp' hm' t

/-- The same interpolation applies to the negative root curve. -/
theorem commute_negativeRoot_of_one {P : Parameters} (hp : Odd P.prime)
    (g : SplitGroup P) (i : Fin 4) (h : Commute g (negativeRoot P i 1))
    (t : ExtensionField P) : Commute g (negativeRoot P i t) := by
  have hm : Commute g (negativeRoot P i (-1)) := by
    have he : negativeRoot P i (-1) = (negativeRoot P i 1)⁻¹ := by
      apply Subtype.ext
      exact (negativeUnit_inv _ _).symm
    exact he.symm ▸ h.inv_right
  have hp' : Commute g.val.val (negativeMatrix (typeDRootPairing_baseEquiv 2 i) 1) :=
    congrArg (fun x : SplitGroup P => x.val.val) h.eq
  have hm' : Commute g.val.val (negativeMatrix (typeDRootPairing_baseEquiv 2 i) (-1)) :=
    congrArg (fun x : SplitGroup P => x.val.val) hm.eq
  rw [negative_quadratic] at hp' hm'
  apply Subtype.ext
  apply Units.ext
  change Commute g.val.val (negativeMatrix (typeDRootPairing_baseEquiv 2 i) t)
  rw [negative_quadratic]
  exact commute_quadratic (two_ne_zero P hp) _ _ _ hp' hm' t

private theorem base_transvection_one (P : Parameters) (i j : Fin 2) (hij : i ≠ j) :
    sl2BaseEmbedding P (SpecialLinearGroup.transvection hij 1) =
      SpecialLinearGroup.transvection hij 1 := by
  apply Subtype.ext
  ext a b
  change baseFieldEmbedding P ((1 + Matrix.single i j 1 :
    Matrix (Fin 2) (Fin 2) (GaloisField P.prime P.exponent)) a b) =
    (1 + Matrix.single i j 1 : Matrix (Fin 2) (Fin 2) (ExtensionField P)) a b
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add]
  split_ifs <;> simp only [map_zero, map_one]

/-- In odd characteristic, the centralizers of the base-field and full split
central SL₂ coincide. Only the root values 1 and -1 enter the interpolation. -/
theorem centralizer_base_eq_split {P : Parameters} (hp : Odd P.prime)
    (D : PinnedRankOneMaps P) :
    Subgroup.centralizer ((D.centralFixedEmbedding).range : Set (SplitGroup P)) =
      Subgroup.centralizer ((D.hom 1).range : Set (SplitGroup P)) := by
  apply le_antisymm
  · intro g hg
    have hbase (a : SL(2, GaloisField P.prime P.exponent)) :
        Commute g (D.centralFixedEmbedding a) :=
      (Subgroup.mem_centralizer_iff.mp hg _ ⟨a, rfl⟩).symm
    have hpos : Commute g (positiveRoot P 1 1) := by
      have h := hbase (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
        (by decide) 1)
      simpa only [PinnedRankOneMaps.centralFixedEmbedding, MonoidHom.comp_apply,
        base_transvection_one, D.positive] using h
    have hneg : Commute g (negativeRoot P 1 1) := by
      have h := hbase (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
        (by decide) 1)
      simpa only [PinnedRankOneMaps.centralFixedEmbedding, MonoidHom.comp_apply,
        base_transvection_one, D.negative] using h
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    have hc : Commute g (D.hom 1 a) := by
      apply sl2_root_induction (fun a => Commute g (D.hom 1 a)) ?_ ?_ ?_ a
      · intro t
        simpa only [D.positive] using commute_positiveRoot_of_one hp g 1 hpos t
      · intro t
        simpa only [D.negative] using commute_negativeRoot_of_one hp g 1 hneg t
      · intro a b ha hb
        simpa only [map_mul] using ha.mul_right hb
    exact hc.symm.eq
  · intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hg _ ⟨sl2BaseEmbedding P a, rfl⟩

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
