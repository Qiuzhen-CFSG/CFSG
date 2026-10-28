module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.CellSeparation.Height
public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.RankOne
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Comparison

/-!
# Negative simple curves are outside the split Borel

A positive matrix has zero Cartan/simple-root entry, whereas the negative
simple curve has its parameter in that entry. Since the Borel normalizes the
positive subgroup, a simple Weyl word in the Borel would put its negative
simple curve inside the positive subgroup. The rank-one word then excludes
the negative simple curve itself from the Borel.

Source: the nontriviality condition in GLS3 2.3.4(b), using §2.4 rank-one
identities; `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Parabolics PositiveCoordinates PositiveCoordinates.Injectivity
open Parabolics.RankOneMatrices
attribute [local instance] matrixLatticeDecidableEq

lemma height_simple (i : Fin 4) :
    height ((typeDRootPairing 2).root (typeDSimpleRootIndex 2 i)) = 1 := by
  fin_cases i <;>
    norm_num [height, typeDSimpleRootIndex,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      basisVector, Pi.single_apply, Fin.ext_iff]

lemma negative_entry (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    matrix P (negativeRoot P i t) (.inl (typeDRootPairing_baseEquiv 2 i))
      (.inr (typeDSimpleRootIndex 2 i)) = t := by
  change RootPairing.SimpleGeckGroup.negativeMatrix _ t _ _ = _
  rw [← orderedRoot_zero i]
  change RootPairing.SimpleGeckGroup.negativeMatrix _ t
    (flatEquiv i (.inl i)) (flatEquiv i (.inr 0)) = _
  rw [negativeMatrix_entry]
  simp [fData]

lemma negative_not_positive (n : ℕ) (hn : 0 < n) (i : Fin 4)
    (t : ExtensionField (binaryParameters n hn)) (ht : t ≠ 0) :
    negativeRoot (binaryParameters n hn) i t ∉ positiveSubgroup _ := by
  intro h
  have hz := positive_raises n hn h (.inl (typeDRootPairing_baseEquiv 2 i))
    (.inr (typeDSimpleRootIndex 2 i))
  have hdeg : degree (.inl (typeDRootPairing_baseEquiv 2 i)) <
      1 + degree (.inr (typeDSimpleRootIndex 2 i)) := by
    change height 0 < 1 + height ((typeDRootPairing 2).root (typeDSimpleRootIndex 2 i))
    rw [map_zero, height_simple]
    norm_num
  have he := hz hdeg
  exact ht (by simpa [Matrix.sub_apply, negative_entry] using he)

lemma borel_normalizes_positive {P : Parameters} (D : Inputs P) :
    splitBorel P ≤ Subgroup.normalizer (positiveSubgroup P) :=
  sup_le (positiveSubgroup P).le_normalizer D.torus_normalizes_positive

lemma weylWord_not_borel (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4) :
    weylWord (binaryParameters n hn) i 1 ∉ splitBorel _ := by
  intro hw
  have hx : positiveRoot (binaryParameters n hn) i 1 ∈ positiveSubgroup _ :=
    Subgroup.subset_closure ⟨i, 1, rfl⟩
  have hconj := (Subgroup.le_normalizer_iff.mp (borel_normalizes_positive D)) _ hw _ hx
  have hinv : (weylWord (binaryParameters n hn) i 1)⁻¹ =
      weylWord (binaryParameters n hn) i 1 := by
    exact (eq_inv_of_mul_eq_one_left (by simpa only [pow_two] using
      (weylWord_sq (binaryParameters n hn) rfl i))).symm
  rw [hinv, weylWord_positive _ rfl] at hconj
  exact negative_not_positive n hn i 1 one_ne_zero hconj

lemma negativeRoot_not_borel (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4) :
    negativeRoot (binaryParameters n hn) i 1 ∉ splitBorel _ := by
  intro hy
  apply weylWord_not_borel n hn D i
  have hx : positiveRoot (binaryParameters n hn) i 1 ∈ splitBorel _ :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, 1, rfl⟩)
  have h := (splitBorel _).mul_mem ((splitBorel _).mul_mem hx hy) hx
  let := rankOneExtensionCharTwo (binaryParameters n hn) rfl
  simpa only [weylWord, inv_one, CharTwo.neg_eq] using h
end
end Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
