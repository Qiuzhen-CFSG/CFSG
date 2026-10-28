module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.CellSeparation.Height
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation

/-!
# Negative canonical D4 root curves lower height

The published height is the linear combination of simple-coroot pairings with
coefficients `(3, 5, 3, 3)`. Integral Chevalley homogeneity, for both signs of
roots and their actual Tits routes, therefore makes the nth divided power shift
height by n times its root's height. A negative root has height at most -1;
each nonconstant term of its specialized curve lowers height by at least one.

This supplies the negative-root matrix premise of the opposite-subgroup and
single-cell separation arguments. No characteristic restriction is needed.
Source: the support argument for GLS3 2.3.8(c) and the canonical root curves of
§2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Parabolics PositiveCoordinates PositiveCoordinates.Injectivity
open Parabolics.RankOneMatrices
attribute [local instance] matrixLatticeDecidableEq

private def corootHeight (w : TypeDRootIndex 4 → ℤ) : ℤ :=
  3 * w (typeDSimpleRootIndex 2 0) + 5 * w (typeDSimpleRootIndex 2 1) +
    3 * w (typeDSimpleRootIndex 2 2) + 3 * w (typeDSimpleRootIndex 2 3)

private lemma height_eq_corootHeight (r : TypeDRootIndex 4) :
    height ((typeDRootPairing 2).root r) =
      (corootHeight ((typeDRootPairing 2).pairingIn ℤ r) : ℝ) := by
  have hc (q : TypeDRootIndex 4) :
      ((typeDRootPairing 2).pairingIn ℤ r q : ℝ) = (typeDRootPairing 2).pairing r q :=
    (typeDRootPairing 2).algebraMap_pairingIn ℤ r q
  simp only [corootHeight, Int.cast_add, Int.cast_mul, Int.cast_ofNat, hc,
    typeDRootPairing_pairing, typeDRootEmbedding_typeDSimpleRootIndex]
  change 3 * (typeDRootEmbedding 4 r : Vec 4) 0 +
    2 * (typeDRootEmbedding 4 r : Vec 4) 1 + (typeDRootEmbedding 4 r : Vec 4) 2 = _
  simp only [typeDSimpleRoot, dot, Fin.sum_univ_succ]
  norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  ring

private lemma degree_eq_corootHeight (j : LatticeIndex) :
    degree j = (corootHeight (chevalleyBasisWeight (P := typeDRootPairing 2) j) : ℝ) := by
  rcases j with j | j
  · simp [degree, rootWeight, chevalleyBasisWeight, corootHeight]
  · exact height_eq_corootHeight j

private lemma dividedPower_degree (r : TypeDRootIndex 4) (n : ℕ)
    (i j : LatticeIndex)
    (hij : rootDividedPower (b := typeDRootPairing_base 2) r n i j ≠ 0) :
    degree i - degree j = (n : ℝ) * height ((typeDRootPairing 2).root r) := by
  have h := rootDividedPower_isChevalleyHomogeneous
    (b := typeDRootPairing_base 2) r n i j hij
  have h0 := h (typeDSimpleRootIndex 2 0)
  have h1 := h (typeDSimpleRootIndex 2 1)
  have h2 := h (typeDSimpleRootIndex 2 2)
  have h3 := h (typeDSimpleRootIndex 2 3)
  have hd : corootHeight (chevalleyBasisWeight (P := typeDRootPairing 2) i) -
      corootHeight (chevalleyBasisWeight (P := typeDRootPairing 2) j) =
      (n : ℤ) * corootHeight ((typeDRootPairing 2).pairingIn ℤ r) := by
    dsimp only [corootHeight]
    linear_combination 3 * h0 + 5 * h1 + 3 * h2 + 3 * h3
  rw [degree_eq_corootHeight, degree_eq_corootHeight, height_eq_corootHeight]
  exact_mod_cast hd

private lemma negative_height (r : TypeDRootIndex 4)
    (hr : ¬ (typeDRootPairing_base 2).IsPos r) :
    height ((typeDRootPairing 2).root r) ≤ -1 := by
  let _ := (typeDRootPairing 2).indexNeg
  have hp := (RootPairing.Base.IsPos.neg_iff_not (typeDRootPairing_base 2) r).mpr hr
  have hmem : -r ∈ Set.range rootIndex := by rw [range_rootIndex]; exact hp
  obtain ⟨i, hi⟩ := hmem
  have h := height_rootIndex_ge_one i
  rw [hi] at h
  have he : (typeDRootPairing 2).root (-r) = -(typeDRootPairing 2).root r := by
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rw [he, map_neg] at h
  linarith

private lemma negative_dividedPower_lowers (P : Parameters) (r : TypeDRootIndex 4)
    (hr : ¬ (typeDRootPairing_base 2).IsPos r) (n : ℕ) (hn : 0 < n) :
    Raises (fun i => -degree i) 1
      (specializeMatrix (S := ExtensionField P)
        (rootDividedPower (b := typeDRootPairing_base 2) r n)) := by
  intro i j hij
  by_contra hne
  have hint : rootDividedPower (b := typeDRootPairing_base 2) r n i j ≠ 0 := by
    intro hz
    exact hne (by simp [specializeMatrix, hz])
  have hd := dividedPower_degree r n i j hint
  have hrh := negative_height r hr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- Every canonical negative root curve lowers the published root height by at least one.
This holds over every parameter field, including all binary parameters. -/
lemma negative_rootCurve_lowers (P : Parameters) (r : TypeDRootIndex 4)
    (hr : ¬ (typeDRootPairing_base 2).IsPos r) (t : ExtensionField P) :
    Raises (fun j => -degree j) 1 (matrix P (rootCurve P r t) - 1) := by
  change Raises (fun j => -degree j) 1 (rootMatrix (b := typeDRootPairing_base 2) r t - 1)
  rw [rootMatrix_sub_one]
  exact (((negative_dividedPower_lowers P r hr 1 (by decide)).smul _ t).add _
    ((negative_dividedPower_lowers P r hr 2 (by decide)).smul _ (t ^ 2))).add _
    ((negative_dividedPower_lowers P r hr 3 (by decide)).smul _ (t ^ 3))

end
end Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
