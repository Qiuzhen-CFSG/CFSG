module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.FixedWitnesses
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.Matrices

/-!
# Fixed positive normalization detects the Weyl chamber

Suppose an actual fixed matrix is monomial on the root columns, with a
specified Weyl permutation and nonzero column scalars. If it normalizes the
fixed positive subgroup, the fixed words detecting the four simple-root
coordinates force every simple root to have positive Weyl image. Otherwise,
comparing a negative-root/Cartan entry in `(n x n⁻¹)n = n x` gives zero on
the left and a nonzero entry on the right. Minimal Weyl-word length then
forces the Weyl element to be one, so the matrix is height triangular.

The monomial Weyl presentation is an explicit premise. This module does not
infer that fixed-positive normalization implies split-positive normalization,
and it makes no claim that every normalizer word has already been presented
in this way. All fixed-coordinate witnesses are constructed here through
`FixedWitnesses`; no simplicity or Sylow premise is needed, even at `m = 0`.

The chamber argument extends
`ParabolicAmalgam/BinaryLocals/FixedGeometry/WeylSeparation.lean`.
Source: Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of
`refs/quasithin.pdf`, and the Chevalley positive-chamber argument.
-/

public section

namespace ReeF4.Parabolics.Overlap
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction LargeLocalSeeds
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry
noncomputable section
private local instance fixedSeparationIndexNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg

private def height (r : F4Chevalley.Root) := basisDegree (.inr r)
private theorem height_simple (i : Fin 4) : height (typeF4SimpleRootIndex i) = 1 := by
  have hp (j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [height, basisDegree, chevalleyBasisWeight, hp]
  fin_cases i <;> norm_num [typeF4CartanMatrix, Fin.ext_iff]
private theorem height_add {i j k : F4Chevalley.Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    height k = height i + height j := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ k q =
      typeF4RootPairing.pairingIn ℤ i q + typeF4RootPairing.pairingIn ℤ j q := by
    simpa using typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ)
      (j := q) (show typeF4RootPairing.root k =
        (1 : ℤ) • typeF4RootPairing.root i + (1 : ℤ) • typeF4RootPairing.root j by simpa using h)
  simp only [height, basisDegree, chevalleyBasisWeight, hp]
  ring
private theorem height_pos {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) : 0 < height r := by
  have hs (i : F4Chevalley.Root) (hi : i ∈ typeF4RootPairing_base.support) :
      height i = 1 := by
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, height_simple]
  apply hr.induction_on_add
  · intro i hi; rw [hs i hi]; norm_num
  · intro i j k hk hi hj
    rw [height_add hk, hs j hj]
    omega
private theorem height_neg (r : F4Chevalley.Root) : height (-r) = -height r := by
  simp only [height, basisDegree, chevalleyBasisWeight, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left]
  ring
private theorem height_neg_of_not_pos (r : F4Chevalley.Root)
    (hr : ¬ typeF4RootPairing_base.IsPos r) : height r < 0 := by
  have hp := height_pos ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr)
  rw [height_neg] at hp
  omega
private def matrix (m : ℕ) : Model m →* Matrix F4Chevalley.BasisIndex
    F4Chevalley.BasisIndex (CoefficientField m) :=
  (Units.coeHom _).comp ((Subgroup.subtype _).comp (toSplitGroup m))

private theorem negative_cartan_entry {m : ℕ} {x : Model m} (hx : x ∈ unipotent m)
    (r : F4Chevalley.Root) (hr : ¬ typeF4RootPairing_base.IsPos r)
    (j : typeF4RootPairing_base.support) : matrix m x (.inr r) (.inl j) = 0 := by
  have hh := height_neg_of_not_pos r hr
  change (toSplitGroup m x).val.val _ _ = 0
  rw [splitUnipotent_entry hx _ _ (by simpa only [basisDegree_cartan, height] using le_of_lt hh)]
  simp

private theorem weyl_eq_one_of_simple_positive (w : typeF4RootPairing.weylGroup)
    (hp : ∀ i : typeF4RootPairing_base.support,
      typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm w i)) : w = 1 := by
  let b := typeF4RootPairing_base
  obtain ⟨l, hlen, hprod⟩ := b.wordLength_spec w
  by_cases hl : l = []
  · subst l
    simpa using hprod.symm
  · let j := l.getLast hl
    let p := l.dropLast
    have he : p ++ [j] = l := List.dropLast_append_getLast hl
    have hw : w * b.simpleReflection j = b.wordProd p := by
      rw [← hprod, ← he, b.wordProd_append]
      change (b.wordProd p * b.simpleReflection j) * b.simpleReflection j = _
      rw [mul_assoc, b.simpleReflection_mul_self, mul_one]
    have hbound := b.wordLength_le (w * b.simpleReflection j) p hw.symm
    have hinc := b.wordLength_mul_simpleReflection_of_isPos w j (hp j)
    have hlens : p.length + 1 = l.length := by rw [← he]; simp
    omega

/-- Fixed positive coordinate witnesses rule out every nonidentity Weyl action
of a matrix normalizing the fixed positive subgroup. -/
theorem weyl_eq_one_of_normalizes_fixedUnipotent {m : ℕ} (n : Model m)
    (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ)
    (hmono : RootMonomial (toSplitGroup m n).val.val (typeF4RootPairing.weylGroupToPerm w) c)
    (hN : n ∈ normalizer (unipotent m : Set (Model m))) : w = 1 := by
  classical
  apply weyl_eq_one_of_simple_positive
  intro i
  obtain ⟨k, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  obtain ⟨x, hx, j, hj⟩ := FixedWitnesses.exists_simple_coordinate m k
  by_contra hneg
  let r := typeF4SimpleRootIndex k
  let e := typeF4RootPairing.weylGroupToPerm w
  have hxc : n * x * n⁻¹ ∈ unipotent m := (mem_normalizer_iff.mp hN x).mp hx
  have he : matrix m (n * x * n⁻¹) * matrix m n = matrix m n * matrix m x := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hleft : (matrix m (n * x * n⁻¹) * matrix m n) (.inr (e r)) (.inl j) = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    cases z with
    | inl q => rw [negative_cartan_entry hxc (e r) hneg q, zero_mul]
    | inr q =>
      have hz : matrix m n (.inr q) (.inl j) = 0 := hmono.2 q j
      rw [hz, mul_zero]
  have hright : (matrix m n * matrix m x) (.inr (e r)) (.inl j) =
      (c r : CoefficientField m) * matrix m x (.inr r) (.inl j) := by
    rw [Matrix.mul_apply]
    calc
      _ = ∑ z, (if z = .inr r then (c r : CoefficientField m) else 0) *
          matrix m x z (.inl j) := by
        apply Finset.sum_congr rfl
        intro z _
        congr 1
        exact (rootMonomial_row hmono (e r) z).trans (by simp [e])
      _ = _ := by simp
  have he' := congrArg (fun A => A (.inr (e r)) (.inl j)) he
  rw [hleft, hright] at he'
  exact (mul_ne_zero (Units.ne_zero _) hj) he'.symm

/-- An identity root permutation has no height-lowering matrix entries,
including in the degree-zero Cartan block. -/
theorem heightTriangular_of_rootMonomial_one {m : ℕ} (n : SplitGroup m)
    (c : F4Chevalley.Root → (CoefficientField m)ˣ)
    (hmono : RootMonomial n.val.val 1 c) : IsHeightTriangular n := by
  intro i j hij
  cases j with
  | inl q =>
    cases i with
    | inl p => simp only [basisDegree_cartan] at hij; omega
    | inr r => exact hmono.2 r q
  | inr r =>
    rw [hmono.1]
    apply if_neg
    intro he
    simp only [Equiv.Perm.one_apply] at he
    subst i
    exact lt_irrefl _ hij

/-- The matrix-separation step is conditional only on an actual Weyl monomial
presentation; it does not assume normalization of the split positive subgroup. -/
theorem normalizer_heightTriangular_of_weyl_monomial {m : ℕ} (n : Model m)
    (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ)
    (hmono : RootMonomial (toSplitGroup m n).val.val (typeF4RootPairing.weylGroupToPerm w) c)
    (hN : n ∈ normalizer (unipotent m : Set (Model m))) :
    IsHeightTriangular (toSplitGroup m n) := by
  have hw := weyl_eq_one_of_normalizes_fixedUnipotent n w c hmono hN
  subst w
  rw [map_one] at hmono
  exact heightTriangular_of_rootMonomial_one _ c hmono

end
end ReeF4.Parabolics.Overlap
