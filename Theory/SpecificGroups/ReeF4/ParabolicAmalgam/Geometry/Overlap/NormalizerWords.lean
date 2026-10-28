module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.NormalizerWords.Tits
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.Grading
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness
/-!
# Weyl action and triangular torus kernel of Ree normalizer words

Factor the actual rank-one normalizer words into a diagonal element and a
matrix with unscaled Weyl root columns. This gives the Weyl-monomial presentation.
If the original matrix is height triangular, a negative image of a simple root
would put a nonzero root-column entry strictly below its permitted height.
Hence the Weyl element preserves the positive chamber and is the identity.

The residual Tits matrix fixes every root vector. Restricted adjoint transport
then fixes the short simple Cartan vectors, and faithfulness of the short ideal
makes the entire matrix the identity. This argument works in the full split
carrier for every parameter, including `m = 0`, without simplicity or fixed-point
hypotheses. The root-vector argument extends the binary fixed-group proof in
`BinaryLocals/FixedGeometry/WeylSeparation/RootFaithfulness.lean`; the height and
chamber arguments adapt `Overlap/FixedSeparation.lean`, preserving both originals.

Source: the Chevalley normalizer and positive-chamber argument in GLS3 1.12.1,
used for the actual subgroup amalgam in Aschbacher–Smith F.1.4–5 and
F.1.12(I)(5), printed pp.260,263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Overlap
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry LargeLocalSeeds
open WordRelations WordRelations.Faithfulness WordRelations.Faithfulness.Adjoint
open WordRelations.Faithfulness.RestrictedAdjoint
open scoped Matrix
private local instance normalizerWordsIndexNeg : InvolutiveNeg F4Chevalley.Root :=
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


private theorem cast_e_neg (m : ℕ) (i : typeF4RootPairing_base.support) :
    (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) *ᵥ
      Pi.single (Sum.inr (-i.val)) 1 = Pi.single (Sum.inl i) 1 := by
  have h := congrArg (fun v : F4Chevalley.BasisIndex → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v)
      (eMatrix_mulVec_v_neg (P := typeF4RootPairing) i)
  have hm (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ)
      (v : F4Chevalley.BasisIndex → ℤ) :
      (Int.castRingHom (CoefficientField m)) ∘ (A *ᵥ v) =
        A.map (Int.castRingHom (CoefficientField m)) *ᵥ
          ((Int.castRingHom (CoefficientField m)) ∘ v) := by
    ext i
    exact (Int.castRingHom (CoefficientField m)).map_mulVec A v i
  have hs (j : F4Chevalley.BasisIndex) :
      (Int.castRingHom (CoefficientField m)) ∘ Pi.single j (1 : ℤ) = Pi.single j 1 := by
    classical
    ext x
    simp [Pi.single_apply]
  simpa only [hm, u, v, hs] using h


private theorem split_eq_one_of_fixes_roots {m : ℕ} (n : SplitGroup m)
    (hfix : ∀ r : F4Chevalley.Root,
      n.val.val *ᵥ Pi.single (Sum.inr r) 1 = Pi.single (Sum.inr r) 1) : n = 1 := by
  let g : MatrixUnits m := n.val
  have hg : g ∈ Subgroup.closure (Set.range
      (fun rt : F4Chevalley.Root × CoefficientField m => F4Chevalley.rootCurve rt.1 rt.2)) :=
    n.property
  have heq := generated_equivariantOnShort m g hg
  have hcart (i : typeF4RootPairing_base.support) (hi : IsShortRoot i.val) :
      n.val.val *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1 := by
    have hE : (F4Chevalley.integralOperators.rootOperator i.val).map
        (Int.castRingHom (CoefficientField m)) =
      (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) :=
      congrArg (fun A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ =>
        A.map (Int.castRingHom (CoefficientField m))) (rootOperator_simple i)
    have hc := heq (Pi.single (Sum.inr i.val) 1) (shortSupported_single _ hi)
    change adjointMap m (n.val.val *ᵥ Pi.single (Sum.inr i.val) 1) * n.val.val =
      n.val.val * adjointMap m (Pi.single (Sum.inr i.val) 1) at hc
    rw [hfix, adjointMap_root_single, hE] at hc
    have hh := congrArg (fun A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
      (CoefficientField m) => A *ᵥ Pi.single (Sum.inr (-i.val)) 1) hc
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix, cast_e_neg m] at hh
    exact hh.symm
  have hg1 : g = 1 := eq_one_of_fixes_short_coordinates m g hg (by
    intro j hj
    cases j with
    | inr r => exact hfix r
    | inl i => exact hcart i hj)
  exact Subtype.ext hg1

private theorem torus_monomial {m : ℕ} {d : SplitGroup m} (hd : d ∈ diagonalTorus m) :
    ∃ c : F4Chevalley.Root → (CoefficientField m)ˣ,
      RootMonomial d.val.val (Equiv.refl _) c := by
  classical
  obtain ⟨u, hu⟩ := hd
  change diagonalTorusHom m u = d.val at hu
  rw [← hu]
  refine ⟨fun r => chevalleyBasisTorusUnit (P := typeF4RootPairing) u (.inr r), ?_, ?_⟩
  · intro a r
    change Matrix.diagonal _ a (.inr r) = _
    by_cases h : a = .inr r
    · subst a; simp
    · simp [h]
  · intro r i
    change (Matrix.diagonal _ : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
      (CoefficientField m)) (.inr r) (.inl i) = 0
    simp

private theorem torus_mul_monomial {m : ℕ} {d k : SplitGroup m}
    (hd : d ∈ diagonalTorus m) (w : typeF4RootPairing.weylGroup)
    (hk : RootMonomial k.val.val (typeF4RootPairing.weylGroupToPerm w) (fun _ => 1)) :
    ∃ c : F4Chevalley.Root → (CoefficientField m)ˣ,
      RootMonomial (d * k).val.val (typeF4RootPairing.weylGroupToPerm w) c := by
  obtain ⟨c, hc⟩ := torus_monomial hd
  refine ⟨fun r => c (typeF4RootPairing.weylGroupToPerm w r), ?_⟩
  simpa only [show Equiv.refl F4Chevalley.Root = 1 from rfl, one_mul, mul_one,
    Subgroup.coe_mul, Units.val_mul] using
    rootMonomial_mul hc hk

/-- Every word in the actual rank-one normalizer generators has a Weyl root
permutation and nonzero root-column scalars, also over the binary field. -/
theorem normalizerWords_weylMonomial {m : ℕ} (hT : splitTorus m = diagonalTorus m)
    {n : SplitGroup m} (hn : n ∈ splitNormalizerWords m) :
    ∃ (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ),
      RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c := by
  obtain ⟨d, hd, k, w, rfl, hk⟩ := NormalizerWords.normalizerWords_torus_weyl hT hn
  obtain ⟨c, hc⟩ := torus_mul_monomial hd w hk
  exact ⟨w, c, hc⟩

private theorem weyl_eq_one_of_heightTriangular {m : ℕ} {n : SplitGroup m}
    (hn : IsHeightTriangular n) (w : typeF4RootPairing.weylGroup)
    (c : F4Chevalley.Root → (CoefficientField m)ˣ)
    (hmono : RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c) : w = 1 := by
  apply weyl_eq_one_of_simple_positive
  intro i
  by_contra hi
  have hneg := height_neg_of_not_pos _ hi
  have hpos := height_pos (typeF4RootPairing_base.isPos_of_mem_support i.property)
  have hz := hn (.inr (typeF4RootPairing.weylGroupToPerm w i)) (.inr i)
    (lt_trans hneg hpos)
  rw [hmono.1, if_pos rfl] at hz
  exact (c i).ne_zero hz

/-- A height-triangular word in the actual rank-one normalizer generators is a
diagonal torus element. No fixed-point or positive-normalizer premise is required. -/
theorem normalizerWord_mem_diagonalTorus_of_heightTriangular {m : ℕ}
    (hT : splitTorus m = diagonalTorus m) {n : SplitGroup m}
    (hn : n ∈ splitNormalizerWords m) (htri : IsHeightTriangular n) :
    n ∈ diagonalTorus m := by
  obtain ⟨d, hd, k, w, he, hk⟩ := NormalizerWords.normalizerWords_torus_weyl hT hn
  obtain ⟨c, hc⟩ := torus_mul_monomial hd w hk
  rw [← he] at hc
  have hw := weyl_eq_one_of_heightTriangular htri w c hc
  subst w
  have hk1 : k = 1 := split_eq_one_of_fixes_roots k (by
    intro r
    ext i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, map_one,
      Equiv.Perm.one_apply, Units.val_one, Pi.single_apply] using hk.1 i r)
  simpa only [he, hk1, mul_one] using hd
end ReeF4.Parabolics.Overlap
