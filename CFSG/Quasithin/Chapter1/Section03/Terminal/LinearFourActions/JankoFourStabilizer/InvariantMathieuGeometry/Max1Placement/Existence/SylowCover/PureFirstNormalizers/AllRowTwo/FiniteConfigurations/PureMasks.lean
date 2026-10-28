module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.RowGeometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.MarkedCoordinates

/-!
# Pure masks and extension certificates in the marked intersection

The existing native conjugacy forest and displacement ranks identify every
pure element in the certified 128-element intersection. Exact mask arithmetic
then enumerates the extensions of the marked plane to eight, the extensions
of each eight to sixteen, and excludes all further pure extensions. The five
extra pure sixteen lists are retained explicitly: purity alone does not
exclude them. The independent-pair rank condition is discharged separately.
Source: Kleidman--Wilson (1988), Corollary 1.2.2(a), Section 2.1, pp.488--489.
All finite checks use kernel reduction; the saved diagnostics are not proofs.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open MarkedIntersection
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.Coordinates
open Cardinality.LocalInvolutionCensus.FiberCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
attribute [local instance 2000] Finset.decidableDforallFinset
attribute [local instance 2000] Finset.decidableExistsAndFinset
set_option Elab.async false

@[expose] def pureMasks : Finset (Fin 8192) := {0,1,6,7,198,199,564,565,1246,1247,1578,1579,2384,2385,2390,2391,2448,2449,2916,2917,2978,2979,2980,2981,3400,3401,3464,3465,3962,3963,4026,4027,4028,4029,4190,4191,4248,4249,4254,4255,4714,4715,4716,4717,4778,4779,5190,5191,5254,5255,5746,5747,5748,5749,5812,5813,6408,6409,6600,6601,6606,6607,7162,7163,7440,7441,8164,8165}

@[expose] def extraMasks : Fin 5 → Finset (Fin 8192) := ![
  {0,1,6,7,2978,2979,2980,2981,4714,4715,4716,4717,6600,6601,6606,6607},
  {0,1,198,199,3962,3963,4028,4029,5746,5747,5812,5813,6408,6409,6606,6607},
  {0,1,564,565,2384,2385,2916,2917,4254,4255,4778,4779,6606,6607,7162,7163},
  {0,1,1246,1247,2390,2391,3464,3465,4248,4249,5190,5191,6606,6607,7440,7441},
  {0,1,1578,1579,2448,2449,4026,4027,4190,4191,5748,5749,6606,6607,8164,8165}]

@[expose] def pureSixteenMasks (i : Fin 15) : Finset (Fin 8192) :=
  if h : i.val < 10 then rowMasks (sixteenIndex ⟨i.val,h⟩)
  else extraMasks ⟨i.val-10,by omega⟩

@[expose] def planeMasks : Finset (Fin 8192) := {0,1,6606,6607}

@[expose] def maskMul (m n : Fin 8192) : Fin 8192 :=
  ⟨fastMultiply m.val n.val % 8192, Nat.mod_lt _ (by decide)⟩

theorem nativeWord_mul (m n : Fin 8192) :
    nativeWord (maskMul m n) = nativeWord m * nativeWord n := by
  have he : fastMultiply m.val n.val = maskMultiply m.val n.val := by
    simp only [fastMultiply,maskMultiply,correction_fast]
  have hb : maskMultiply m.val n.val < 8192 := by
    apply Nat.xor_lt_two_pow (n := 13) (Nat.xor_lt_two_pow m.isLt n.isLt)
    cases correction m.val n.val <;> decide
  change ((maskProduct kernelFactor (fastMultiply m.val n.val % 8192) : sourceSubgroup) : Model) = _
  rw [he,Nat.mod_eq_of_lt hb,source_mask_multiply]
  rfl

private theorem rank_a : displacementRank a = 50 := by
  have hr := congrArg Prod.fst (sourceRepresentative_rankPair 1)
  change displacementRank (sourceRepresentative 1 : Model) = 50 at hr
  have hc : IsConj a (sourceRepresentative 1 : Model) := by
    have h1 : sourceRepresentative 1 = sourceSeed ^ 2 := by
      change kernelFactor 0 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1)))))))))))) * 1 = _
      simp only [mul_one]
      rfl
    rw [h1,coe_sourceSeed_sq]
    exact (isConj_iff.mpr ⟨h⁻¹,by simpa only [inv_inv] using conjugates_t⟩).symm
  exact (displacementRank_of_isConj hc).trans hr

theorem pure_nativeWord_mem_masks (m : Fin 8192)
    (hp : IsConj a (nativeWord m)) : m ∈ masks 1 ∨ m ∈ masks 2 := by
  have hs : (sourceElement 0 m) ^ 2 = 1 := by
    apply Subtype.ext
    have hh := IsConj.pow 2 hp
    have ha : a ^ 2 = 1 := by simpa only [orderOf_a] using pow_orderOf_eq_one a
    rw [ha,isConj_one_right] at hh
    simpa only [sourceElement,sourceLift,Matrix.cons_val_zero,mul_one,Subgroup.coe_pow,Subgroup.coe_one,nativeWord] using hh
  obtain ⟨k,hk,hm,hc⟩ := source_forest Cardinality.Thompson.max2_card.le 0 m hs
  have hc' : IsConj (sourceRepresentative k : Model) (sourceElement 0 m : Model) :=
    (sourceSubgroup.subtype).map_isConj hc
  have he : (expectedRanks k).1 = 50 := by
    rw [← sourceRepresentative_rankPair]
    change displacementRank (sourceRepresentative k : Model) = 50
    rw [displacementRank_of_isConj hc']
    have h0 : (sourceElement 0 m : Model) = nativeWord m := by
      change ((kernelProduct m * 1 : sourceSubgroup) : Model) = _
      rw [mul_one]
      rfl
    rw [h0,← displacementRank_of_isConj hp,rank_a]
  have ht : ∀ k : Fin 11, fiberIndex k = 0 → (expectedRanks k).1 = 50 → k = 1 ∨ k = 2 := by
    decide +kernel
  rcases ht k hk he with rfl | rfl
  · exact Or.inl hm
  · exact Or.inr hm

theorem marked_pure_mask (m : Fin 8192)
    (hi : nativeWord m ∈ markedIntersection)
    (hp : nativeWord m = 1 ∨ IsConj a (nativeWord m)) : m ∈ pureMasks := by
  obtain ⟨i,hi⟩ := (mem_markedIntersection_iff _).mp hi
  have he : coordinate i = m := nativeWord_injective hi
  rcases hp with hp | hp
  · have hm : m = 0 := nativeWord_injective (hp.trans nativeWord_zero.symm)
    exact hm.symm ▸ (by decide +kernel : (0 : Fin 8192) ∈ pureMasks)
  · have hh := pure_nativeWord_mem_masks m hp
    have ht : ∀ i : Fin 128, coordinate i ∈ masks 1 ∨ coordinate i ∈ masks 2 →
        coordinate i ∈ pureMasks := by decide +kernel
    exact he ▸ ht i (he.symm ▸ hh)

theorem extend_plane : ∀ m ∈ pureMasks, m ∉ planeMasks →
    ∃ i : Fin 16, rowMasks (eightIndex i) =
      planeMasks ∪ planeMasks.image (maskMul m) := by decide +kernel

set_option maxRecDepth 10000 in
theorem extend_eight : ∀ i : Fin 16, ∀ m ∈ pureMasks,
    m ∉ rowMasks (eightIndex i) →
    (∀ n ∈ rowMasks (eightIndex i), maskMul m n ∈ pureMasks) →
    ∃ j : Fin 15, pureSixteenMasks j =
      rowMasks (eightIndex i) ∪ (rowMasks (eightIndex i)).image (maskMul m) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem no_extend_sixteen : ∀ i : Fin 15, ∀ m ∈ pureMasks,
    (∀ n ∈ pureSixteenMasks i, maskMul m n ∈ pureMasks) → m ∈ pureSixteenMasks i := by
  decide +kernel

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
