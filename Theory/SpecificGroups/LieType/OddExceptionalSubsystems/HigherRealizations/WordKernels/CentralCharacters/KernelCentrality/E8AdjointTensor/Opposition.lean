module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.Candidate
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.OppositionTransfer
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.Opposition.IntegralWords


/-!
# Signed opposition for the E6 tensor on the E8 lattice

The literal E6 root inclusion preserves reflections and complete root strings,
so the source Tits carrier signs equal the signs along the mapped E8 word.
The integral opposition correction is the product of the two opposite carrier
signs. The fixed source route orientation cancels that product and leaves the
required minus sign. Cartan operators satisfy the same identity because
opposition reverses their raising/lowering commutator.

Linear extension proves `D(Ω₆ x) = -(Ω₈ * D(x) * Ω₈)` for the fixed tensor.
The final application supplies the opposition premise of the existing transfer
to negative commutators; the independent positive calculation remains explicit.

This adapts the checked F4 opposition argument using the actual E6-to-E8
embedding, without identifying the two lattices or commuting opposition with
an integral Tits word. Source: GLS3 §§1.10–1.12 and 2.6.2,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Classical
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
attribute [local instance] Classical.decEq
local instance : Fintype typeE8Roots := Fintype.ofFinite _

private lemma rootE8_root (r : typeE6Roots) :
    typeE8RootPairing.root (AdjointBlocks.rootE8 r) =
      (typeE6RootPairing.root r).val := rfl

private lemma rootE8_simple (i : typeE6RootPairing_base.support) :
    AdjointBlocks.rootE8 i = (AdjointBlocks.baseE8 i : typeE8Roots) :=
  AdjointBlocks.e8Embedding.base_root i

private lemma rootE8_chain (i j : typeE6Roots) :
    typeE8RootPairing.chainBotCoeff (AdjointBlocks.rootE8 i) (AdjointBlocks.rootE8 j) =
      typeE6RootPairing.chainBotCoeff i j := AdjointBlocks.e8Embedding.chainBotCoeff i j

private lemma rootE8_reflection (i j : typeE6Roots) :
    AdjointBlocks.rootE8 (typeE6RootPairing.reflectionPerm i j) =
      typeE8RootPairing.reflectionPerm (AdjointBlocks.rootE8 i) (AdjointBlocks.rootE8 j) := by
  apply typeE8RootPairing.root.injective
  rw [rootE8_root, typeE6RootPairing.root_reflectionPerm,
    typeE6RootPairing.reflection_apply_root, Submodule.coe_sub, Submodule.coe_smul,
    typeE8RootPairing.root_reflectionPerm, typeE8RootPairing.reflection_apply_root,
    typeE6RootPairing_pairing, typeE8RootPairing_pairing]
  rfl

private lemma rootE8_neg (r : typeE6Roots) :
    let := typeE6RootPairing.indexNeg
    let := typeE8RootPairing.indexNeg
    AdjointBlocks.rootE8 (-r) = -AdjointBlocks.rootE8 r :=
  AdjointBlocks.e8Embedding.neg_index r

private lemma reflectionWord_map (w : List typeE6RootPairing_base.support) (r : typeE6Roots) :
    reflectionWord (P := typeE8RootPairing) (w.map AdjointBlocks.baseE8)
        (AdjointBlocks.rootE8 r) =
      AdjointBlocks.rootE8 (reflectionWord (P := typeE6RootPairing) w r) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [List.map_cons, reflectionWord, ih]
      rw [← rootE8_simple, ← rootE8_reflection]

private lemma titsWordSign_map (w : List typeE6RootPairing_base.support) (r : typeE6Roots) :
    titsWordSign (P := typeE8RootPairing) (w.map AdjointBlocks.baseE8)
        (AdjointBlocks.rootE8 r) =
      titsWordSign (P := typeE6RootPairing) w r := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [List.map_cons, titsWordSign, ih, reflectionWord_map]
      rw [← rootE8_simple, rootE8_chain]

private lemma titsWordOppositionSign_map (w : List typeE6RootPairing_base.support)
    (i : typeE6RootPairing_base.support) :
    titsWordOppositionSign (P := typeE8RootPairing) (w.map AdjointBlocks.baseE8)
        (AdjointBlocks.baseE8 i) =
      titsWordOppositionSign (P := typeE6RootPairing) w i := by
  let := typeE6RootPairing.indexNeg
  let := typeE8RootPairing.indexNeg
  simp only [titsWordOppositionSign]
  rw [← rootE8_simple, ← rootE8_neg, titsWordSign_map, titsWordSign_map]

private lemma tensor_opposite_pos (r : typeE6Roots)
    (hr : typeE6RootPairing_base.IsPos r) :
    let := typeE6RootPairing.indexNeg
    tensor (Sum.inr (-r)) =
      -(omegaMatrix (P := typeE8RootPairing) * tensor (Sum.inr r) * omegaMatrix) := by
  let := typeE6RootPairing.indexNeg
  dsimp only
  have hn : ¬typeE6RootPairing_base.IsPos (-r) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hr
  let q := rootRoute (P := typeE6RootPairing) (b := typeE6RootPairing_base) r
  rw [tensor, rootTensor, if_neg hn, neg_neg, tensor, rootTensor, if_pos hr]
  change simpleRouteOperatorOrientation false q.word q.simple •
      transportedMatrix (q.word.map AdjointBlocks.baseE8)
        (fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 q.simple)) =
    -(omegaMatrix * (simpleRouteOperatorOrientation true q.word q.simple •
      transportedMatrix (q.word.map AdjointBlocks.baseE8)
        (eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 q.simple))) * omegaMatrix)
  rw [Matrix.mul_smul, Matrix.smul_mul, omegaMatrix_conj_transported_eMatrix,
    titsWordOppositionSign_map]
  simp only [smul_smul, ← neg_smul, simpleRouteOperatorOrientation,
    Bool.false_eq_true, if_false, if_true, signedSimpleOperatorOrientation_false,
    signedSimpleOperatorOrientation_true, titsWordOppositionSign]
  congr 1
  calc
    _ = -(1 * (titsWordSign q.word (-q.simple) * simpleOperatorOrientation q.simple)) := by
      ring
    _ = -((titsWordSign q.word q.simple * titsWordSign q.word q.simple) *
        (titsWordSign q.word (-q.simple) * simpleOperatorOrientation q.simple)) := by
      rw [titsWordSign_mul_self_opposition]
    _ = _ := by ring

/-- Every pair of opposite source roots gives opposite-conjugate operators
on the literal E8 integral carrier. -/
lemma tensor_opposite (r : typeE6Roots) :
    let := typeE6RootPairing.indexNeg
    tensor (Sum.inr (-r)) =
      -(omegaMatrix (P := typeE8RootPairing) * tensor (Sum.inr r) * omegaMatrix) := by
  let := typeE6RootPairing.indexNeg
  dsimp only
  by_cases hr : typeE6RootPairing_base.IsPos r
  · exact tensor_opposite_pos r hr
  · have hn : typeE6RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    have h := tensor_opposite_pos (-r) hn
    simp only [neg_neg] at h
    rw [h]
    simp only [mul_neg, neg_mul, neg_neg]
    symm
    calc
      _ = (omegaMatrix * omegaMatrix) * tensor (Sum.inr (-r)) *
          (omegaMatrix * omegaMatrix) := by noncomm_ring
      _ = _ := by rw [omegaMatrix_sq, one_mul, mul_one]

/-- The source Cartan coordinate is fixed by opposition; its E8 commutator
operator is negated by conjugation. -/
lemma tensor_cartan_opposition (i : typeE6RootPairing_base.support) :
    tensor (Sum.inl i) =
      -(omegaMatrix (P := typeE8RootPairing) * tensor (Sum.inl i) * omegaMatrix) := by
  let O := omegaMatrix (P := typeE8RootPairing) (b := typeE8RootPairing_base)
  let E := eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)
  let F := fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)
  have he : O * E = F * O := omegaMatrix_mul_eMatrix (AdjointBlocks.baseE8 i)
  have hf : O * F = E * O := omegaMatrix_mul_fMatrix (AdjointBlocks.baseE8 i)
  have hoo : O * O = 1 := omegaMatrix_sq
  have hcomm : O * (E * F - F * E) * O = -(E * F - F * E) := by
    calc
      _ = (O * E) * F * O - (O * F) * E * O := by noncomm_ring
      _ = F * (O * F) * O - E * (O * E) * O := by
        conv_lhs => rw [he, hf]
        noncomm_ring
      _ = F * E * (O * O) - E * F * (O * O) := by
        conv_lhs => rw [hf, he]
        noncomm_ring
      _ = _ := by rw [hoo, mul_one, mul_one]; abel
  change -simpleOperatorOrientation i • (E * F - F * E) =
    -(O * (-simpleOperatorOrientation i • (E * F - F * E)) * O)
  rw [Matrix.mul_smul, Matrix.smul_mul, hcomm, smul_neg, neg_neg]

/-- Signed opposition covariance of the fixed E6 tensor on the E8 carrier,
with no commutator or equivariance premises. -/
theorem integral_opposition_covariance : IntegralOppositionCovariance := by
  have hb (j : Index) :
      adjointMap (omegaMatrix (P := typeE6RootPairing) *ᵥ Pi.single j 1) =
        -(omegaMatrix (P := typeE8RootPairing) * adjointMap (Pi.single j 1) * omegaMatrix) := by
    rcases j with i | r
    · change adjointMap (omegaMatrix *ᵥ u i) = _
      rw [omegaMatrix_mulVec_u, adjointMap_single]
      exact tensor_cartan_opposition i
    · let := typeE6RootPairing.indexNeg
      change adjointMap (omegaMatrix *ᵥ v r) = _
      rw [omegaMatrix_mulVec_v, adjointMap_single, adjointMap_single]
      exact tensor_opposite r
  intro x
  have hx : x = ∑ j, x j • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  rw [hx]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    ← Finset.sum_neg_distrib, ← smul_neg]
  exact Finset.sum_congr rfl (fun j _ => congrArg (fun A => x j • A) (hb j))

/-- Opposition discharges the negative-commutator branch once the independent
positive calculation is supplied by the tensor assembly. -/
theorem negativeCommutators_of_positive (hE : PositiveCommutators) : NegativeCommutators :=
  negativeCommutators_of_positive_and_opposition hE integral_opposition_covariance

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
