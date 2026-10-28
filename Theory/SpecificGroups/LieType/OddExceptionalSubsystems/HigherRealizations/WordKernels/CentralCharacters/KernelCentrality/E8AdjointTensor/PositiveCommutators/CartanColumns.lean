module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.SimpleCommutators
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyBrackets

/-!
# Source-signed Cartan columns for the relative E6 tensor in E8

The literal saturated root embedding preserves reflections and root strings.
Induction along a mapped SOURCE Tits word therefore gives the same carrier
signs as in E6. The signed simple Cartan-column formulas transport along that
word; the two source carrier signs cancel. This proves the exact Cartan
columns of `rootTensor`, without comparing it to an ambient canonical route.

The sum-root commutator proof uses these columns to determine its integer
coefficient. Adapted from the checked F4 proof in
`F4Identification.WordDescent.CoverCenter.Equivariance.PositiveCommutators.CartanColumns`.
Source: GLS3 §§1.10–1.12 and 2.6.2, the common integral lattice for a closed
root subsystem (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
attribute [local instance] Classical.decEq
local instance : Fintype typeE8Roots := Fintype.ofFinite _

lemma embedded_base (i : typeE6RootPairing_base.support) :
    AdjointBlocks.rootE8 i = (AdjointBlocks.baseE8 i : typeE8Roots) :=
  AdjointBlocks.e8Embedding.base_root i

lemma embedded_pairing (r s : typeE6Roots) :
    typeE8RootPairing.pairing (AdjointBlocks.rootE8 r) (AdjointBlocks.rootE8 s) =
      typeE6RootPairing.pairing r s := by
  simp only [typeE8RootPairing_pairing, typeE6RootPairing_pairing]
  rfl

lemma embedded_root (r : typeE6Roots) :
    AdjointBlocks.e8Embedding.weight (typeE6RootPairing.root r) =
      typeE8RootPairing.root (AdjointBlocks.rootE8 r) :=
  AdjointBlocks.e8Embedding.root r

lemma embedded_reflection (i : typeE6RootPairing_base.support) (r : typeE6Roots) :
    typeE8RootPairing.reflectionPerm (AdjointBlocks.baseE8 i) (AdjointBlocks.rootE8 r) =
      AdjointBlocks.rootE8 (typeE6RootPairing.reflectionPerm i r) := by
  apply typeE8RootPairing.root.injective
  rw [← embedded_root, typeE6RootPairing.root_reflectionPerm,
    typeE6RootPairing.reflection_apply_root, map_sub, map_smul,
    embedded_root, embedded_root,
    typeE8RootPairing.root_reflectionPerm, typeE8RootPairing.reflection_apply_root,
    ← embedded_base, embedded_pairing]

lemma embedded_neg (r : typeE6Roots) :
    let := typeE6RootPairing.indexNeg
    let := typeE8RootPairing.indexNeg
    AdjointBlocks.rootE8 (-r) = -AdjointBlocks.rootE8 r :=
  AdjointBlocks.e8Embedding.neg_index r

lemma embedded_word (w : List typeE6RootPairing_base.support) (r : typeE6Roots) :
    reflectionWord (P := typeE8RootPairing) (w.map AdjointBlocks.baseE8)
      (AdjointBlocks.rootE8 r) = AdjointBlocks.rootE8 (reflectionWord w r) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, reflectionWord, ih, embedded_reflection]

lemma embedded_chainBot (i : typeE6RootPairing_base.support) (r : typeE6Roots) :
    typeE8RootPairing.chainBotCoeff (AdjointBlocks.baseE8 i) (AdjointBlocks.rootE8 r) =
      typeE6RootPairing.chainBotCoeff i r := by
  rw [← embedded_base]
  exact AdjointBlocks.e8Embedding.chainBotCoeff i r

lemma embedded_cartan (i j : typeE6RootPairing_base.support) :
    typeE8RootPairing_base.cartanMatrix (AdjointBlocks.baseE8 i) (AdjointBlocks.baseE8 j) =
      typeE6RootPairing_base.cartanMatrix i j :=
  AdjointBlocks.e8Embedding.cartan i j

lemma embedded_root_add (i : typeE6RootPairing_base.support) (r s : typeE6Roots)
    (h : typeE6RootPairing.root s = typeE6RootPairing.root i + typeE6RootPairing.root r) :
    typeE8RootPairing.root (AdjointBlocks.rootE8 s) =
      typeE8RootPairing.root (AdjointBlocks.baseE8 i) +
        typeE8RootPairing.root (AdjointBlocks.rootE8 r) := by
  simpa only [map_add, embedded_root, embedded_base] using
    congrArg AdjointBlocks.e8Embedding.weight h

lemma embedded_titsLift_v (i : typeE6RootPairing_base.support) (r : typeE6Roots) :
    titsLift (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) *ᵥ
        v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 r) =
      ((-1 : ℤ) ^ typeE6RootPairing.chainBotCoeff i r) •
        v (b := typeE8RootPairing_base)
          (AdjointBlocks.rootE8 (typeE6RootPairing.reflectionPerm i r)) := by
  rw [titsLift_mulVec_v, embedded_chainBot, embedded_reflection]

lemma embedded_eMatrix_v_add (i : typeE6RootPairing_base.support) (r s : typeE6Roots)
    (h : typeE6RootPairing.root s = typeE6RootPairing.root i + typeE6RootPairing.root r) :
    eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) *ᵥ
        v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 r) =
      (typeE6RootPairing.chainBotCoeff i r + 1 : ℤ) •
        v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 s) := by
  rw [eMatrix_mulVec_v_add (embedded_root_add i r s h), embedded_chainBot]

private lemma pairingIn_reflect (i j : typeE6RootPairing_base.support) (r : typeE6Roots) :
    typeE6RootPairing.pairingIn ℤ (typeE6RootPairing.reflectionPerm i r) j =
      typeE6RootPairing.pairingIn ℤ r j - typeE6RootPairing_base.cartanMatrix i j *
        typeE6RootPairing.pairingIn ℤ r i := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  simp only [map_sub, map_mul, RootPairing.algebraMap_pairingIn,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  change typeE6RootPairing.toLinearMap
    (typeE6RootPairing.root (typeE6RootPairing.reflectionPerm i r))
      (typeE6RootPairing.coroot j) = _
  rw [typeE6RootPairing.root_reflectionPerm, typeE6RootPairing.reflection_apply_root]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
  rw [typeE6RootPairing.root_coroot_eq_pairing, typeE6RootPairing.root_coroot_eq_pairing]
  ring

private lemma titsLiftInv_cartan (i j : typeE8RootPairing_base.support) :
    titsLiftInv (P := typeE8RootPairing) i *ᵥ u j =
      u j - |typeE8RootPairing_base.cartanMatrix i j| • u i := by
  have hfix : titsLift (P := typeE8RootPairing) i *ᵥ (titsLift i *ᵥ u j) = u j := by
    rw [titsLift_mulVec_u, Matrix.mulVec_sub, Matrix.mulVec_smul,
      titsLift_mulVec_u, titsLift_mulVec_u]
    have hii : |typeE8RootPairing_base.cartanMatrix i i| = 2 := by simp
    rw [hii]
    module
  calc
    _ = titsLiftInv i *ᵥ (titsLift i *ᵥ (titsLift i *ᵥ u j)) := by rw [hfix]
    _ = titsLift i *ᵥ u j := by
      rw [Matrix.mulVec_mulVec, titsLift_inv_mul, Matrix.one_mulVec]
    _ = _ := titsLift_mulVec_u i j

private lemma transported_cartan_columns (r : typeE6Roots)
    (A : Matrix TargetIndex TargetIndex ℤ)
    (hA : ∀ j : typeE6RootPairing_base.support, A *ᵥ u (AdjointBlocks.baseE8 j) =
      (simpleOperatorOrientation (b := typeE6RootPairing_base) j *
        typeE6RootPairing.pairingIn ℤ r j) • v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 r))
    (w : List typeE6RootPairing_base.support) (j : typeE6RootPairing_base.support) :
    transportedMatrix (P := typeE8RootPairing) (w.map AdjointBlocks.baseE8) A *ᵥ u (AdjointBlocks.baseE8 j) =
      (titsWordSign w r * simpleOperatorOrientation (b := typeE6RootPairing_base) j *
        typeE6RootPairing.pairingIn ℤ (reflectionWord w r) j) •
          v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 (reflectionWord w r)) := by
  induction w generalizing j with
  | nil => simpa [transportedMatrix, titsWord, titsWordSign, reflectionWord] using hA j
  | cons i w ih =>
      have hcons : transportedMatrix (P := typeE8RootPairing) ((i :: w).map AdjointBlocks.baseE8) A =
          titsLift (AdjointBlocks.baseE8 i) * transportedMatrix (w.map AdjointBlocks.baseE8) A * titsLiftInv (AdjointBlocks.baseE8 i) := by
        simp only [List.map_cons, transportedMatrix, titsWord, titsWordInv_cons, mul_assoc]
      rw [hcons, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, titsLiftInv_cartan, embedded_cartan,
        Matrix.mulVec_sub, Matrix.mulVec_smul, ih j, ih i,
        Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, embedded_titsLift_v]
      simp only [Matrix.mulVec_smul, embedded_titsLift_v, smul_smul, ← sub_smul,
        reflectionWord, titsWordSign, pairingIn_reflect]
      congr 1
      have h := simple_orientation_abs_cartan i j
      linear_combination -(titsWordSign w r *
        (-1 : ℤ) ^ typeE6RootPairing.chainBotCoeff i (reflectionWord w r) *
          typeE6RootPairing.pairingIn ℤ (reflectionWord w r) i) * h

private lemma signed_e_cartan (i j : typeE6RootPairing_base.support) :
    (simpleOperatorOrientation (b := typeE6RootPairing_base) i •
        eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)) *ᵥ u (AdjointBlocks.baseE8 j) =
      (simpleOperatorOrientation (b := typeE6RootPairing_base) j *
        typeE6RootPairing.pairingIn ℤ i j) • v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 i) := by
  rw [Matrix.smul_mulVec, eMatrix_mulVec_u, embedded_cartan, smul_smul, mul_comm,
    simple_orientation_abs_cartan, embedded_base]
  rfl

private lemma signed_f_cartan (i j : typeE6RootPairing_base.support) :
    let := typeE6RootPairing.indexNeg
    (-simpleOperatorOrientation (b := typeE6RootPairing_base) i •
        fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)) *ᵥ u (AdjointBlocks.baseE8 j) =
      (simpleOperatorOrientation (b := typeE6RootPairing_base) j *
        typeE6RootPairing.pairingIn ℤ (-i : typeE6Roots) j) •
          v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 (-i : typeE6Roots)) := by
  let := typeE6RootPairing.indexNeg
  let := typeE8RootPairing.indexNeg
  dsimp only
  rw [Matrix.smul_mulVec, fMatrix_mulVec_u, embedded_cartan, smul_smul, neg_mul, mul_comm,
    simple_orientation_abs_cartan]
  rw [embedded_neg, embedded_base]
  simp only [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left,
    mul_neg]
  rfl

/-- Exact source-signed Cartan columns of the relative E8 root tensor. -/
lemma rootTensor_cartan_column (r : typeE6Roots)
    (j : typeE6RootPairing_base.support) :
    rootTensor r *ᵥ u (AdjointBlocks.baseE8 j) =
      (simpleOperatorOrientation (b := typeE6RootPairing_base) j *
        typeE6RootPairing.pairingIn ℤ r j) •
          v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 r) := by
  let := typeE6RootPairing.indexNeg
  by_cases hr : typeE6RootPairing_base.IsPos r
  · let z := rootRoute (P := typeE6RootPairing) (b := typeE6RootPairing_base) r
    have ht : rootTensor r =
        titsWordSign z.word z.simple • transportedMatrix (z.word.map AdjointBlocks.baseE8)
          (simpleOperatorOrientation (b := typeE6RootPairing_base) z.simple •
            eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 z.simple)) := by
      simp only [rootTensor, if_pos hr, simpleRouteOperatorOrientation,
        if_true, signedSimpleOperatorOrientation_true,
        transportedMatrix, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rfl
    rw [ht, Matrix.smul_mulVec, transported_cartan_columns _ _ (signed_e_cartan z.simple)]
    simp only [smul_smul, ← mul_assoc, titsWordSign_mul_self, one_mul, z.target]
  · let z := rootRoute (P := typeE6RootPairing) (b := typeE6RootPairing_base) (-r)
    have ht : rootTensor r =
        titsWordSign z.word (-z.simple : typeE6Roots) •
          transportedMatrix (z.word.map AdjointBlocks.baseE8)
          (-simpleOperatorOrientation (b := typeE6RootPairing_base) z.simple •
            fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 z.simple)) := by
      simp only [rootTensor, if_neg hr, simpleRouteOperatorOrientation,
        Bool.false_eq_true, if_false, signedSimpleOperatorOrientation_false,
        transportedMatrix, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rfl
    rw [ht, Matrix.smul_mulVec,
      transported_cartan_columns _ _ (signed_f_cartan z.simple)]
    simp only [smul_smul, ← mul_assoc, titsWordSign_mul_self, one_mul,
      reflectionWord_neg, z.target, neg_neg]

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
