module
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.CorootTorus
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyBrackets
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.Generators

/-!
# Sign coroots and faithful simple parameters in the native adjoint group

The square of the literal rank-one Tits word is the minus-one coroot diagonal.
The proof evaluates the integral word on Cartan and root vectors, then descends
its signs to the coefficient field. Its conjugation action follows the actual
root pairing. Positive and negative simple parameters are recovered from a
single matrix entry. These facts supply the native coordinate detectors used
by the exceptional rank-four centralizer construction.

Sources: Geck's integral adjoint construction; GLS3 §§1.12, 2.4 and 2.6;
Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.OddRankFour
open Matrix
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
attribute [local instance] Classical.decEq
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F]
set_option linter.unusedSimpArgs false

private lemma tits_square_cartan (i j : b.support) :
    (titsLift i * titsLift i) *ᵥ u j = u j := by
  rw [← Matrix.mulVec_mulVec, titsLift_mulVec_u, Matrix.mulVec_sub,
    Matrix.mulVec_smul, titsLift_mulVec_u, titsLift_mulVec_u]
  have hii : |b.cartanMatrix i i| = 2 := by simp
  rw [hii]
  module

private lemma tits_square_root (i : b.support) (j : ι) :
    (titsLift i * titsLift i) *ᵥ v (b := b) j =
      (-1 : ℤ) ^ (P.chainBotCoeff i j +
        P.chainBotCoeff i (P.reflectionPerm i j)) •
      v (b := b) j := by
  rw [← Matrix.mulVec_mulVec, titsLift_mulVec_v, Matrix.mulVec_smul,
    titsLift_mulVec_v, P.reflectionPerm_self, smul_smul, ← pow_add]

private lemma chain_sign (i : b.support) (j : ι) :
    (-1 : F) ^ (P.chainBotCoeff i j +
      P.chainBotCoeff i (P.reflectionPerm i j)) =
      (((-1 : Fˣ) ^ (-P.pairingIn ℤ j i) : Fˣ) : F) := by
  let := P.indexNeg
  have hdep : ¬ LinearIndependent R ![P.root i, P.root i] := by
    rw [LinearIndependent.pair_iff]
    intro h
    exact one_ne_zero (h 1 (-1) (by simp)).1
  have htop : P.chainTopCoeff i i = 0 :=
    P.chainTopCoeff_of_not_linearIndependent hdep
  have hbot : P.chainBotCoeff i i = 0 :=
    P.chainBotCoeff_of_not_linearIndependent hdep
  by_cases hsame : j = i.val
  · subst j
    simp [htop, hbot]
  by_cases hneg : j = (-i : ι)
  · subst j
    simp [htop, hbot, RootPairing.indexNeg_neg]
  have hlin : LinearIndependent R ![P.root i, P.root j] := by
    apply RootPairing.IsReduced.linearIndependent P (Ne.symm hsame)
    intro h
    apply hneg
    apply P.root.injective
    simpa only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self] using (neg_eq_iff_eq_neg.mpr h).symm
  have hlinNeg : LinearIndependent R
      ![P.root (-i : ι), P.root j] := by
    rw [LinearIndependent.pair_iff] at hlin ⊢
    intro a b hab
    have hab' : (-a) • P.root i + b • P.root j = 0 := by
      simpa only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self, smul_neg, neg_smul] using hab
    obtain ⟨ha, hb⟩ := hlin (-a) b hab'
    exact ⟨neg_eq_zero.mp ha, hb⟩
  have hc : P.chainBotCoeff i (P.reflectionPerm i j) =
      P.chainTopCoeff i j := by
    have h := chainBotCoeff_reflectionWord (P := P)
      (b := b) [i] (-i : ι) j hlinNeg
    simpa only [reflectionWord, RootPairing.indexNeg_neg,
      P.reflectionPerm_self,
      P.chainBotCoeff_reflectionPerm_left] using h
  rw [hc]
  have hchain := P.chainTopCoeff_sub_chainBotCoeff hlin
  have hp : (-1 : Fˣ) ^ ((P.chainBotCoeff i j +
      P.chainTopCoeff i j : ℕ) : ℤ) =
      (-1 : Fˣ) ^ (-P.pairingIn ℤ j i) := by
    calc
      _ = (-1 : Fˣ) ^ (2 * (P.chainBotCoeff i j : ℤ) +
          (-P.pairingIn ℤ j i)) := by
            congr 1
            push_cast
            omega
      _ = _ := by rw [_root_.zpow_add, _root_.zpow_mul]; norm_num
  rw [zpow_natCast] at hp
  simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using congrArg Units.val hp

private def signDiagonal (i : b.support) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  Matrix.diagonal fun a => match a with
    | .inl _ => 1
    | .inr j => (-1 : ℤ) ^ (P.chainBotCoeff i j +
        P.chainBotCoeff i (P.reflectionPerm i j))

private lemma tits_square_diagonal (i : b.support) :
    titsLift i * titsLift i = signDiagonal i := by
  apply Matrix.ext_of_mulVec_single
  rintro (j | j)
  · change (titsLift i * titsLift i) *ᵥ u j = _
    rw [tits_square_cartan]
    simp [signDiagonal, u, Matrix.diagonal_mulVec_single]
  · change (titsLift i * titsLift i) *ᵥ v (b := b) j = _
    rw [tits_square_root]
    ext k
    by_cases hk : k = Sum.inr j
    · subst k
      simp [signDiagonal, v, Matrix.diagonal_mulVec_single]
    · simp [signDiagonal, v, Matrix.diagonal_mulVec_single, Pi.single_apply, hk, Ne.symm hk]

/-- The square of the actual simple Tits word is its minus-one coroot diagonal. -/
theorem tits_square_eq_coroot (i : b.support) :
    rootCurveTitsWord (P := P) (S := F) [i,i] =
      integralChevalleyTorusElement (P := P)
        (integralChevalleySimpleCorootParameter i (-1 : Fˣ)) := by
  apply Units.ext
  change specializeMatrix (titsWord [i,i]) = Matrix.diagonal _
  simp only [titsWord, mul_one, tits_square_diagonal]
  ext row col
  by_cases h : row = col
  · subst col
    cases row with
    | inl j =>
        simp [specializeMatrix, signDiagonal, integralChevalleyTorusElement,
          chevalleyBasisTorusUnit, chevalleyBasisWeight]
    | inr j =>
        simp only [specializeMatrix, signDiagonal, Matrix.map_apply, Matrix.diagonal_apply,
          if_true, Int.coe_castRingHom, Int.cast_pow, Int.cast_neg, Int.cast_one]
        rw [chain_sign]
        simp [chevalleyBasisTorusUnit_root]
  · simp [specializeMatrix, signDiagonal, Matrix.diagonal_apply, h]


open TwistedE6.FoldedSubsystem.HigherRealizations

/-- The minus-one simple coroot as a literal six-factor root word. -/
def elementaryCoroot (i : b.support) : rootGenerated P b F :=
  (signedSimple F true i 1 * signedSimple F false i (-1) * signedSimple F true i 1) ^ 2

theorem elementaryCoroot_val (i : b.support) :
    (elementaryCoroot (F := F) i).val = integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter i (-1 : Fˣ)) := by
  have hw := tits_square_eq_coroot (F := F) i
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_cons, rootCurveTitsWord_nil] at hw
  simp only [elementaryCoroot, Subgroup.coe_pow, Subgroup.coe_mul, signedSimple_val]
  simpa only [positiveUnit, negativeUnit, pow_two, mul_one, mul_assoc] using hw

theorem elementaryCoroot_square (i : b.support) : elementaryCoroot (F := F) i ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, elementaryCoroot_val, pow_two,
    ← integralChevalleyTorusElement_mul]
  have hparam :
      integralChevalleySimpleCorootParameter i (-1 : Fˣ) *
        integralChevalleySimpleCorootParameter i (-1 : Fˣ) = 1 := by
    ext j
    by_cases hj : j = i <;> simp [integralChevalleySimpleCorootParameter, hj]
  rw [hparam, integralChevalleyTorusElement_one]
  rfl

theorem elementaryCoroot_commute (i j : b.support) :
    Commute (elementaryCoroot (F := F) i) (elementaryCoroot j) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, elementaryCoroot_val]
  rw [← integralChevalleyTorusElement_mul, ← integralChevalleyTorusElement_mul, mul_comm]

theorem elementaryCoroot_conjugate_root (i : b.support) (r : ι) (t : F) :
    elementaryCoroot i * elementaryRoot P b F r t * (elementaryCoroot i)⁻¹ =
      elementaryRoot P b F r ((((-1 : Fˣ) ^ P.pairingIn ℤ r i : Fˣ) : F) * t) := by
  have he : (elementaryCoroot (F := F) i)⁻¹ * elementaryRoot P b F r t *
      elementaryCoroot i =
      elementaryRoot P b F r ((((-1 : Fˣ) ^ P.pairingIn ℤ r i : Fˣ) : F) * t) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, elementaryCoroot_val]
    exact integralChevalleyRootCurve_simpleCoroot_conjugation i (-1 : Fˣ) r t
  have hci : (elementaryCoroot (F := F) i)⁻¹ = elementaryCoroot i :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using elementaryCoroot_square (F := F) i)
  rwa [hci] at he ⊢

theorem elementaryCoroot_conjugate_signed (i j : b.support) (s : Bool) (t : F) :
    elementaryCoroot i * signedSimple F s j t * (elementaryCoroot i)⁻¹ =
      signedSimple F s j ((((-1 : Fˣ) ^ b.cartanMatrix j i : Fˣ) : F) * t) := by
  let := P.indexNeg
  cases s
  · change elementaryCoroot i * elementaryRoot P b F (-j : ι) t *
      (elementaryCoroot i)⁻¹ = elementaryRoot P b F (-j : ι) _
    rw [elementaryCoroot_conjugate_root]
    congr 1
    simp only [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left,
      RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def, _root_.zpow_neg]
    have hneg : (-1 : Fˣ)⁻¹ = -1 := by simp
    rw [← _root_.inv_zpow, hneg]
  · exact elementaryCoroot_conjugate_root i j t


theorem signedSimple_injective (s : Bool) (i : b.support) :
    Function.Injective (signedSimple (P := P) F s i) := by
  cases s
  · let := P.indexNeg
    have entry (t : F) : negativeMatrix i t (Sum.inl i) (Sum.inr i.val) = t := by
      simp [negativeMatrix_formula, fDividedPower, Matrix.mul_apply, omegaMatrix,
        eDividedPower, eMatrix, Matrix.one_apply, -RootPairing.indexNeg_neg]
    intro t u h
    have he := congrArg (fun x : rootGenerated P b F =>
      x.val.val (Sum.inl i) (Sum.inr i.val)) h
    simp only [signedSimple_val] at he
    change negativeMatrix i t _ _ = negativeMatrix i u _ _ at he
    simpa only [entry] using he
  · exact TheoremDRootNormalizer.elementaryRoot_simple_injective i

end ExceptionalSplit.OddRankFour
