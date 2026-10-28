module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence.ParameterOneFaithfulness.CoxeterReduction
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence.ParameterOneFaithfulness.SignTorus.CorootBridge
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# The parameter-one sign torus in the F4 pair completion

The square of the literal lift `x_i(1) x_{-i}(-1) x_i(1)` is the
simple-coroot diagonal at -1. The Tits grading gives its conjugation formula
with Cartan exponent `-pairingIn ℤ i j`, where i is the conjugating root.
The actual two-node relations lift this matrix identity to `PairCompletion`.
Consequently the four square corrections form a subgroup normal relative to
the generated Tits normalizer.

The commuting squares give a homomorphism from four integral exponents onto
this subgroup. Evaluation is the faithful F4 diagonal parameter map applied
to the four signs. In odd characteristic its kernel forces every exponent
to be even; the fourth-power relation then kills the original element.
This uses no finite-field hypothesis and includes characteristic three.
The final theorem supplies both exact inputs of the Coxeter reduction.

Source: GLS3 Theorem 2.9.3, normalizer argument in
`refs/KGroup/GLS3/chapter2.tex`, lines 1429–1441. The actual matrix identities
are reused through `SignTorus.CorootBridge`; no global presentation or
faithfulness of the separate root-plane completion is assumed.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ExceptionalSplit.TheoremDRootNormalizer
attribute [local instance] Classical.decEq
local instance signTorusRootsFintype : Fintype typeF4Roots := Fintype.ofFinite _
private abbrev P := typeF4RootPairing
private abbrev b := typeF4RootPairing_base
private abbrev Idx := b.support ⊕ typeF4Roots
variable (F : Type*) [Field F]

private def signCoroot (r : typeF4Roots) : (Matrix Idx Idx F)ˣ where
  val := Matrix.diagonal fun a => ((-1 : Fˣ) ^ chevalleyBasisWeight (P := P) a r : Fˣ)
  inv := Matrix.diagonal fun a => (((-1 : Fˣ) ^ chevalleyBasisWeight (P := P) a r)⁻¹ : Fˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    trans Matrix.diagonal (fun _ : Idx => (1 : F))
    · apply congrArg Matrix.diagonal
      funext a
      exact ((-1 : Fˣ) ^ chevalleyBasisWeight (P := P) a r).val_inv
    · exact Matrix.diagonal_one
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    trans Matrix.diagonal (fun _ : Idx => (1 : F))
    · apply congrArg Matrix.diagonal
      funext a
      exact ((-1 : Fˣ) ^ chevalleyBasisWeight (P := P) a r).inv_val
    · exact Matrix.diagonal_one

private theorem signCoroot_inv (r : typeF4Roots) : (signCoroot F r)⁻¹ = signCoroot F r := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext a
  simp only [← inv_zpow, inv_neg, inv_one]

private theorem signCoroot_simple (i : b.support) :
    signCoroot F i = integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter i (-1 : Fˣ)) := by
  apply Units.ext
  apply congrArg Matrix.diagonal
  funext a
  simp [chevalleyBasisTorusUnit, integralChevalleySimpleCorootParameter, ← inv_zpow]

private theorem tits_square (i : b.support) :
    rootCurveTitsWord (P := P) (S := F) [i] ^ 2 = signCoroot F i := by
  have h := SignTorusMatrices.coroot F i (-1 : Fˣ)
  simp only [Units.val_neg, Units.val_one, inv_neg, inv_one,
    matrixH, matrixN_neg_one, matrixN_one, ← signCoroot_simple] at h
  have hi := congrArg Inv.inv h
  simpa only [mul_inv_rev, inv_inv, signCoroot_inv, pow_two] using hi

private theorem weight_reflect (a : Idx) (r s : typeF4Roots) :
    chevalleyBasisWeight (P := P) a (P.reflectionPerm s r) =
      chevalleyBasisWeight (P := P) a r -
        P.pairingIn ℤ s r * chevalleyBasisWeight (P := P) a s := by
  cases a with
  | inl i => simp [chevalleyBasisWeight]
  | inr k =>
    change P.pairingIn ℤ k (P.reflectionPerm s r) = _
    apply FaithfulSMul.algebraMap_injective ℤ ℝ
    simp only [map_sub, map_mul, RootPairing.algebraMap_pairingIn, chevalleyBasisWeight]
    simp only [← P.root_coroot_eq_pairing, P.coroot_reflectionPerm,
      P.coreflection_apply_coroot, map_sub, map_smul, smul_eq_mul]

private def diagonalUnitHom : (Idx → Fˣ) →* (Matrix Idx Idx F)ˣ where
  toFun t :=
    { val := Matrix.diagonal fun a => (t a : F)
      inv := Matrix.diagonal fun a => ((t a)⁻¹ : Fˣ)
      val_inv := by ext a c; by_cases h : a = c <;> simp [Matrix.one_apply, h]
      inv_val := by ext a c; by_cases h : a = c <;> simp [Matrix.one_apply, h] }
  map_one' := by ext a c; simp [Matrix.diagonal_apply, Matrix.one_apply]
  map_mul' t u := by ext a c; by_cases h : a = c <;> simp [h]

private theorem signCoroot_reflect (r s : typeF4Roots) :
    signCoroot F (P.reflectionPerm s r) =
      signCoroot F r * signCoroot F s ^ (-P.pairingIn ℤ s r) := by
  change diagonalUnitHom F _ = diagonalUnitHom F _ * (diagonalUnitHom F _) ^ _
  rw [← map_zpow, ← map_mul]
  congr 1
  funext a
  change (-1 : Fˣ) ^ chevalleyBasisWeight (P := P) a (P.reflectionPerm s r) =
    (-1 : Fˣ) ^ chevalleyBasisWeight (P := P) a r *
      ((-1 : Fˣ) ^ chevalleyBasisWeight (P := P) a s) ^ (-P.pairingIn ℤ s r)
  rw [weight_reflect, zpow_sub, zpow_neg, ← zpow_mul, mul_comm (P.pairingIn ℤ s r)]

private theorem tits_sign_conj (i j : b.support) :
    rootCurveTitsWord (P := P) (S := F) [i] * signCoroot F j *
      (rootCurveTitsWord (P := P) (S := F) [i])⁻¹ =
      signCoroot F j * signCoroot F i ^ (-P.pairingIn ℤ i j) := by
  rw [← signCoroot_reflect]
  apply (mul_right_cancel_iff (a := rootCurveTitsWord (P := P) (S := F) [i])).mp
  rw [inv_mul_cancel_right]
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    Matrix.diagonal _ * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading (P := P) i row col hz
      (P.reflectionPerm i j)
    rw [P.reflectionPerm_self] at hw
    rw [hw]
    exact mul_comm _ _

/-- The literal matrix of a square is its simple-coroot sign diagonal. -/
theorem transportGenerator_sq_matrix (i : typeF4RootPairing_base.support) :
    (completionEvaluation F (transportGenerator F i ^ 2)).val =
      SignTorusMatrices.parameterMatrixHom F (Pi.mulSingle (typeF4RootPairing_baseEquiv.symm i) (-1 : Fˣ)) := by
  rw [map_pow, Subgroup.coe_pow]
  change (coverEvaluation F (transportTitsWord F [i])).val ^ 2 = _
  rw [coverEvaluation_transportTitsWord, tits_square, signCoroot_simple]
  change integralChevalleyTorusElement (P := P) _ = integralChevalleyTorusElement (P := P) _
  congr 1
  funext j
  have he : typeF4RootPairing_baseEquiv.symm j = typeF4RootPairing_baseEquiv.symm i ↔ j = i :=
    typeF4RootPairing_baseEquiv.symm.injective.eq_iff
  by_cases hji : j = i <;> simp [integralChevalleySimpleCorootParameter, he, hji]

/-- The Cartan exponent has first index the conjugating simple root. -/
theorem transportGenerator_conj_sq (i j : typeF4RootPairing_base.support) :
    transportGenerator F i * transportGenerator F j ^ 2 * (transportGenerator F i)⁻¹ =
      transportGenerator F j ^ 2 *
        (transportGenerator F i ^ 2) ^ (-typeF4RootPairing.pairingIn ℤ i j) := by
  let a := typeF4RootPairing_baseEquiv.symm i
  let c := typeF4RootPairing_baseEquiv.symm j
  let x := pairTransportTitsWord F [true]
  let y := pairTransportTitsWord F [false]
  have hx : pairInclusion F a c x = transportTitsWord F [i] := by
    rw [pairInclusion_pairTransportTitsWord]
    simp [pairTransportNodes, pairNode, sourceIndex, a]
  have hy : pairInclusion F a c y = transportTitsWord F [j] := by
    rw [pairInclusion_pairTransportTitsWord]
    simp [pairTransportNodes, pairNode, sourceIndex, c]
  have he : pairEvaluation F a c (x * y ^ 2 * x⁻¹) =
      pairEvaluation F a c (y ^ 2 * (x ^ 2) ^ (-P.pairingIn ℤ i j)) := by
    change coverEvaluation F (pairInclusion F a c (x * y ^ 2 * x⁻¹)) =
      coverEvaluation F (pairInclusion F a c (y ^ 2 * (x ^ 2) ^ (-P.pairingIn ℤ i j)))
    simp only [map_mul, map_pow, map_inv, map_zpow, hx, hy]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_zpow,
      coverEvaluation_transportTitsWord, tits_square]
    exact tits_sign_conj F i j
  have h := pairQuotient_eq_of_pairEvaluation_eq F a c _ _ he
  simpa only [map_mul, map_pow, map_inv, map_zpow, hx, hy, transportGenerator] using h

private def signExponentHom : (Fin 4 → Multiplicative ℤ) →* PairCompletion F :=
  MonoidHom.noncommPiCoprod
    (fun i => zpowersHom _ (transportGenerator F (sourceIndex i) ^ 2))
    (by
      intro i j _ m n
      change Commute ((transportGenerator F (sourceIndex i) ^ 2) ^ Multiplicative.toAdd m)
        ((transportGenerator F (sourceIndex j) ^ 2) ^ Multiplicative.toAdd n)
      exact (transportGenerator_sq_commute F _ _).zpow_zpow _ _)

private theorem signExponentHom_single (i : Fin 4) (n : Multiplicative ℤ) :
    signExponentHom F (Pi.mulSingle i n) =
      (transportGenerator F (sourceIndex i) ^ 2) ^ Multiplicative.toAdd n :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem signExponentHom_range : (signExponentHom F).range = transportSignTorus F := by
  rw [signExponentHom, MonoidHom.noncommPiCoprod_range]
  apply le_antisymm
  · apply iSup_le
    intro i
    rintro _ ⟨n, rfl⟩
    exact (transportSignTorus F).zpow_mem (transportGenerator_sq_mem F _) _
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    apply (le_iSup (fun j => (zpowersHom (PairCompletion F)
      (transportGenerator F (sourceIndex j) ^ 2)).range) (typeF4RootPairing_baseEquiv.symm i))
    refine ⟨Multiplicative.ofAdd 1, ?_⟩
    simp [sourceIndex]

private def signParameterHom : (Fin 4 → Multiplicative ℤ) →* (Fin 4 → Fˣ) where
  toFun n i := (-1 : Fˣ) ^ Multiplicative.toAdd (n i)
  map_one' := by funext i; simp
  map_mul' m n := by funext i; simp [zpow_add]

private theorem signParameterHom_single (i : Fin 4) (n : Multiplicative ℤ) :
    signParameterHom F (Pi.mulSingle i n) =
      Pi.mulSingle i ((-1 : Fˣ) ^ Multiplicative.toAdd n) := by
  ext j
  by_cases h : j = i <;> simp [signParameterHom, h]

private def signCompletionMatrix : PairCompletion F →* (Matrix Idx Idx F)ˣ :=
  (Cover F).subtype.comp (completionEvaluation F)

private theorem signExponentHom_matrix (n : Fin 4 → Multiplicative ℤ) :
    signCompletionMatrix F (signExponentHom F n) =
      SignTorusMatrices.parameterMatrixHom F (signParameterHom F n) := by
  have h : (signCompletionMatrix F).comp (signExponentHom F) =
      (SignTorusMatrices.parameterMatrixHom F).comp (signParameterHom F) := by
    apply MonoidHom.pi_ext
    intro i m
    simp only [MonoidHom.comp_apply, signExponentHom_single, signParameterHom_single,
      map_zpow, Pi.mulSingle_zpow]
    have hs : signCompletionMatrix F (transportGenerator F (sourceIndex i) ^ 2) =
        SignTorusMatrices.parameterMatrixHom F (Pi.mulSingle i (-1 : Fˣ)) := by
      simpa only [signCompletionMatrix, MonoidHom.comp_apply, Subgroup.subtype_apply,
        sourceIndex, Equiv.symm_apply_apply] using transportGenerator_sq_matrix F (sourceIndex i)
    simpa only [map_pow, ← map_zpow] using congrArg (fun g => g ^ Multiplicative.toAdd m) hs
  exact DFunLike.congr_fun h n

set_option backward.isDefEq.respectTransparency false in
private theorem signExponentHom_eq_one (h2 : (2 : F) ≠ 0)
    (n : Fin 4 → Multiplicative ℤ) (hn : signParameterHom F n = 1) :
    signExponentHom F n = 1 := by
  -- Faithfulness of the diagonal recovers each sign; odd characteristic
  -- makes a trivial sign equivalent to an even exponent.
  have hm (i : Fin 4) : (transportGenerator F (sourceIndex i) ^ 2) ^
      Multiplicative.toAdd (n i) = 1 := by
    have hi := congrArg (fun t : Fin 4 → Fˣ => (t i : F)) hn
    change ((-1 : Fˣ) ^ Multiplicative.toAdd (n i) : Fˣ).val = 1 at hi
    rw [Units.val_zpow_eq_zpow_val] at hi
    have hneg : (-1 : F) ≠ 1 := by
      intro h
      apply h2
      calc (2 : F) = 1 + 1 := by norm_num
           _ = 0 := by calc
             1 + 1 = -1 + 1 := congrArg (· + 1) h.symm
             _ = 0 := neg_add_cancel 1
    have he : Even (Multiplicative.toAdd (n i)) := by
      by_contra h
      exact hneg (by simpa [neg_one_zpow_eq_ite, h] using hi)
    obtain ⟨k, hk⟩ := he
    rw [hk, ← two_mul, zpow_mul, zpow_ofNat, ← pow_mul]
    norm_num only [Nat.reduceMul]
    rw [transportGenerator_pow_four, one_zpow]
  rw [signExponentHom, MonoidHom.noncommPiCoprod_apply]
  apply (Finset.noncommProd_eq_pow_card _ _ _ 1 _).trans (one_pow _)
  intro i _
  exact hm i

/-- Evaluation is faithful on the four square corrections, over any odd field. -/
theorem completionEvaluation_injOn_transportSignTorus (h2 : (2 : F) ≠ 0) :
    Set.InjOn (completionEvaluation F) (transportSignTorus F) := by
  have hker {g : PairCompletion F} (hg : g ∈ transportSignTorus F)
      (he : completionEvaluation F g = 1) : g = 1 := by
    rw [← signExponentHom_range] at hg
    obtain ⟨n, rfl⟩ := hg
    have hm : SignTorusMatrices.parameterMatrixHom F (signParameterHom F n) = 1 := by
      rw [← signExponentHom_matrix]
      exact congrArg Subtype.val he
    have hn := SignTorusMatrices.parameterMatrixHom_injective F (hm.trans (map_one _).symm)
    exact signExponentHom_eq_one F h2 n hn
  intro x hx y hy he
  apply mul_inv_eq_one.mp
  apply hker ((transportSignTorus F).mul_mem hx ((transportSignTorus F).inv_mem hy))
  rw [map_mul, map_inv, he, mul_inv_cancel]

/-- Each simple Tits lift normalizes the subgroup of square corrections. -/
theorem transportGenerator_conj_sq_mem_signTorus (i j : typeF4RootPairing_base.support) :
    transportGenerator F i * transportGenerator F j ^ 2 * (transportGenerator F i)⁻¹ ∈
      transportSignTorus F := by
  rw [transportGenerator_conj_sq]
  exact (transportSignTorus F).mul_mem (transportGenerator_sq_mem F j)
    ((transportSignTorus F).zpow_mem (transportGenerator_sq_mem F i) _)

/-- The sign torus is normalized by the literal transport normalizer. -/
theorem transportSignTorus_normalized :
    transportNormalizer F ≤ Subgroup.normalizer (transportSignTorus F : Set (PairCompletion F)) :=
  transportSignTorus_normalized_of_generators F (transportGenerator_conj_sq_mem_signTorus F)

/-- Normality is relative to the generated Tits subgroup. -/
theorem transportSignTorus_relative_normal :
    ((transportSignTorus F).subgroupOf (transportNormalizer F)).Normal :=
  transportSignTorus_normal_subgroupOf F (transportSignTorus_normalized F)

/-- The exact two sign-torus inputs discharge the Coxeter reduction. -/
theorem transportNormalizerFaithful_signTorus_application (h2 : (2 : F) ≠ 0) :
    TransportNormalizerFaithful F :=
  transportNormalizerFaithful_of_signTorus F (transportSignTorus_normalized F)
    (completionEvaluation_injOn_transportSignTorus F h2)

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
