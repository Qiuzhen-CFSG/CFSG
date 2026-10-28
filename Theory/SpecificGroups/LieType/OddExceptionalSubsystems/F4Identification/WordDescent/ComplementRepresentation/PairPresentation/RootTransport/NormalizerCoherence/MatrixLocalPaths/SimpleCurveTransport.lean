module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence.MatrixLocalPaths
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.PlaneCharts.MatrixTransport

/-!
# Transport and recognition of signed simple F4 curves

Equal Weyl endpoints give an integral sign comparing every divided power of
Geck's signed simple operators. Specializing the existing route-comparison
identity therefore transports the literal curves over every field, including F3.

Conversely, Tits words preserve the Cartan block and permute root basis lines
up to signs. A simple curve sends its own Cartan basis vector to that vector
plus `2t` times its root vector. Comparing this column in `n x = y n` identifies
the exact Weyl endpoint whenever `x` is nonidentity and `2` is nonzero. The
higher divided powers vanish on Cartan columns, so this argument does not
extract polynomial coefficients over the coefficient field.

The final application discharges the operator transport input of the matrix
normalizer-path construction. Source: GLS3, the root-transport argument after
Lemma 2.9.4, `refs/KGroup/GLS3/chapter2.tex`, lines 1439–1454.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open RootPairing.SimpleGeckGroup
open scoped Matrix
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local notation "𝓟" => typeF4RootPairing
local notation "𝓑" => typeF4RootPairing_base.support ⊕ typeF4Roots

variable (F : Type*) [Field F]

/-- The literal signed simple curves follow their Weyl endpoints. -/
theorem simpleTransport_map
    (w : List Node) (s z : Bool) (i j : Fin 4)
    (h : typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd w)
      (signedRoot s i) = signedRoot z j) (t : F) :
    ∃ u : F, titsEvaluation F w * coverSimple F s i t * (titsEvaluation F w)⁻¹ =
      coverSimple F z j u := by
  have hr : reflectionWord (P := 𝓟) w (signedRoot s i) =
      reflectionWord (P := 𝓟) (b := typeF4RootPairing_base) [] (signedRoot z j) := by
    rw [reflectionWord_eq_weylGroupToPerm]
    exact h
  obtain ⟨ε, _, he⟩ := PlaneCharts.route_evaluation_comparison F w [] s z i j hr
  refine ⟨(ε : F) * t, ?_⟩
  simpa only [transportRouteWord, map_mul, map_inv, coverEvaluation_of,
    transportTitsWord_nil, map_one, one_mul, inv_one, mul_one, titsEvaluation] using he t

private theorem simple_mulVec_cartan (s : Bool) (i : Fin 4) (t : F) (k : Node) :
    (coverSimple F s i t).val.val *ᵥ Pi.single (Sum.inl k) 1 =
      Pi.single (Sum.inl k) 1 +
        (t * (|typeF4RootPairing_base.cartanMatrix (sourceIndex i) k| : ℤ)) •
          (Pi.single (Sum.inr (signedRoot s i)) 1 : 𝓑 → F) := by
  have he (n : ℕ) (a : 𝓑) :
      eDividedPower (P := 𝓟) (sourceIndex i) (n + 2) a (Sum.inl k) = 0 := by
    simpa only [u, Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using
      congrFun (eDividedPower_add_two_mulVec_u (P := 𝓟) (sourceIndex i) k n) a
  have hf (n : ℕ) (a : 𝓑) :
      fDividedPower (P := 𝓟) (sourceIndex i) (n + 2) a (Sum.inl k) = 0 := by
    simpa only [u, Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using
      congrFun (fDividedPower_add_two_mulVec_u (P := 𝓟) (sourceIndex i) k n) a
  rw [coverSimple_val]
  cases s
  · change negativeMatrix (sourceIndex i) t *ᵥ _ = _
    ext (a | a) <;>
      simp [negativeMatrix_formula, hf 0, hf 1,
        fDividedPower_one, fMatrix, signedRoot, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  · change positiveMatrix (sourceIndex i) t *ᵥ _ = _
    ext (a | a) <;>
      simp [positiveMatrix_formula, he 0, he 1,
        eDividedPower_one, eMatrix, signedRoot, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all

private theorem integral_titsLift_cartan_zero (i k : Node) (r : typeF4Roots) :
    titsLift (P := 𝓟) i (Sum.inr r) (Sum.inl k) = 0 := by
  simpa [u, Matrix.mulVec_single_one] using
    congrFun (titsLift_mulVec_u (P := 𝓟) i k) (Sum.inr r)

private theorem integral_titsWord_cartan_zero (w : List Node) (r : typeF4Roots) (k : Node) :
    titsWord (P := 𝓟) w (Sum.inr r) (Sum.inl k) = 0 := by
  induction w generalizing r k with
  | nil => simp [titsWord]
  | cons i w ih =>
    simp [titsWord, Matrix.mul_apply, Fintype.sum_sum_type,
      integral_titsLift_cartan_zero, ih]

private theorem titsEvaluation_cartan_zero (w : List Node) (r : typeF4Roots) (k : Node) :
    (titsEvaluation F w).val.val (Sum.inr r) (Sum.inl k) = 0 := by
  simp only [titsEvaluation, coverEvaluation_transportTitsWord, rootCurveTitsWord,
    specializeMatrix, Matrix.map_apply, integral_titsWord_cartan_zero, map_zero]

private theorem titsEvaluation_mulVec_root (w : List Node) (r : typeF4Roots) :
    (titsEvaluation F w).val.val *ᵥ Pi.single (Sum.inr r) 1 =
      (titsWordSign (P := 𝓟) w r : F) •
        (Pi.single (Sum.inr (reflectionWord (P := 𝓟) w r)) 1 : 𝓑 → F) := by
  ext a
  have h := congrFun (titsWord_mulVec_v (P := 𝓟) w r) a
  simp only [v, Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
    smul_eq_mul] at h
  simp only [titsEvaluation, coverEvaluation_transportTitsWord, rootCurveTitsWord,
    specializeMatrix, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply,
    Int.coe_castRingHom, h, Int.cast_mul, Pi.smul_apply, smul_eq_mul]
  simp [Pi.single_apply]

private theorem simple_cartan_root_zero (s : Bool) (i : Fin 4) (t : F)
    (r : typeF4Roots) (hr : r ≠ signedRoot s i) (k : Node) :
    (coverSimple F s i t).val.val (Sum.inr r) (Sum.inl k) = 0 := by
  simpa [Matrix.mulVec_single_one, Pi.single_apply, hr] using
    congrFun (simple_mulVec_cartan F s i t k) (Sum.inr r)

private theorem simple_zero (s : Bool) (i : Fin 4) : coverSimple F s i 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [coverSimple_val]
  cases s
  · exact negativeMatrix_zero _
  · exact positiveMatrix_zero _

/-- A nonidentity transported curve determines the exact Weyl-root index. -/
theorem simpleTransport_recognize (h2 : (2 : F) ≠ 0)
    (w : List Node) (s z : Bool) (i j : Fin 4) (t u : F)
    (ht : coverSimple F s i t ≠ 1)
    (h : titsEvaluation F w * coverSimple F s i t * (titsEvaluation F w)⁻¹ =
      coverSimple F z j u) :
    typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd w)
      (signedRoot s i) = signedRoot z j := by
  rw [← reflectionWord_eq_weylGroupToPerm]
  by_contra hr
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (simple_zero F s i)
  have hn : titsEvaluation F w * coverSimple F s i t =
      coverSimple F z j u * titsEvaluation F w := by
    rw [← h]
    group
  have hc := congrArg (fun g : Cover F =>
    g.val.val *ᵥ (Pi.single (Sum.inl (sourceIndex i)) 1 : 𝓑 → F)) hn
  change ((titsEvaluation F w).val.val * (coverSimple F s i t).val.val) *ᵥ _ =
    ((coverSimple F z j u).val.val * (titsEvaluation F w).val.val) *ᵥ _ at hc
  rw [← Matrix.mulVec_mulVec, simple_mulVec_cartan, Matrix.mulVec_add,
    Matrix.mulVec_smul, titsEvaluation_mulVec_root] at hc
  have he := congrFun hc (Sum.inr (reflectionWord (P := 𝓟) w (signedRoot s i)))
  have hz :
      ((coverSimple F z j u).val.val * (titsEvaluation F w).val.val)
        (Sum.inr (reflectionWord (P := 𝓟) w (signedRoot s i)))
        (Sum.inl (sourceIndex i)) = 0 := by
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, titsEvaluation_cartan_zero,
      simple_cartan_root_zero F z j u _ hr, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one,
    Matrix.col_apply, titsEvaluation_cartan_zero, Pi.single_eq_same,
    mul_one, zero_add, hz] at he
  have heps : (titsWordSign (P := 𝓟) w (signedRoot s i) : F) ≠ 0 := by
    have hs := congrArg (Int.castRingHom F)
      (titsWordSign_mul_self (P := 𝓟) w (signedRoot s i))
    simp only [map_mul, map_one, Int.coe_castRingHom] at hs
    exact left_ne_zero_of_mul_eq_one hs
  have hc2 : (|typeF4RootPairing_base.cartanMatrix (sourceIndex i) (sourceIndex i)| : ℤ) = 2 := by simp
  rw [hc2] at he
  exact (mul_ne_zero (mul_ne_zero ht0 h2) heps) (by simpa only [Int.cast_ofNat] using he)

/-- Tits transport and endpoint recognition over every field with `2 ≠ 0`. -/
theorem simpleTransport (h2 : (2 : F) ≠ 0) : SimpleTransport F where
  map := simpleTransport_map F
  recognize := simpleTransport_recognize F h2

/-- The actual matrix path consumer, with its operator transport premise discharged. -/
theorem hasNormalizerTransportPaths_of_weyl_and_squares [Finite F]
    (h2 : (2 : F) ≠ 0) (hg : HasWeylPairPaths) (ht : HasSquareCorrections F) :
    HasNormalizerTransportPaths F :=
  hasNormalizerTransportPaths_of_inputs F hg (simpleTransport F h2) ht

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
