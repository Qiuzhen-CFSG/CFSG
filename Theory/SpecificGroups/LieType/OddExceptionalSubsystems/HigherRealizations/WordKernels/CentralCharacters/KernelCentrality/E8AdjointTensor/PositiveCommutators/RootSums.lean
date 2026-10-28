module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.PositiveCommutators.CartanColumns
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.RootSpace

/-!
# Exact root-sum commutators of the relative E6 tensor in E8

The fixed tensor is a signed Tits transport in E8 with endpoint the embedded
E6 root. Ambient root-space multiplicity one and primitive integral descent
put each commutator on the actual tensor's sum-root line. Evaluation on the
embedded source Cartan columns then determines the scalar: independence of
the two source roots forces it to be the source `chainBotCoeff + 1`.

The source routes and orientations are retained for both polarities.
Adapted from the checked F4
`CoverCenter.Equivariance.PositiveCommutators.RootSums` proof and its generic
integral root-space API. Source: GLS3 §§1.10–1.12 and 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup ReeF4.WordRelations.Faithfulness
open scoped Classical
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
attribute [local instance] Classical.decEq
local instance : Fintype typeE8Roots := Fintype.ofFinite _
attribute [local instance 100] LieRing.ofAssociativeRing
-- Use the coefficient embedding of the generic integral root-space theorem.
local instance : Algebra ℤ RatAlgClosure := Ring.toIntAlgebra RatAlgClosure

/-- The fixed source-normalized tensor is a unit multiple of a positive-simple
Tits transport in E8, with the actual embedded root as endpoint. -/
lemma rootTensor_eq_signed_transport (r : typeE6Roots) :
    ∃ (w : List typeE8RootPairing_base.support) (j : typeE8RootPairing_base.support)
      (q : ℤ), q * q = 1 ∧
      reflectionWord (P := typeE8RootPairing) w j = AdjointBlocks.rootE8 r ∧
        rootTensor r = q • titsConjugate w (eMatrix j) := by
  let := typeE6RootPairing.indexNeg
  let := typeE8RootPairing.indexNeg
  by_cases hr : typeE6RootPairing_base.IsPos r
  · let z := rootRoute (P := typeE6RootPairing) (b := typeE6RootPairing_base) r
    refine ⟨z.word.map AdjointBlocks.baseE8, AdjointBlocks.baseE8 z.simple,
      simpleRouteOperatorOrientation true z.word z.simple,
      simpleRouteOperatorOrientation_sq _ _ _, ?_, ?_⟩
    · rw [← embedded_base, embedded_word, z.target]
    · simp only [rootTensor, if_pos hr, titsConjugate_apply, transportedMatrix]
      rfl
  · let z := rootRoute (P := typeE6RootPairing) (b := typeE6RootPairing_base) (-r)
    refine ⟨z.word.map AdjointBlocks.baseE8 ++ [AdjointBlocks.baseE8 z.simple],
      AdjointBlocks.baseE8 z.simple, -simpleRouteOperatorOrientation false z.word z.simple,
      ?_, ?_, ?_⟩
    · simpa only [neg_mul_neg] using simpleRouteOperatorOrientation_sq false z.word z.simple
    · rw [ReeF4.WordRelations.RouteComparison.reflectionWord_append_simple_self,
        ← embedded_base, embedded_word, z.target, embedded_neg, neg_neg]
    · rw [titsConjugate_apply]
      change rootTensor r = -simpleRouteOperatorOrientation false z.word z.simple •
        transportedMatrix (z.word.map AdjointBlocks.baseE8 ++ [AdjointBlocks.baseE8 z.simple])
          (eMatrix (AdjointBlocks.baseE8 z.simple))
      rw [ReeF4.WordRelations.RouteComparison.transportedMatrix_append_simple_eMatrix]
      simp only [rootTensor, if_neg hr, smul_neg, neg_smul, neg_neg]
      rfl

private lemma extension_root_add {r t s : typeE8Roots}
    (h : typeE8RootPairing.root s = typeE8RootPairing.root r + typeE8RootPairing.root t) :
    (scalarExtension (P := typeE8RootPairing) (b := typeE8RootPairing_base)).root s =
      (scalarExtension (P := typeE8RootPairing) (b := typeE8RootPairing_base)).root r +
        (scalarExtension (P := typeE8RootPairing) (b := typeE8RootPairing_base)).root t := by
  have hs : typeE8RootPairing.rootSpanMem ℤ s =
      typeE8RootPairing.rootSpanMem ℤ r + typeE8RootPairing.rootSpanMem ℤ t :=
    Subtype.ext h
  change scalarExtensionRoot s = scalarExtensionRoot r + scalarExtensionRoot t
  ext l
  simp only [scalarExtensionRoot, hs, map_add, Finsupp.add_apply, Pi.add_apply]

/-- The integral commutator lies in the literal signed sum-root operator line. -/
lemma positive_root_commutator_mem_line (i : typeE6RootPairing_base.support)
    (r s : typeE6Roots)
    (h : typeE6RootPairing.root s = typeE6RootPairing.root i + typeE6RootPairing.root r) :
    ∃ n : ℤ, eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * rootTensor r -
      rootTensor r * eMatrix (AdjointBlocks.baseE8 i) =
        n • rootTensor s := by
  obtain ⟨w, j, q, _, hw, hr⟩ := rootTensor_eq_signed_transport r
  obtain ⟨z, k, p, hp, hz, hs⟩ := rootTensor_eq_signed_transport s
  have hroot :
      (scalarExtension (P := typeE8RootPairing) (b := typeE8RootPairing_base)).root
          (reflectionWord (P := scalarExtension (P := typeE8RootPairing)
            (b := typeE8RootPairing_base))
            (b := scalarExtensionBase (P := typeE8RootPairing) (b := typeE8RootPairing_base))
            z k) =
        (scalarExtension (P := typeE8RootPairing) (b := typeE8RootPairing_base)).root (AdjointBlocks.baseE8 i) +
          (scalarExtension (P := typeE8RootPairing) (b := typeE8RootPairing_base)).root
            (reflectionWord (P := scalarExtension (P := typeE8RootPairing)
              (b := typeE8RootPairing_base))
              (b := scalarExtensionBase (P := typeE8RootPairing) (b := typeE8RootPairing_base))
              w j) := by
    simpa only [scalarExtension_reflectionWord, hw, hz] using extension_root_add (embedded_root_add i r s h)
  let P := scalarExtension (P := typeE8RootPairing) (b := typeE8RootPairing_base)
  let b := scalarExtensionBase (P := typeE8RootPairing) (b := typeE8RootPairing_base)
  let i₀ : b.support := AdjointBlocks.baseE8 i
  let j₀ : b.support := j
  let k₀ : b.support := k
  let w₀ : List b.support := w
  let z₀ : List b.support := z
  have hroot₀ : P.root (reflectionWord (P := P) (b := b) z₀ k₀) =
      P.root i₀ + P.root (reflectionWord (P := P) (b := b) w₀ j₀) := hroot
  let E := (eMatrix (P := P) (b := b) i₀).map (algebraMap ℤ RatAlgClosure)
  let B := (titsConjugate (P := P) (b := b) w₀
    (eMatrix (P := P) (b := b) j₀)).map (algebraMap ℤ RatAlgClosure)
  let A := eMatrix (P := P) (b := b) i₀ *
      titsConjugate (P := P) (b := b) w₀ (eMatrix (P := P) (b := b) j₀) -
    titsConjugate (P := P) (b := b) w₀ (eMatrix (P := P) (b := b) j₀) *
      eMatrix (P := P) (b := b) i₀
  have hA : A.map (algebraMap ℤ RatAlgClosure) = ⁅E, B⁆ := by
    simp only [A, E, B, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Ring.lie_def]
  have hEmem : E ∈ RootPairing.GeckConstruction.lieAlgebra b := by
    rw [show E = RootPairing.GeckConstruction.e (P := P) (b := b) i₀ from
      map_eMatrix (P := P) (b := b) i₀]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (P := P) (b := b) i₀
  have hBmem : B ∈ RootPairing.GeckConstruction.lieAlgebra b := by
    apply map_titsConjugate_mem_lieAlgebra (P := P) (b := b)
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (P := P) (b := b) j₀
  have hEweight : HasRootWeight (P := P) (b := b) i₀ E := by
    have hE := map_titsConjugate_hasRootWeight (P := P) ([] : List b.support) i₀
    simpa only [E, reflectionWord, titsConjugate_apply, titsWord, titsWordInv_nil,
      one_mul, mul_one] using hE
  have hAweight : HasRootWeight (P := P) (b := b)
      (reflectionWord (P := P) (b := b) z₀ k₀)
      (A.map (algebraMap ℤ RatAlgClosure)) := by
    rw [hA]
    intro l
    rw [leibniz_lie, hEweight l, map_titsConjugate_hasRootWeight (P := P) (b := b) w₀ j₀ l,
      smul_lie, lie_smul, ← add_smul, RootPairing.pairing_eq_add_of_root_eq_add hroot₀]
  obtain ⟨n, hn⟩ :=
    Adjoint.PositiveSimple.RootSumSpace.integral_matrix_eq_smul_titsConjugate_of_weight
      (P := P) (b := b) A z₀ k₀ (by rw [hA]; exact (RootPairing.GeckConstruction.lieAlgebra b).lie_mem hEmem hBmem)
      hAweight
  dsimp only [A, P, b, i₀, j₀, k₀, w₀, z₀] at hn
  simp only [scalarExtension_eMatrix, scalarExtension_titsConjugate] at hn
  change eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * titsConjugate w (eMatrix j) -
    titsConjugate w (eMatrix j) * eMatrix (AdjointBlocks.baseE8 i) = n • titsConjugate z (eMatrix k) at hn
  refine ⟨q * n * p, ?_⟩
  rw [hr, hs, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hn, smul_smul, smul_smul]
  congr 1
  calc
    q * n = (q * n) * (p * p) := by rw [hp, mul_one]
    _ = _ := by ring


private lemma coefficients_zero_of_pairing_relation (i : typeE6RootPairing_base.support)
    (r s : typeE6Roots)
    (hroot : typeE6RootPairing.root s = typeE6RootPairing.root i + typeE6RootPairing.root r)
    (a b : ℤ)
    (h : ∀ j : typeE6RootPairing_base.support,
      a * typeE6RootPairing.pairingIn ℤ i j + b * typeE6RootPairing.pairingIn ℤ r j = 0) :
    a = 0 ∧ b = 0 := by
  have hlin := typeE6RootPairing.linearIndependent_of_add_mem_range_root' ⟨s, hroot⟩
  have hv : (a : ℝ) • typeE6RootPairing.root i + (b : ℝ) • typeE6RootPairing.root r = 0 := by
    apply typeE6RootPairing.toPerfPair.injective
    apply typeE6RootPairing_base.flip.toWeightBasis.ext
    intro j
    simp only [RootPairing.Base.toWeightBasis_apply, map_zero, LinearMap.zero_apply]
    change typeE6RootPairing.toLinearMap
      ((a : ℝ) • typeE6RootPairing.root i + (b : ℝ) • typeE6RootPairing.root r)
        (typeE6RootPairing.coroot j) = 0
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      typeE6RootPairing.root_coroot_eq_pairing]
    have hj := congrArg (algebraMap ℤ ℝ) (h j)
    simp only [map_add, map_mul, RootPairing.algebraMap_pairingIn, map_zero] at hj
    simpa only [smul_eq_mul, algebraMap_int_eq, Int.coe_castRingHom] using hj
  have hab := (LinearIndependent.pair_iff.mp hlin) (a : ℝ) (b : ℝ) hv
  exact ⟨Int.cast_eq_zero.mp hab.1, Int.cast_eq_zero.mp hab.2⟩

/-- The exact signed root-sum commutator, with coefficient `p + 1`. -/
lemma positive_root_commutator_add (i : typeE6RootPairing_base.support)
    (r s : typeE6Roots)
    (hroot : typeE6RootPairing.root s = typeE6RootPairing.root i + typeE6RootPairing.root r) :
    eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * rootTensor r -
      rootTensor r * eMatrix (AdjointBlocks.baseE8 i) =
        (typeE6RootPairing.chainBotCoeff i r + 1 : ℤ) •
          rootTensor s := by
  obtain ⟨n, hn⟩ := positive_root_commutator_mem_line i r s hroot
  let c : ℤ := typeE6RootPairing.chainBotCoeff i r + 1
  let y : ℤ := (rootTensor r *ᵥ
    v (b := typeE8RootPairing_base) (AdjointBlocks.rootE8 i)) (Sum.inr (AdjointBlocks.rootE8 s))
  have he (j : typeE6RootPairing_base.support) :
      n * (simpleOperatorOrientation (b := typeE6RootPairing_base) j *
        typeE6RootPairing.pairingIn ℤ s j) =
      (simpleOperatorOrientation (b := typeE6RootPairing_base) j *
        typeE6RootPairing.pairingIn ℤ r j) * c -
      |typeE6RootPairing_base.cartanMatrix i j| * y := by
    have hv := congrArg (fun X : Matrix TargetIndex TargetIndex ℤ =>
      (X *ᵥ u (AdjointBlocks.baseE8 j)) (Sum.inr (AdjointBlocks.rootE8 s))) hn
    simpa only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      rootTensor_cartan_column, Matrix.mulVec_smul,
      embedded_eMatrix_v_add i r s hroot, eMatrix_mulVec_u, embedded_cartan,
      ← embedded_base, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, v, Pi.single_eq_same, mul_one, c, y] using hv.symm
  have hpair (j : typeE6RootPairing_base.support) :
      (n + simpleOperatorOrientation (b := typeE6RootPairing_base) i * y) *
          typeE6RootPairing.pairingIn ℤ i j +
        (n - c) * typeE6RootPairing.pairingIn ℤ r j = 0 := by
    have hj0 : simpleOperatorOrientation (b := typeE6RootPairing_base) j ≠ 0 := by
      intro hj
      have hs := simpleOperatorOrientation_sq (b := typeE6RootPairing_base) j
      rw [hj, zero_mul] at hs
      exact zero_ne_one hs
    have habs : |typeE6RootPairing_base.cartanMatrix i j| =
        simpleOperatorOrientation (b := typeE6RootPairing_base) j *
          simpleOperatorOrientation (b := typeE6RootPairing_base) i *
            typeE6RootPairing_base.cartanMatrix i j := by
      calc
        _ = (|typeE6RootPairing_base.cartanMatrix i j| *
            simpleOperatorOrientation (b := typeE6RootPairing_base) i) *
              simpleOperatorOrientation (b := typeE6RootPairing_base) i := by
          rw [mul_assoc, simpleOperatorOrientation_sq, mul_one]
        _ = _ := by rw [simple_orientation_abs_cartan]; ring
    have hp : typeE6RootPairing.pairingIn ℤ s j =
        typeE6RootPairing_base.cartanMatrix i j + typeE6RootPairing.pairingIn ℤ r j :=
      RootPairing.pairingIn_eq_add_of_root_eq_add hroot
    have he' : n * (typeE6RootPairing_base.cartanMatrix i j +
          typeE6RootPairing.pairingIn ℤ r j) =
        typeE6RootPairing.pairingIn ℤ r j * c -
          simpleOperatorOrientation (b := typeE6RootPairing_base) i *
            typeE6RootPairing_base.cartanMatrix i j * y := by
      apply mul_left_cancel₀ hj0
      calc
        _ = n * (simpleOperatorOrientation (b := typeE6RootPairing_base) j *
            typeE6RootPairing.pairingIn ℤ s j) := by rw [hp]; ring
        _ = _ := he j
        _ = _ := by rw [habs]; ring
    change (n + simpleOperatorOrientation (b := typeE6RootPairing_base) i * y) *
      typeE6RootPairing_base.cartanMatrix i j +
        (n - c) * typeE6RootPairing.pairingIn ℤ r j = 0
    linear_combination he'
  have hc := (coefficients_zero_of_pairing_relation i r s hroot
    (n + simpleOperatorOrientation (b := typeE6RootPairing_base) i * y) (n - c) hpair).2
  rw [sub_eq_zero.mp hc] at hn
  exact hn


end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
