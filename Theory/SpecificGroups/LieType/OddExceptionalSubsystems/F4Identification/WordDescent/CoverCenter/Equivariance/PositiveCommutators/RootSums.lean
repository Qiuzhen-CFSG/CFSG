module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.PositiveCommutators.CartanColumns
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.RootSpace

/-!
# Exact signed root-sum commutators over the integers

Root-space multiplicity one first puts the matrix commutator on the sum-root
line. Primitivity after undoing the Tits route gives an integer coefficient.
Every canonical operator, including a negative one, is a signed transport of
a positive-simple operator, so this step retains the literal integral model.

To determine the coefficient, evaluate on each Cartan column using
`integralCoordinateOperator_cartan_column`. The resulting equations express
a linear relation between the two root-coroot functionals. The two roots
are independent because their sum is a root, so the relation forces the
coefficient to be exactly the positive integer `chainBotCoeff + 1`.

Sources: the Geck root-space argument and primitive-column descent in
`PositiveSimple.RootLinear.RootSums.RootSpace` (whose integral argument is
reused here), the integral root-string formulas, and GLS3 §§2.2–2.6.
-/

public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter

attribute [local instance 100] LieRing.ofAssociativeRing

-- Match the coefficient embedding used by the generic integral Geck interfaces.
local instance : Algebra ℤ RatAlgClosure := Ring.toIntAlgebra RatAlgClosure

private lemma integralCoordinateOperator_eq_signed_transport (r : typeF4Roots) :
    ∃ (w : List typeF4RootPairing_base.support) (j : typeF4RootPairing_base.support)
      (q : ℤ), q * q = 1 ∧ reflectionWord (P := typeF4RootPairing) w j = r ∧
        integralCoordinateOperator (Sum.inr r) = q • titsConjugate w (eMatrix j) := by
  let := typeF4RootPairing.indexNeg
  by_cases hr : typeF4RootPairing_base.IsPos r
  · let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    refine ⟨z.word, z.simple, rootOperatorOrientation r,
      rootOperatorOrientation_sq r, z.target, ?_⟩
    simp only [integralCoordinateOperator, rootOperator_of_pos r hr,
      titsConjugate_apply, transportedMatrix]
    rfl
  · have hn : typeF4RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)
    refine ⟨z.word ++ [z.simple], z.simple, -rootOperatorOrientation r, ?_, ?_, ?_⟩
    · simpa only [neg_mul_neg] using rootOperatorOrientation_sq r
    · rw [ReeF4.WordRelations.RouteComparison.reflectionWord_append_simple_self,
        z.target, neg_neg]
    · have he := rootOperator_neg_of_pos (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) (-r) hn
      simp only [neg_neg] at he
      change rootOperatorOrientation r • rootOperator r =
        -rootOperatorOrientation r • transportedMatrix (z.word ++ [z.simple]) (eMatrix z.simple)
      rw [ReeF4.WordRelations.RouteComparison.transportedMatrix_append_simple_eMatrix]
      simp only [he, smul_neg, neg_smul, neg_neg]
      rfl

private lemma extension_root_add {r t s : typeF4Roots}
    (h : typeF4RootPairing.root s = typeF4RootPairing.root r + typeF4RootPairing.root t) :
    (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root s =
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root r +
        (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root t := by
  have hs : typeF4RootPairing.rootSpanMem ℤ s =
      typeF4RootPairing.rootSpanMem ℤ r + typeF4RootPairing.rootSpanMem ℤ t :=
    Subtype.ext h
  change scalarExtensionRoot s = scalarExtensionRoot r + scalarExtensionRoot t
  ext l
  simp only [scalarExtensionRoot, hs, map_add, Finsupp.add_apply, Pi.add_apply]

/-- The integral commutator lies in the literal signed sum-root operator line. -/
lemma integral_positive_root_commutator_mem_line (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r) :
    ∃ n : ℤ, eMatrix (P := typeF4RootPairing) i * integralCoordinateOperator (Sum.inr r) -
      integralCoordinateOperator (Sum.inr r) * eMatrix i =
        n • integralCoordinateOperator (Sum.inr s) := by
  obtain ⟨w, j, q, _, hw, hr⟩ := integralCoordinateOperator_eq_signed_transport r
  obtain ⟨z, k, p, hp, hz, hs⟩ := integralCoordinateOperator_eq_signed_transport s
  have hroot :
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root
          (reflectionWord (P := scalarExtension (P := typeF4RootPairing)
            (b := typeF4RootPairing_base))
            (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
            z k) =
        (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root i +
          (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root
            (reflectionWord (P := scalarExtension (P := typeF4RootPairing)
              (b := typeF4RootPairing_base))
              (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
              w j) := by
    simpa only [scalarExtension_reflectionWord, hw, hz] using extension_root_add h
  let P := scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)
  let b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base)
  let i₀ : b.support := i
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
  change eMatrix (P := typeF4RootPairing) i * titsConjugate w (eMatrix j) -
    titsConjugate w (eMatrix j) * eMatrix i = n • titsConjugate z (eMatrix k) at hn
  refine ⟨q * n * p, ?_⟩
  rw [hr, hs, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hn, smul_smul, smul_smul]
  congr 1
  calc
    q * n = (q * n) * (p * p) := by rw [hp, mul_one]
    _ = _ := by ring


private lemma coefficients_zero_of_pairing_relation (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (hroot : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r)
    (a b : ℤ)
    (h : ∀ j : typeF4RootPairing_base.support,
      a * typeF4RootPairing.pairingIn ℤ i j + b * typeF4RootPairing.pairingIn ℤ r j = 0) :
    a = 0 ∧ b = 0 := by
  have hlin := typeF4RootPairing.linearIndependent_of_add_mem_range_root' ⟨s, hroot⟩
  have hv : (a : ℝ) • typeF4RootPairing.root i + (b : ℝ) • typeF4RootPairing.root r = 0 := by
    apply typeF4RootPairing.toPerfPair.injective
    apply typeF4RootPairing_base.flip.toWeightBasis.ext
    intro j
    simp only [RootPairing.Base.toWeightBasis_apply, map_zero, LinearMap.zero_apply]
    change typeF4RootPairing.toLinearMap
      ((a : ℝ) • typeF4RootPairing.root i + (b : ℝ) • typeF4RootPairing.root r)
        (typeF4RootPairing.coroot j) = 0
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      typeF4RootPairing.root_coroot_eq_pairing]
    have hj := congrArg (algebraMap ℤ ℝ) (h j)
    simp only [map_add, map_mul, RootPairing.algebraMap_pairingIn, map_zero] at hj
    simpa only [smul_eq_mul, algebraMap_int_eq, Int.coe_castRingHom] using hj
  have hab := (LinearIndependent.pair_iff.mp hlin) (a : ℝ) (b : ℝ) hv
  exact ⟨Int.cast_eq_zero.mp hab.1, Int.cast_eq_zero.mp hab.2⟩

/-- The exact signed root-sum commutator, with coefficient `p + 1`. -/
lemma integral_positive_root_commutator_add (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (hroot : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r) :
    eMatrix (P := typeF4RootPairing) i * integralCoordinateOperator (Sum.inr r) -
      integralCoordinateOperator (Sum.inr r) * eMatrix i =
        (typeF4RootPairing.chainBotCoeff i r + 1 : ℤ) •
          integralCoordinateOperator (Sum.inr s) := by
  obtain ⟨n, hn⟩ := integral_positive_root_commutator_mem_line i r s hroot
  let c : ℤ := typeF4RootPairing.chainBotCoeff i r + 1
  let y : ℤ := (integralCoordinateOperator (Sum.inr r) *ᵥ
    v (b := typeF4RootPairing_base) i) (Sum.inr s)
  have he (j : typeF4RootPairing_base.support) :
      n * (simpleOperatorOrientation (b := typeF4RootPairing_base) j *
        typeF4RootPairing.pairingIn ℤ s j) =
      (simpleOperatorOrientation (b := typeF4RootPairing_base) j *
        typeF4RootPairing.pairingIn ℤ r j) * c -
      |typeF4RootPairing_base.cartanMatrix i j| * y := by
    have hv := congrArg (fun X : Matrix Coordinate Coordinate ℤ =>
      (X *ᵥ u j) (Sum.inr s)) hn
    simpa only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      integralCoordinateOperator_cartan_column, Matrix.mulVec_smul,
      eMatrix_mulVec_v_add hroot, eMatrix_mulVec_u, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, v, Pi.single_eq_same, mul_one, c, y] using hv.symm
  have hpair (j : typeF4RootPairing_base.support) :
      (n + simpleOperatorOrientation (b := typeF4RootPairing_base) i * y) *
          typeF4RootPairing.pairingIn ℤ i j +
        (n - c) * typeF4RootPairing.pairingIn ℤ r j = 0 := by
    have hj0 : simpleOperatorOrientation (b := typeF4RootPairing_base) j ≠ 0 := by
      intro hj
      have hs := simpleOperatorOrientation_sq (b := typeF4RootPairing_base) j
      rw [hj, zero_mul] at hs
      exact zero_ne_one hs
    have habs : |typeF4RootPairing_base.cartanMatrix i j| =
        simpleOperatorOrientation (b := typeF4RootPairing_base) j *
          simpleOperatorOrientation (b := typeF4RootPairing_base) i *
            typeF4RootPairing_base.cartanMatrix i j := by
      calc
        _ = (|typeF4RootPairing_base.cartanMatrix i j| *
            simpleOperatorOrientation (b := typeF4RootPairing_base) i) *
              simpleOperatorOrientation (b := typeF4RootPairing_base) i := by
          rw [mul_assoc, simpleOperatorOrientation_sq, mul_one]
        _ = _ := by rw [simple_orientation_abs_cartan]; ring
    have hp : typeF4RootPairing.pairingIn ℤ s j =
        typeF4RootPairing_base.cartanMatrix i j + typeF4RootPairing.pairingIn ℤ r j :=
      RootPairing.pairingIn_eq_add_of_root_eq_add hroot
    have he' : n * (typeF4RootPairing_base.cartanMatrix i j +
          typeF4RootPairing.pairingIn ℤ r j) =
        typeF4RootPairing.pairingIn ℤ r j * c -
          simpleOperatorOrientation (b := typeF4RootPairing_base) i *
            typeF4RootPairing_base.cartanMatrix i j * y := by
      apply mul_left_cancel₀ hj0
      calc
        _ = n * (simpleOperatorOrientation (b := typeF4RootPairing_base) j *
            typeF4RootPairing.pairingIn ℤ s j) := by rw [hp]; ring
        _ = _ := he j
        _ = _ := by rw [habs]; ring
    change (n + simpleOperatorOrientation (b := typeF4RootPairing_base) i * y) *
      typeF4RootPairing_base.cartanMatrix i j +
        (n - c) * typeF4RootPairing.pairingIn ℤ r j = 0
    linear_combination he'
  have hc := (coefficients_zero_of_pairing_relation i r s hroot
    (n + simpleOperatorOrientation (b := typeF4RootPairing_base) i * y) (n - c) hpair).2
  rw [sub_eq_zero.mp hc] at hn
  exact hn

end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
