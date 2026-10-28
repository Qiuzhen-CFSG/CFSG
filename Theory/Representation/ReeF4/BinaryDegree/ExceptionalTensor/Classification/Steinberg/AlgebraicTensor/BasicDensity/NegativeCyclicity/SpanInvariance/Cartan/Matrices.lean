module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular

/-!
# Integral Cartan relations for the concrete F₄ matrices

Opposite-root operators share one Tits route, so their commutator is the
transport of the simple Geck Cartan matrix. The Tits grading identifies this
transport with the coroot diagonal. Integral coroot spanning puts it in the
span of the four simple diagonals. Homogeneity of all root operators gives
the Cartan/root commutator. These identities specialize to arbitrary fields,
including characteristic two, without dividing by any integer.

Source: Steinberg, *Representations of Algebraic Groups* (1963), §2,
equations (2.4)–(2.5), using the project's integral Geck construction.
The separate `Cartan.Transfer` module transports these matrix identities to
the actual coefficient operators of arbitrary rational factors.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
namespace NegativeCyclicity.SpanInvariance.CartanMatrices
noncomputable section
local instance cartanMatricesNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

abbrev rootMatrix (r : F4Chevalley.Root) : F4Chevalley.IntegralMatrix :=
  F4Chevalley.integralOperators.rootOperator r

def diagonalCartan (r : F4Chevalley.Root) : F4Chevalley.IntegralMatrix :=
  Matrix.diagonal (fun a => chevalleyBasisWeight (P := typeF4RootPairing) a r)

private theorem simple_bracket (i : typeF4RootPairing_base.support) :
    eMatrix i * fMatrix i - fMatrix i * eMatrix i = diagonalCartan i := by
  have hd : (diagonalCartan i).map (algebraMap ℤ ℝ) = RootPairing.GeckConstruction.h i := by
    ext (j | j) (k | k) <;>
      simp [diagonalCartan, chevalleyBasisWeight, RootPairing.GeckConstruction.h, Matrix.diagonal_apply]
  have he : (eMatrix i * fMatrix i - fMatrix i * eMatrix i).map (algebraMap ℤ ℝ) =
      (diagonalCartan i).map (algebraMap ℤ ℝ) := by
    rw [Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, map_eMatrix, map_fMatrix, hd]
    · exact RootPairing.GeckConstruction.lie_e_f_same i
    · exact fun a b => map_sub (algebraMap ℤ ℝ) a b
  ext j k
  exact Int.cast_injective (congrArg (fun A => A j k) he)

private theorem transported_diagonal (word : List typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) :
    transportedMatrix (P := typeF4RootPairing) word (diagonalCartan r) =
      diagonalCartan (reflectionWord word r) := by
  have h : titsWord (P := typeF4RootPairing) word * diagonalCartan r =
      diagonalCartan (reflectionWord word r) * titsWord word := by
    ext a b
    simp only [diagonalCartan, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hz : titsWord (P := typeF4RootPairing) word a b = 0
    · simp [hz]
    · have hw := titsWord_respectsChevalleyGrading (P := typeF4RootPairing)
        word a b hz (reflectionWord word r)
      rw [inverseReflectionWord_right_inverse] at hw
      rw [hw, mul_comm]
  rw [transportedMatrix, h, Matrix.mul_assoc, titsWord_mul_inv, Matrix.mul_one]

/-- Opposite integral root matrices bracket to the corresponding coroot diagonal. -/
theorem opposite_bracket (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) :
    rootMatrix r * rootMatrix (-r) - rootMatrix (-r) * rootMatrix r = diagonalCartan r := by
  change rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r *
    rootOperator (-r) - rootOperator (-r) * rootOperator r = _
  rw [rootOperator_of_pos r hr, rootOperator_neg_of_pos r hr]
  rw [← transportedMatrix_mul, ← transportedMatrix_mul]
  have hs (word : List typeF4RootPairing_base.support) (A B : F4Chevalley.IntegralMatrix) :
      transportedMatrix (P := typeF4RootPairing) word A - transportedMatrix word B =
        transportedMatrix word (A - B) := by
    simp only [transportedMatrix, Matrix.mul_sub, Matrix.sub_mul]
  rw [hs, simple_bracket, transported_diagonal, (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).target]

/-- Homogeneity gives the Cartan/root bracket over the integral lattice. -/
theorem diagonal_bracket (r s : F4Chevalley.Root) :
    diagonalCartan r * rootMatrix s - rootMatrix s * diagonalCartan r =
      typeF4RootPairing.pairingIn ℤ s r • rootMatrix s := by
  ext a b
  simp only [diagonalCartan, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply,
    Matrix.smul_apply, zsmul_eq_mul]
  by_cases hz : rootMatrix s a b = 0
  · simp [hz]
  · have hw := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) s 1
    rw [rootDividedPower_one] at hw
    have he := hw a b hz r
    simp only [Nat.cast_one, one_mul] at he
    rw [← he]
    simp only [Int.cast_id]
    ring


/-- Every coroot diagonal is an integral linear combination of the simple diagonals. -/
theorem diagonal_mem_simple_span (r : F4Chevalley.Root) :
    diagonalCartan r ∈ Submodule.span ℤ
      (Set.range fun i : typeF4RootPairing_base.support => diagonalCartan i) := by
  classical
  obtain ⟨f, _, _, hf⟩ := typeF4RootPairing_base.flip.exists_root_eq_sum_int r
  have ht : typeF4RootPairing.corootSpanMem ℤ r =
      ∑ j ∈ typeF4RootPairing_base.support, f j • typeF4RootPairing.corootSpanMem ℤ j := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, RootPairing.corootSpanMem,
      RootPairing.flip_root, RootPairing.Base.flip_support] using hf
  have hp (s : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ s r =
      ∑ j ∈ typeF4RootPairing_base.support, f j • typeF4RootPairing.pairingIn ℤ s j := by
    have h := congrArg (typeF4RootPairing.root'In ℤ s) ht
    simpa only [map_sum, map_smul, RootPairing.root'In_corootSpanMem_eq_pairingIn] using h
  have hD : diagonalCartan r =
      ∑ j ∈ typeF4RootPairing_base.support, f j • diagonalCartan j := by
    ext a b
    simp only [diagonalCartan, Matrix.sum_apply, Matrix.smul_apply]
    by_cases hab : a = b
    · subst b
      simp only [Matrix.diagonal_apply_eq]
      cases a with
      | inl i => simp [chevalleyBasisWeight]
      | inr s => exact hp s
    · simp [Matrix.diagonal_apply_ne _ hab]
  rw [hD]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)


variable {F : Type*} [Field F]

private theorem specialize_sub (A B : F4Chevalley.IntegralMatrix) :
    specializeMatrix (S := F) (A - B) = specializeMatrix A - specializeMatrix B :=
  map_sub (Int.castRingHom F).mapMatrix A B

private theorem specialize_add (A B : F4Chevalley.IntegralMatrix) :
    specializeMatrix (S := F) (A + B) = specializeMatrix A + specializeMatrix B :=
  map_add (Int.castRingHom F).mapMatrix A B

private theorem specialize_smul (c : ℤ) (A : F4Chevalley.IntegralMatrix) :
    specializeMatrix (S := F) (c • A) = (c : F) • specializeMatrix A := by
  rw [Int.cast_smul_eq_zsmul]
  exact map_zsmul (Int.castRingHom F).mapMatrix c A


/-- Specialization of the integral root operator to the coefficient field. -/
abbrev specializedRootMatrix (r : F4Chevalley.Root) :
    Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F :=
  specializeMatrix (S := F) (rootMatrix r)

/-- The simple commutator after specialization. -/
@[expose] def specializedCartanMatrix (i : Fin 4) :
    Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F :=
  specializedRootMatrix (typeF4SimpleRootIndex i) * specializedRootMatrix (-typeF4SimpleRootIndex i) -
    specializedRootMatrix (-typeF4SimpleRootIndex i) * specializedRootMatrix (typeF4SimpleRootIndex i)

private theorem specializedCartanMatrix_eq (i : Fin 4) :
    specializedCartanMatrix (F := F) i = specializeMatrix (S := F)
      (diagonalCartan (typeF4SimpleRootIndex i)) := by
  have h := congrArg (specializeMatrix (S := F))
    (opposite_bracket (typeF4SimpleRootIndex i)
      (typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv i).property))
  simpa only [specialize_sub, specializeMatrix_mul, specializedCartanMatrix,
    specializedRootMatrix] using h

/-- Every specialized opposite bracket lies in the span of the four simple brackets. -/
theorem specialized_opposite_mem_span (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) :
    specializedRootMatrix (F := F) r * specializedRootMatrix (-r) -
      specializedRootMatrix (-r) * specializedRootMatrix r ∈
        Submodule.span F (Set.range (specializedCartanMatrix (F := F))) := by
  have he : specializedRootMatrix (F := F) r * specializedRootMatrix (-r) -
      specializedRootMatrix (-r) * specializedRootMatrix r =
        specializeMatrix (S := F) (diagonalCartan r) := by
    have h := congrArg (specializeMatrix (S := F)) (opposite_bracket r hr)
    simpa only [specialize_sub, specializeMatrix_mul, specializedRootMatrix] using h
  rw [he]
  have h := diagonal_mem_simple_span r
  generalize diagonalCartan r = D at h ⊢
  induction h using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨i, rfl⟩ := hA
    obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    change specializeMatrix (S := F) (diagonalCartan (typeF4SimpleRootIndex j)) ∈ _
    rw [← specializedCartanMatrix_eq]
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero => simp [specializeMatrix]
  | add A B hA hB ihA ihB =>
    simpa only [specialize_add] using
      Submodule.add_mem _ ihA ihB
  | smul c A hA ihA =>
    rw [specialize_smul]
    exact Submodule.smul_mem _ _ ihA

/-- The specialized simple Cartan commutator acts with the integral coroot pairing. -/
theorem specialized_cartan_bracket (i : Fin 4) (s : F4Chevalley.Root) :
    specializedCartanMatrix (F := F) i * specializedRootMatrix s -
      specializedRootMatrix s * specializedCartanMatrix i =
        (typeF4RootPairing.pairingIn ℤ s (typeF4SimpleRootIndex i) : F) •
          specializedRootMatrix s := by
  rw [specializedCartanMatrix_eq]
  have h := congrArg (specializeMatrix (S := F))
    (diagonal_bracket (typeF4SimpleRootIndex i) s)
  simpa only [specialize_sub, specializeMatrix_mul, specialize_smul] using h

end
end NegativeCyclicity.SpanInvariance.CartanMatrices
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
