module

public import Theory.Representation.G2.TensorClassification.Construction

/-!
# Highest vectors in the concrete G₂ Frobenius tensors

The recursive tensor of the four specified highest vectors is nonzero: an
explicit tensor coefficient evaluates to one. It is fixed by the actual positive
unipotent group, and its simple-coroot weights are the binary sums of the
restricted weights. Short/long refer to Wilson F/E, so the short coordinate is
GLS3's λ₂ and the long coordinate is λ₁.

These formulas do not assert uniqueness of the fixed line or cyclicity. Those
are separate obligations in the proof of GLS3, 2.8.6(a) and 2.8.10(g).

The concrete coordinate actions use the attributed ATLAS port already imported
by `RestrictedModules`; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Atlas.G2.TensorClassification
open Restricted Explicit

variable (F : Type*) [Field F] [CharP F 2]

/-- False selects the short root (GLS3 λ₂), true the long root (GLS3 λ₁). -/
def weightBit (s : Bool) (a : Factor) : ℕ :=
  if s then a.longWeight else a.shortWeight

/-- Binary highest-weight coordinate, with the first letter least significant. -/
def wordWeight (s : Bool) : List Factor → ℕ
  | [] => 0
  | a :: w => weightBit s a + 2 * wordWeight s w

/-- The two marked simple coroots of the actual octonion group. -/
def simpleCoroot (s : Bool) (t : Fˣ) : Model F :=
  if s then longCoroot t else shortCoroot t

/-- A coefficient taking value one on the specified factor highest vector. -/
def factorHighestCoefficient : (a : Factor) → Space F a →ₗ[F] F
  | .trivial => LinearMap.id
  | .natural => LinearMap.proj 0
  | .adjoint => (LinearMap.proj 0).comp (Adjoint.Coordinates.equiv F).toLinearMap
  | .steinberg => (LinearMap.proj (0, 0, 1)).comp
      ((Steinberg.coordinates F).toLinearMap.comp (Steinberg.orbitSpan F).toSubmodule.subtype)

@[simp] theorem factorHighestCoefficient_highestVector (a : Factor) :
    factorHighestCoefficient F a (highestVector F a) = 1 := by
  cases a with
  | trivial => rfl
  | natural =>
    change (Pi.single 0 (1 : F) : Fin 6 → F) 0 = 1
    simp
  | adjoint =>
    change Adjoint.Coordinates.equiv F (Adjoint.highestVector F) 0 = 1
    rw [Adjoint.equiv_highestVector]
    simp [Adjoint.Coordinates.highestVector]
  | steinberg => exact Steinberg.coordinates_seed_001 F

/-- The pure tensor of the actual highest vectors. -/
def wordHighestVector : (w : List Factor) → WordSpace F w
  | [] => (1 : F)
  | a :: w => highestVector F a ⊗ₜ[F] wordHighestVector w

/-- Tensor of the specified highest coefficients. -/
def wordHighestCoefficient : (w : List Factor) → WordSpace F w →ₗ[F] F
  | [] => LinearMap.id
  | a :: w => (TensorProduct.lid F F).toLinearMap.comp
      (TensorProduct.map (factorHighestCoefficient F a) (wordHighestCoefficient w))

@[simp] theorem wordHighestCoefficient_highestVector (w : List Factor) :
    wordHighestCoefficient F w (wordHighestVector F w) = 1 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (TensorProduct.lid F F)
      (TensorProduct.map (factorHighestCoefficient F a) (wordHighestCoefficient F w)
        (highestVector F a ⊗ₜ[F] wordHighestVector F w)) = 1
    rw [TensorProduct.map_tmul, factorHighestCoefficient_highestVector, ih,
      TensorProduct.lid_tmul]
    simp

theorem wordHighestVector_ne_zero (w : List Factor) : wordHighestVector F w ≠ 0 := by
  intro h
  have hc := wordHighestCoefficient_highestVector F w
  rw [h, map_zero] at hc
  exact zero_ne_one hc

omit [CharP F 2] in
private theorem field_unipotentProduct (σ : F ≃+* F) (t : Fin 6 → F) :
    fieldEquiv σ (unipotentProduct t) = unipotentProduct (σ ∘ t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [fieldEquiv, Atlas.SplitOctonion.transportAutomorphism,
    Atlas.SplitOctonion.transportLinear, Atlas.SplitOctonion.mapCoefficients,
    unipotentProduct, rootA, rootB, rootC, rootD, rootE, rootF,
    rootAEquiv, rootBEquiv, rootCEquiv, rootDEquiv, rootEEquiv, rootFEquiv,
    rootALinear, rootBLinear, rootCLinear, rootDLinear, rootELinear, rootFLinear,
    rootAApply, rootBApply, rootCApply, rootDApply, rootEApply, rootFApply]

omit [CharP F 2] in
private theorem field_unipotent_mem (σ : F ≃+* F) (g : Model F)
    (hg : g ∈ unipotent) : fieldEquiv σ g ∈ unipotent := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  rw [field_unipotentProduct]
  exact unipotentProduct_mem _

omit [CharP F 2] in
private theorem field_torus (σ : F ≃+* F) (l m : Fˣ) :
    fieldEquiv σ (torus l m) =
      torus (Units.map σ.toMonoidHom l) (Units.map σ.toMonoidHom m) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [fieldEquiv, Atlas.SplitOctonion.transportAutomorphism,
    Atlas.SplitOctonion.transportLinear, Atlas.SplitOctonion.mapCoefficients,
    torus, torusEquiv, torusLinear, torusWeights]

omit [CharP F 2] in
private theorem field_simpleCoroot (σ : F ≃+* F) (s : Bool) (t : Fˣ) :
    fieldEquiv σ (simpleCoroot F s t) =
      simpleCoroot F s (Units.map σ.toMonoidHom t) := by
  cases s <;> simp [simpleCoroot, shortCoroot, longCoroot, field_torus]

variable [Finite F]

theorem factorHighestVector_fixed_unipotent (r : ℕ) (a : Factor) (g : Model F)
    (hg : g ∈ unipotent) : factorRep F r a g (highestVector F a) = highestVector F a :=
  highestVector_fixed_unipotent F a _ (field_unipotent_mem F _ g hg)

theorem wordHighestVector_fixed_unipotent (r : ℕ) (w : List Factor) (g : Model F)
    (hg : g ∈ unipotent) : wordRep F r w g (wordHighestVector F w) = wordHighestVector F w := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
    change factorRep F r a g (highestVector F a) ⊗ₜ[F]
      wordRep F (r + 1) w g (wordHighestVector F w) = _
    rw [factorHighestVector_fixed_unipotent F r a g hg, ih]
    rfl

theorem factorHighestVector_simpleCoroot (r : ℕ) (a : Factor) (s : Bool) (t : Fˣ) :
    factorRep F r a (simpleCoroot F s t) (highestVector F a) =
      (t : F) ^ (2 ^ r * weightBit s a) • highestVector F a := by
  change action F a (fieldEquiv (iterateFrobeniusEquiv F 2 r) _) _ = _
  rw [field_simpleCoroot]
  cases s <;>
    simp [simpleCoroot, weightBit, highestVector_shortCoroot, highestVector_longCoroot,
      iterateFrobeniusEquiv_apply, iterateFrobenius_def, ← pow_mul]

theorem wordHighestVector_simpleCoroot (r : ℕ) (w : List Factor) (s : Bool) (t : Fˣ) :
    wordRep F r w (simpleCoroot F s t) (wordHighestVector F w) =
      (t : F) ^ (2 ^ r * wordWeight s w) • wordHighestVector F w := by
  induction w generalizing r with
  | nil => change (1 : F) = (t : F) ^ (2 ^ r * 0) • 1; simp
  | cons a w ih =>
    change factorRep F r a (simpleCoroot F s t) (highestVector F a) ⊗ₜ[F]
      wordRep F (r + 1) w (simpleCoroot F s t) (wordHighestVector F w) =
        (t : F) ^ (2 ^ r * wordWeight s (a :: w)) •
          (highestVector F a ⊗ₜ[F] wordHighestVector F w)
    rw [factorHighestVector_simpleCoroot, ih, TensorProduct.smul_tmul_smul, ← pow_add]
    congr 2
    simp [wordWeight, pow_succ, Nat.mul_add, Nat.mul_assoc]

variable (K : Type*) [Field K] [Algebra F K]

/-- The highest vector on the scalar-extended tensor carrier. -/
def tensorHighestVector {n : ℕ} (w : Fin n → Factor) : TensorSpace F K w :=
  (1 : K) ⊗ₜ[F] wordHighestVector F (List.ofFn w)

/-- Its normalized coefficient after scalar extension. -/
def tensorHighestCoefficient {n : ℕ} (w : Fin n → Factor) : TensorSpace F K w →ₗ[K] K :=
  (TensorProduct.AlgebraTensorModule.rid F K K).toLinearMap.comp
    ((wordHighestCoefficient F (List.ofFn w)).baseChange K)

omit [Finite F] in
@[simp] theorem tensorHighestCoefficient_highestVector {n : ℕ} (w : Fin n → Factor) :
    tensorHighestCoefficient F K w (tensorHighestVector F K w) = 1 := by
  simp [tensorHighestCoefficient, tensorHighestVector]

omit [Finite F] in
theorem tensorHighestVector_ne_zero {n : ℕ} (w : Fin n → Factor) :
    tensorHighestVector F K w ≠ 0 := by
  intro h
  have hc := tensorHighestCoefficient_highestVector F K w
  rw [h, map_zero] at hc
  exact zero_ne_one hc

theorem tensorHighestVector_fixed_unipotent {n : ℕ} (w : Fin n → Factor) (g : Model F)
    (hg : g ∈ unipotent) :
    tensorRep F K w g (tensorHighestVector F K w) = tensorHighestVector F K w := by
  change (1 : K) ⊗ₜ[F] wordRep F 0 (List.ofFn w) g (wordHighestVector F (List.ofFn w)) = _
  rw [wordHighestVector_fixed_unipotent F 0 _ g hg]
  rfl

theorem tensorHighestVector_simpleCoroot {n : ℕ} (w : Fin n → Factor)
    (s : Bool) (t : Fˣ) :
    tensorRep F K w (simpleCoroot F s t) (tensorHighestVector F K w) =
      algebraMap F K (t : F) ^ wordWeight s (List.ofFn w) • tensorHighestVector F K w := by
  change (1 : K) ⊗ₜ[F]
    wordRep F 0 (List.ofFn w) (simpleCoroot F s t) (wordHighestVector F (List.ofFn w)) = _
  rw [wordHighestVector_simpleCoroot]
  simp only [pow_zero, one_mul, TensorProduct.tmul_smul, tensorHighestVector,
    ← map_pow, algebraMap_smul]

end Atlas.G2.TensorClassification
end
