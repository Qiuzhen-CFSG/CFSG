module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.SimpleHead

/-!
# Addition of realized source highest weights

A pure tensor of two nonzero highest vectors has the sum of their direct
coroot weights and is fixed by every positive root curve. The proved
rational tensor construction and cyclic simple head therefore realize
the sum without asserting that the entire tensor product is irreducible.

Source: GLS3 Section 1.14.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped TensorProduct
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

omit [IsAlgClosed F] in
private theorem tmul_nonzero {V W : Type u}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[F] w ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one F hv
  intro h
  have he := congrArg (fun z => TensorProduct.lid F W (TensorProduct.map f LinearMap.id z)) h
  exact hw (by simpa [hf] using he)

/-- Two genuinely realized algebraic highest weights have a realized sum. -/
theorem exists_factor_weight_add {B C : AlgebraicFactor F} {a d : Weight}
    (hB : HasHighestWeight B a) (hC : HasHighestWeight C d) :
    ∃ D : AlgebraicFactor F, HasHighestWeight D (a + d) := by
  obtain ⟨v, hv, hp, hc⟩ := hB
  obtain ⟨w, hw, hq, hd⟩ := hC
  obtain ⟨τ, hτ, hRat⟩ := rationalRepresentation_tensorProduct_exists
    B.action C.action B.irreducible.1 C.irreducible.1
  have ht : HighestVector τ (a + d) (v ⊗ₜ[F] w) := by
    refine ⟨tmul_nonzero hv hw, ?_, ?_⟩
    · intro r hr t
      rw [hτ, hp r hr t, hq r hr t]
    · intro i t
      rw [hτ, hc, hd, TensorProduct.smul_tmul_smul, ← pow_add]
      rfl
  obtain ⟨D, hD, _⟩ := exists_factor_of_highestVector τ hRat ht
  exact ⟨D, hD⟩

/-- The genuine one-dimensional trivial factor realizes the zero basic weight. -/
theorem exists_zero_factor :
    ∃ B : AlgebraicFactor F, Classification.HasBasicHighestWeight B (0, 0) := by
  let ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) F := ⟨1⟩
  have hr : IsRationalRepresentation ρ := by
    let e := Module.finBasis F F
    let c : Fin (Module.finrank F F) → Fin (Module.finrank F F) →
        (F4Chevalley.Carrier (k := F)).PolynomialFunction := fun i j =>
      algebraMap F _ (e.repr (e j) i)
    let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient e ρ.action c c
      (by intro i j g; rw [polynomialFunction_algebraMap_apply]; rfl)
      (by intro i j g; rw [polynomialFunction_algebraMap_apply]; rfl)
    exact ⟨e, f, fun g => glPointEquivOf_generalLinearRepresentationPoint e _⟩
  let B : AlgebraicFactor F :=
    { Space := F
      action := ρ
      irreducible := ⟨hr, fun W _ => eq_bot_or_eq_top W⟩ }
  refine ⟨B, 1, one_ne_zero, ?_, ?_⟩
  · intro r hr t
    rfl
  · intro i t
    change (1 : F) = ((t : F) ^ basicCoefficient (0, 0) i) • (1 : F)
    simp [basicCoefficient]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
