module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.SimpleHead
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.ShortPair

/-!
# A genuine λ₃ factor from the rational short-module tensor square

The alternating tensor β⊗γ−γ⊗β is nonzero by two actual coordinate
functionals. Positive root curves fix it because β is fixed and γ only
changes by a multiple of β. Its two coroot eigencharacters multiply to λ₃.
The rational tensor construction and cyclic simple head give an algebraic
irreducible factor, without an exterior-power rationality or classifier premise.

Source: GLS3 Section 1.14 and Definition 2.8.1(b).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped TensorProduct
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The alternating tensor on the two literal highest short coordinates. -/
def alternatingVector :
    TensorProduct F (F4Chevalley.shortSubmodule (k := F)) (F4Chevalley.shortSubmodule (k := F)) :=
  ShortPair.betaVector ⊗ₜ[F] ShortPair.gammaVector -
    ShortPair.gammaVector ⊗ₜ[F] ShortPair.betaVector

omit [IsAlgClosed F] [CharP F 2] in
theorem alternatingVector_ne_zero : alternatingVector (F := F) ≠ 0 := by
  obtain ⟨f, g, hfb, hfg, _, hgg⟩ := ShortPair.separating_forms (F := F)
  intro h
  have he := congrArg (TensorProduct.lift (f.smulRight g)) h
  simp [alternatingVector, hfb, hfg, hgg] at he

theorem alternatingVector_highest
    (τ : RationalRepresentation (F4Chevalley.Carrier (k := F))
      (TensorProduct F (F4Chevalley.shortSubmodule (k := F)) (F4Chevalley.shortSubmodule (k := F))))
    (hτ : IsTensorProductRepresentation F4Chevalley.shortRepresentation
      F4Chevalley.shortRepresentation τ) :
    HighestVector τ (basicCoefficient (1, 0)) alternatingVector := by
  refine ⟨alternatingVector_ne_zero, ?_, ?_⟩
  · intro r hr t
    obtain ⟨a, hγ⟩ := ShortPair.gamma_root r hr t
    simp only [alternatingVector, map_sub]
    rw [hτ, hτ]
    simp only [ShortPair.beta_root r hr t, hγ, TensorProduct.tmul_add,
      TensorProduct.add_tmul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
    abel
  · intro i t
    have hab := ShortPair.coroot_product i t
    have hba : ((t ^ ShortPair.gammaWeight i : Fˣ) : F) *
        (t : F) ^ basicCoefficient (0, 1) i = (t : F) ^ basicCoefficient (1, 0) i := by
      rw [mul_comm]
      exact hab
    simp only [alternatingVector, map_sub]
    rw [hτ, hτ]
    simp only [ShortPair.beta_coroot, ShortPair.gamma_coroot,
      TensorProduct.smul_tmul_smul, hab, hba, smul_sub]

/-- An actual rational irreducible factor of source basic weight (1,0). -/
theorem exists_middle_factor :
    ∃ B : AlgebraicFactor F, Classification.HasBasicHighestWeight B (1, 0) := by
  obtain ⟨τ, hτ, hRat⟩ := rationalRepresentation_tensorProduct_exists
    (F4Chevalley.shortRepresentation (k := F)) F4Chevalley.shortRepresentation
    F4Chevalley.shortRepresentation_isRational F4Chevalley.shortRepresentation_isRational
  obtain ⟨B, hB, _⟩ := exists_factor_of_highestVector τ hRat (alternatingVector_highest τ hτ)
  exact ⟨B, hB⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
