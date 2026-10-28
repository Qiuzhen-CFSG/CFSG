module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.AlternatingTensor
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.TensorAddition

/-!
# Existence of all four exceptional basic algebraic factors

The zero factor is the rational trivial line. The (0,1) factor is the genuine
short-module simple head. The alternating tensor of the top two short
coordinates realizes (1,0). Tensoring these last two highest vectors and
taking a simple head realizes (1,1). Every conclusion uses the published
root and direct-coroot equations, without a basic-model or classifier premise.

Source: GLS3 Definition 2.8.1(b), Section 1.14.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- All four source basic weights occur in actual rational irreducible factors. -/
theorem exists_basic_algebraicFactor (b : Fin 2 × Fin 2) :
    ∃ B : AlgebraicFactor F, Classification.HasBasicHighestWeight B b := by
  rcases b with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · exact exists_zero_factor
  · obtain ⟨B, hB, _⟩ := EndNode.exists_small_endNode_algebraicFactor (F := F)
    exact ⟨B, hB⟩
  · exact exists_middle_factor
  · obtain ⟨B, hB⟩ := exists_middle_factor (F := F)
    obtain ⟨C, hC, _⟩ := EndNode.exists_small_endNode_algebraicFactor (F := F)
    obtain ⟨D, hD⟩ := exists_factor_weight_add
      (a := basicCoefficient (1, 0)) (d := basicCoefficient (0, 1)) hB hC
    have he : basicCoefficient (1, 0) + basicCoefficient (0, 1) =
        basicCoefficient (1, 1) := by
      funext i
      fin_cases i <;> rfl
    rw [he] at hD
    exact ⟨D, hD⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
