module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Weights

/-!
# The 52-weight middle-node gap

The two middle basic highest weights have Weyl orbits of sizes 96 and 192.
The first 52 words of each orbit are certified here by the actual F4 Cartan
matrix. Normalizer transport and common-eigenspace independence then give the
middle-node part of the exact small-degree exclusion used at the Tits endpoint.

Source: GLS3, Sections 1.8 and 1.14.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle

private def middleWords52 : Fin 2 → Fin 52 → List (Fin 4)
  | 0 =>
  ![
    [],
    [2],
    [2, 1],
    [2, 3],
    [2, 1, 0],
    [2, 1, 2],
    [2, 1, 3],
    [2, 1, 0, 2],
    [2, 1, 0, 3],
    [2, 1, 2, 3],
    [2, 1, 3, 2],
    [2, 1, 0, 2, 1],
    [2, 1, 0, 2, 3],
    [2, 1, 0, 3, 2],
    [2, 1, 2, 3, 2],
    [2, 1, 3, 2, 1],
    [2, 1, 0, 2, 1, 2],
    [2, 1, 0, 2, 1, 3],
    [2, 1, 0, 2, 3, 2],
    [2, 1, 0, 3, 2, 1],
    [2, 1, 2, 3, 2, 1],
    [2, 1, 3, 2, 1, 0],
    [2, 1, 0, 2, 1, 2, 3],
    [2, 1, 0, 2, 1, 3, 2],
    [2, 1, 0, 2, 3, 2, 1],
    [2, 1, 0, 3, 2, 1, 0],
    [2, 1, 0, 3, 2, 1, 2],
    [2, 1, 2, 3, 2, 1, 0],
    [2, 1, 2, 3, 2, 1, 2],
    [2, 1, 0, 2, 1, 2, 3, 2],
    [2, 1, 0, 2, 1, 3, 2, 1],
    [2, 1, 0, 2, 3, 2, 1, 0],
    [2, 1, 0, 2, 3, 2, 1, 2],
    [2, 1, 0, 3, 2, 1, 0, 2],
    [2, 1, 0, 3, 2, 1, 2, 3],
    [2, 1, 2, 3, 2, 1, 0, 2],
    [2, 1, 0, 2, 1, 2, 3, 2, 1],
    [2, 1, 0, 2, 1, 3, 2, 1, 0],
    [2, 1, 0, 2, 1, 3, 2, 1, 2],
    [2, 1, 0, 2, 3, 2, 1, 0, 2],
    [2, 1, 0, 2, 3, 2, 1, 2, 3],
    [2, 1, 0, 3, 2, 1, 0, 2, 1],
    [2, 1, 0, 3, 2, 1, 0, 2, 3],
    [2, 1, 2, 3, 2, 1, 0, 2, 1],
    [2, 1, 0, 2, 1, 2, 3, 2, 1, 0],
    [2, 1, 0, 2, 1, 2, 3, 2, 1, 2],
    [2, 1, 0, 2, 1, 3, 2, 1, 0, 2],
    [2, 1, 0, 2, 1, 3, 2, 1, 2, 3],
    [2, 1, 0, 2, 3, 2, 1, 0, 2, 1],
    [2, 1, 0, 2, 3, 2, 1, 0, 2, 3],
    [2, 1, 0, 3, 2, 1, 0, 2, 1, 3],
    [2, 1, 2, 3, 2, 1, 0, 2, 1, 2]
  ]
  | 1 =>
  ![
    [],
    [2],
    [3],
    [2, 1],
    [2, 3],
    [3, 2],
    [2, 1, 0],
    [2, 1, 2],
    [2, 1, 3],
    [2, 3, 2],
    [3, 2, 1],
    [2, 1, 0, 2],
    [2, 1, 0, 3],
    [2, 1, 2, 3],
    [2, 1, 3, 2],
    [2, 3, 2, 1],
    [3, 2, 1, 0],
    [3, 2, 1, 2],
    [2, 1, 0, 2, 1],
    [2, 1, 0, 2, 3],
    [2, 1, 0, 3, 2],
    [2, 1, 2, 3, 2],
    [2, 1, 3, 2, 1],
    [2, 3, 2, 1, 0],
    [2, 3, 2, 1, 2],
    [3, 2, 1, 0, 2],
    [3, 2, 1, 2, 3],
    [2, 1, 0, 2, 1, 2],
    [2, 1, 0, 2, 1, 3],
    [2, 1, 0, 2, 3, 2],
    [2, 1, 0, 3, 2, 1],
    [2, 1, 2, 3, 2, 1],
    [2, 1, 3, 2, 1, 0],
    [2, 1, 3, 2, 1, 2],
    [2, 3, 2, 1, 0, 2],
    [2, 3, 2, 1, 2, 3],
    [3, 2, 1, 0, 2, 1],
    [3, 2, 1, 0, 2, 3],
    [2, 1, 0, 2, 1, 2, 3],
    [2, 1, 0, 2, 1, 3, 2],
    [2, 1, 0, 2, 3, 2, 1],
    [2, 1, 0, 3, 2, 1, 0],
    [2, 1, 0, 3, 2, 1, 2],
    [2, 1, 2, 3, 2, 1, 0],
    [2, 1, 2, 3, 2, 1, 2],
    [2, 1, 3, 2, 1, 0, 2],
    [2, 1, 3, 2, 1, 2, 3],
    [2, 3, 2, 1, 0, 2, 1],
    [2, 3, 2, 1, 0, 2, 3],
    [3, 2, 1, 0, 2, 1, 2],
    [3, 2, 1, 0, 2, 1, 3],
    [2, 1, 0, 2, 1, 2, 3, 2]
  ]
private theorem middleWords52_distinct (b : Fin 2) :
    Function.Injective (fun n => reflectWord (middleWords52 b n)
      ![0, 0, 1, (b.val : ℤ)]) := by
  fin_cases b <;> decide

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Every middle basic factor has degree at least 52. -/
theorem middle_basicHighestWeight_finrank_ge_52
    (B : AlgebraicFactor F) (b : Fin 2)
    (h : B.HasBasicHighestWeight (1, b)) :
    52 ≤ Module.finrank F B.Space := by
  classical
  obtain ⟨v, hv⟩ := h
  have hstart : IsCorootWeightVector B ![0, 0, 1, (b.val : ℤ)] v := by
    refine ⟨hv.1, ?_⟩
    intro i t
    have hh := hv.2.2 i t
    fin_cases i <;> simpa [basicCoefficient] using hh
  have hwords (n : Fin 52) : ∃ w,
      IsCorootWeightVector B
        (reflectWord (middleWords52 b n) ![0, 0, 1, (b.val : ℤ)]) w :=
    exists_corootWeightVector_word B _ ⟨v, hstart⟩
  choose w hw using hwords
  have hind := corootWeightVectors_linearIndependent B _
    (middleWords52_distinct b) w hw
  simpa only [Fintype.card_fin] using hind.fintype_card_le_finrank

end ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
