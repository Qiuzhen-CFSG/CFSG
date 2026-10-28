module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.EnumerationSetup
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.ModelRelations
public import Theory.SpecificGroups.Janko3.Model.Order
public import Theory.GroupTheory.GeneratorCosetCoverIndex
public import Theory.GroupTheory.GeneratorCosetCoverFiniteIndex

/-!
# Assembly of the J₃ presentation bound from M₁

A certified cover of the literal subgroup M₁ gives at most 6156 cosets.
Its independent finite bound of 8160 then bounds the eight-relator group by
50232960 and makes its already-proved epimorphism to the ATLAS model bijective.
The cover and the subgroup bound are explicit outstanding inputs. No instance
of finiteness for the presentation is asserted before those inputs are supplied.

Source: ATLAS J3G1-P1, the M₁ enumeration route.
-/

namespace Sporadic.Janko3.RecognitionPresentation.OrderBound

/-- Finiteness is obtained from the actual covering, separately from its bound. -/
public theorem finite_card_le_of_m1
    (hM : Finite M1 ∧ Nat.card M1 ≤ 8160)
    (C : Subgroup.GeneratorCosetCover M1 generator (Fin 6156)) :
    Finite Presentation ∧ Nat.card Presentation ≤ 50232960 := by
  let : Finite M1 := hM.1
  obtain ⟨hf, hc⟩ := C.finite_card_le generator_generates
  refine ⟨hf, hc.trans ?_⟩
  simpa using Nat.mul_le_mul_right 6156 hM.2

/-- The finite-coset conclusion does not require M₁ itself to be finite. -/
public theorem m1_finiteIndex_of_cover
    (C : Subgroup.GeneratorCosetCover M1 generator (Fin 6156)) :
    M1.FiniteIndex ∧ M1.index ≤ 6156 := by
  exact ⟨⟨(C.index_pos generator_generates).ne'⟩,
    by simpa using C.index_le_card generator_generates⟩

/-- The source bound makes the canonical evaluation bijective, without assuming
simplicity of either the presentation or the concrete model. -/
public theorem evaluation_bijective_of_m1
    (hM : Finite M1 ∧ Nat.card M1 ≤ 8160)
    (C : Subgroup.GeneratorCosetCover M1 generator (Fin 6156)) :
    Function.Bijective (evaluation model_satisfies) := by
  obtain ⟨hf, hc⟩ := finite_card_le_of_m1 hM C
  let : Finite Presentation := hf
  apply evaluation_bijective_of_card_le model_satisfies generators_closure
  rwa [model_card]

/-- The equivalence is induced by the already defined evaluation map.
Both enumeration inputs still have to be proved in the abstract presentation. -/
public noncomputable def modelEquivOfM1
    (hM : Finite M1 ∧ Nat.card M1 ≤ 8160)
    (C : Subgroup.GeneratorCosetCover M1 generator (Fin 6156)) :
    Presentation ≃* Model :=
  MulEquiv.ofBijective (evaluation model_satisfies) (evaluation_bijective_of_m1 hM C)

@[simp] public theorem modelEquivOfM1_x
    (hM : Finite M1 ∧ Nat.card M1 ≤ 8160)
    (C : Subgroup.GeneratorCosetCover M1 generator (Fin 6156)) :
    modelEquivOfM1 hM C x = a := evaluation_x model_satisfies

@[simp] public theorem modelEquivOfM1_y
    (hM : Finite M1 ∧ Nat.card M1 ≤ 8160)
    (C : Subgroup.GeneratorCosetCover M1 generator (Fin 6156)) :
    modelEquivOfM1 hM C y = b := evaluation_y model_satisfies

/-- Once both enumerations are supplied, the abstract and concrete orders agree. -/
public theorem card_eq_of_m1
    (hM : Finite M1 ∧ Nat.card M1 ≤ 8160)
    (C : Subgroup.GeneratorCosetCover M1 generator (Fin 6156)) :
    Nat.card Presentation = 50232960 :=
  (Nat.card_congr (modelEquivOfM1 hM C).toEquiv).trans model_card

end Sporadic.Janko3.RecognitionPresentation.OrderBound
