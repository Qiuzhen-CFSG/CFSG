module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.ShortA2
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation

/-!
# Actual normalizer words and positive-root transport

Words act from left to right on vectors. Conjugation by their inverses therefore
acts on roots in the opposite order. The characteristic-two matrix conjugation
identity is carried into the closed algebraic F4 carrier through its injective
inclusion. The two roots above the short A2 simple roots under the inverse of
entry eight have positive simple coefficients `(1,1,1,1)` and `(0,1,2,1)`.

Source: GLS3, Theorem 1.12.1(h), and Section 1.14. The explicit coordinate
reflection calculation follows the proof in
`ParabolicAmalgam/OuterLocal/SuzukiCommutators/NormalGeneration/MatrixRelations/WeylGeometry.lean`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode

universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The carrier representative whose successive simple reflections act in list order. -/
@[expose] noncomputable def normalizerWord : List (Fin 4) →
    Variety.Point (F4Chevalley.Carrier (k := F))
  | [] => 1
  | i :: w => normalizerWord w * algebraicNElement (typeF4SimpleRootIndex i) 1

/-- The root action of the inverse of a left-to-right normalizer word. -/
@[expose] noncomputable def inverseRootWord : List (Fin 4) → F4Chevalley.Root → F4Chevalley.Root
  | [], r => r
  | i :: w, r => typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) (inverseRootWord w r)

private noncomputable def matrixToAmbient :
    (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ →*
      Variety.Point (F4Chevalley.Ambient F) where
  toFun A := generalLinearRepresentationPoint
    (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    (Matrix.GeneralLinearGroup.toLin A)
  map_one' := by rw [map_one, generalLinearRepresentationPoint_one]
  map_mul' A B := by rw [map_mul, generalLinearRepresentationPoint_mul]

private theorem inclusion_root (r : F4Chevalley.Root) (t : F) :
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
      (algebraicRootElement r t) = matrixToAmbient (F4Chevalley.rootCurve r t) := by
  rw [algebraicRootElement, F4Chevalley.rootMorphism_inclusion_apply,
    F4Chevalley.ambientRootMorphism_apply]
  rfl

private theorem inclusion_n (i : Fin 4) :
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
      (algebraicNElement (typeF4SimpleRootIndex i) 1) =
        matrixToAmbient (ReeF4.WordRelations.titsUnit [typeF4RootPairing_baseEquiv i]) := by
  let := typeF4RootPairing.indexNeg
  simp only [algebraicNElement, map_mul, inclusion_root, Units.val_one, inv_one,
    ReeF4.WordRelations.titsUnit_cons, ReeF4.WordRelations.titsUnit_nil, mul_one,
    typeF4RootPairing_baseEquiv_val]

/-- A simple normalizer conjugates actual root elements, with no parameter sign
in characteristic two. -/
theorem n_root_conjugation [CharP F 2] (i : Fin 4) (r : F4Chevalley.Root) (t : F) :
    algebraicNElement (typeF4SimpleRootIndex i) 1 * algebraicRootElement r t *
      (algebraicNElement (typeF4SimpleRootIndex i) 1)⁻¹ =
    algebraicRootElement (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  simp only [map_mul, map_inv, inclusion_root, inclusion_n]
  simpa only [map_mul, map_inv, typeF4RootPairing_baseEquiv_val] using
    congrArg (matrixToAmbient (F := F))
      (ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj
        (typeF4RootPairing_baseEquiv i) r t)

/-- Move a root element past a simple representative to the right. -/
theorem root_n_commute [CharP F 2] (i : Fin 4) (r : F4Chevalley.Root) (t : F) :
    algebraicRootElement r t * algebraicNElement (typeF4SimpleRootIndex i) 1 =
    algebraicNElement (typeF4SimpleRootIndex i) 1 *
      algebraicRootElement (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  have h := n_root_conjugation i
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t
  rw [typeF4RootPairing.reflectionPerm_self] at h
  rw [← h]
  group

/-- Conjugation along the entire word takes place inside the algebraic carrier. -/
theorem root_normalizerWord_commute [CharP F 2] (w : List (Fin 4))
    (r : F4Chevalley.Root) (t : F) :
    algebraicRootElement r t * normalizerWord w =
      normalizerWord w * algebraicRootElement (inverseRootWord w r) t := by
  induction w with
  | nil => simp [normalizerWord, inverseRootWord]
  | cons i w ih =>
    simp only [normalizerWord, inverseRootWord]
    rw [← mul_assoc, ih, mul_assoc, root_n_commute, ← mul_assoc]

private noncomputable def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

/-- Exact simple-root expansion of the first inverse image. -/
theorem inverseRootWord_eight_two :
    (inverseRootWord (endOrbitWord 8) (typeF4SimpleRootIndex 2)).val =
      ∑ j : Fin 4, (![1, 1, 1, 1] j : ℕ) • typeF4SimpleRoot j := by
  change (inverseRootWord [3, 2, 1, 0, 2, 1] (typeF4SimpleRootIndex 2)).val = _
  simp only [inverseRootWord, reflection_val, typeF4SimpleRootIndex_val]
  ext k
  fin_cases k <;> norm_num [reflectedVector, typeF4SimpleRoot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- Exact simple-root expansion of the second inverse image. -/
theorem inverseRootWord_eight_three :
    (inverseRootWord (endOrbitWord 8) (typeF4SimpleRootIndex 3)).val =
      ∑ j : Fin 4, (![0, 1, 2, 1] j : ℕ) • typeF4SimpleRoot j := by
  change (inverseRootWord [3, 2, 1, 0, 2, 1] (typeF4SimpleRootIndex 3)).val = _
  simp only [inverseRootWord, reflection_val, typeF4SimpleRootIndex_val]
  ext k
  fin_cases k <;> norm_num [reflectedVector, typeF4SimpleRoot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

private theorem isPos_of_expansion (r : F4Chevalley.Root) (c : Fin 4 → ℕ)
    (hc : r.val = ∑ j : Fin 4, c j • typeF4SimpleRoot j) :
    typeF4RootPairing_base.IsPos r := by
  rw [RootPairing.Base.isPos_iff_root_mem_closure]
  change r.val ∈ _
  rw [hc]
  apply AddSubmonoid.sum_mem
  intro j _
  apply AddSubmonoid.nsmul_mem
  apply AddSubmonoid.subset_closure
  exact ⟨typeF4SimpleRootIndex j, (typeF4RootPairing_baseEquiv j).property, rfl⟩

theorem inverseRootWord_eight_two_isPos :
    typeF4RootPairing_base.IsPos
      (inverseRootWord (endOrbitWord 8) (typeF4SimpleRootIndex 2)) :=
  isPos_of_expansion _ _ inverseRootWord_eight_two

theorem inverseRootWord_eight_three_isPos :
    typeF4RootPairing_base.IsPos
      (inverseRootWord (endOrbitWord 8) (typeF4SimpleRootIndex 3)) :=
  isPos_of_expansion _ _ inverseRootWord_eight_three

end ReeF4.BinaryDegree.ExceptionalTensor.EndNode
