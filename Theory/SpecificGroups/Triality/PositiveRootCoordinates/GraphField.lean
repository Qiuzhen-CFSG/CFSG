module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Curves
public import Theory.SpecificGroups.Triality.Model.QTKEParameters
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.GraphField.RouteComparison
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.NonsumCommute
public import Theory.AlgebraicGroup.RootSystems.TypeD4Irreducible

/-!
# Graph-field action on positive triality coordinates

The pinned diagram action carries each integral Tits route to a route ending
at the permuted root. Rational root-space multiplicity one and integral
primitivity compare this route with the canonical route up to a sign;
`RouteComparison` removes that sign after specialization to characteristic two.
Coefficient Frobenius acts on the parameter, giving the actual graph-field
action on all twelve positive Geck curves, including the case q = 2.

The roots in each three-element orbit have no root sums. The proved canonical
curve commutation theorem therefore permits rotation of the three orbit blocks.
This gives equivariance of the ordered product for the inverse-reindexed scalar
twist, without a normal-form or injectivity premise.

Source: GLS3, 2.3.6–7, Table 2.4 type III, and Remark 2.4.3
(`refs/KGroup/GLS3/chapter2.tex`). This is the graph-field action ingredient;
uniqueness and coverage of the positive normal form are separate results.
-/

public section

open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.PositiveCoordinates
noncomputable section
local instance : (typeDRootPairing 2).IsIrreducible := typeD4RootPairing_isIrreducible
private abbrev B := (typeDRootPairing_base 2).support
-- Match the structural index equality used by the imported matrix curves.
local instance : DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2 + 2)) :=
  instDecidableEqSum

private theorem diagram_reflection (r s : TypeDRootIndex 4) :
    typeD4DiagramEquiv.indexEquiv ((typeDRootPairing 2).reflectionPerm r s) =
      (typeDRootPairing 2).reflectionPerm (typeD4DiagramEquiv.indexEquiv r)
        (typeD4DiagramEquiv.indexEquiv s) := by
  apply (typeDRootPairing 2).root.injective
  rw [← diagram_weight_root]
  simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    map_sub, map_smul, diagram_weight_root, typeD4DiagramEquiv.pairing_eq]

private theorem diagram_word (w : List B) (r : TypeDRootIndex 4) :
    reflectionWord (w.map typeD4DiagramBasePermutation) (typeD4DiagramEquiv.indexEquiv r) =
      typeD4DiagramEquiv.indexEquiv (reflectionWord w r) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [List.map_cons, reflectionWord, ih, typeD4DiagramEquiv_simple] using
      (diagram_reflection i (reflectionWord w r)).symm

private theorem diagram_smul {S : Type*} [Semiring S] (s : S)
    (A : Matrix (B ⊕ TypeDRootIndex (2 + 2)) (B ⊕ TypeDRootIndex (2 + 2)) S) :
    diagramMatrixEquiv typeD4DiagramEquiv typeD4DiagramBasePermutation S (s • A) =
      s • diagramMatrixEquiv typeD4DiagramEquiv typeD4DiagramBasePermutation S A := rfl

private theorem diagram_titsLift (i : B) :
    diagramMatrixEquiv typeD4DiagramEquiv typeD4DiagramBasePermutation ℤ (titsLift i) =
      titsLift (typeD4DiagramBasePermutation i) := by
  simp only [titsLift, eUnipotent, fUnipotent, map_mul, map_add, map_one]
  simp only [diagram_smul,
    diagram_eDividedPower _ _ typeD4DiagramEquiv_simple,
    diagram_fDividedPower _ _ typeD4DiagramEquiv_simple]

private theorem diagram_titsWord (w : List B) :
    diagramMatrixEquiv typeD4DiagramEquiv typeD4DiagramBasePermutation ℤ (titsWord w) =
      titsWord (w.map typeD4DiagramBasePermutation) := by
  induction w with
  | nil => exact map_one _
  | cons i w ih => simp only [titsWord, map_mul, diagram_titsLift, ih, List.map_cons]

private theorem diagram_titsWordInv (w : List B) :
    diagramMatrixEquiv typeD4DiagramEquiv typeD4DiagramBasePermutation ℤ (titsWordInv w) =
      titsWordInv (w.map typeD4DiagramBasePermutation) := by
  apply left_inv_eq_right_inv (a := titsWord (w.map typeD4DiagramBasePermutation))
  · rw [← diagram_titsWord, ← map_mul, titsWord_inv_mul, map_one]
  · exact titsWord_mul_inv _

private theorem diagram_transport (w : List B) (i : B) (k : ℕ) :
    diagramMatrixEquiv typeD4DiagramEquiv typeD4DiagramBasePermutation ℤ
      (transportedMatrix w (eDividedPower i k)) =
    transportedMatrix (w.map typeD4DiagramBasePermutation)
      (eDividedPower (typeD4DiagramBasePermutation i) k) := by
  simp only [transportedMatrix, map_mul, diagram_titsWord, diagram_titsWordInv,
    diagram_eDividedPower _ _ typeD4DiagramEquiv_simple]

private theorem diagram_dividedPower_binary {S : Type*} [CommRing S] [CharP S 2]
    (i : Fin 12) (k : ℕ) :
    diagramMatrixEquiv typeD4DiagramEquiv typeD4DiagramBasePermutation S
      (specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) (rootIndex i) k)) =
    specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) (rootIndex (diagram i)) k) := by
  rw [rootDividedPower_of_pos _ (rootIndex_positive i),
    rootDividedPower_of_pos _ (rootIndex_positive (diagram i))]
  rw [specializeMatrix, diagramMatrixEquiv_map, diagram_transport]
  apply GraphFieldProof.specialize_route_eq
  rw [← typeD4DiagramEquiv_simple, diagram_word,
    (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).target,
    (rootRoute (b := typeDRootPairing_base 2) (rootIndex (diagram i))).target,
    diagram_rootIndex]

/-- In characteristic two the pinned diagram action preserves the curve parameter. -/
theorem diagram_curve_binary (n : ℕ) (hn : 0 < n) (i : Fin 12)
    (t : ExtensionField (binaryParameters n hn)) :
    diagramAutomorphism (binaryParameters n hn) (curve (binaryParameters n hn) i t) =
      curve (binaryParameters n hn) (diagram i) t := by
  apply Subtype.ext
  apply Units.ext
  change diagramMatrixEquiv typeD4DiagramEquiv typeD4DiagramBasePermutation _
    (rootCurveMatrix _ (rootIndex i) t) = rootCurveMatrix _ (rootIndex (diagram i)) t
  simp only [rootCurveMatrix, map_add, map_one, diagram_smul]
  rw [show (integralChevalleyRootOperators (b := typeDRootPairing_base 2)).rootDividedPower =
      rootDividedPower from rfl]
  rw [diagram_dividedPower_binary, diagram_dividedPower_binary, diagram_dividedPower_binary]

/-- Coefficient Frobenius acts on the parameter of each canonical integral curve. -/
theorem field_curve (P : Parameters) (i : Fin 12) (t : ExtensionField P) :
    fieldAutomorphism P (curve P i t) = curve P i (fieldFrobenius P t) := by
  apply Subtype.ext
  apply Units.ext
  change (rootCurveMatrix _ (rootIndex i) t).map (fieldFrobenius P) =
    rootCurveMatrix _ (rootIndex i) (fieldFrobenius P t)
  ext j k
  simp [rootCurveMatrix, specializeMatrix, Matrix.one_apply, -fieldFrobenius_apply]

/-- Graph-field action on each of the twelve actual positive Geck curves. -/
theorem graphField_curve_binary (n : ℕ) (hn : 0 < n) (i : Fin 12)
    (t : ExtensionField (binaryParameters n hn)) :
    graphFieldAutomorphism (binaryParameters n hn) (curve (binaryParameters n hn) i t) =
      curve (binaryParameters n hn) (diagram i) (fieldFrobenius (binaryParameters n hn) t) := by
  rw [graphFieldAutomorphism, MulEquiv.trans_apply, diagram_curve_binary, field_curve]

-- Integral coordinates make the finite absence-of-root-sum check decidable.
private def positiveCoords : Fin 12 → Fin 4 → ℤ :=
  ![![1,-1,0,0], ![0,0,1,-1], ![0,0,1,1], ![0,1,-1,0],
    ![1,0,-1,0], ![0,1,0,-1], ![0,1,0,1], ![1,0,0,-1],
    ![0,1,1,0], ![1,0,0,1], ![1,0,1,0], ![1,1,0,0]]

private theorem positiveCoords_spec (i : Fin 12) (j : Fin 4) :
    ((typeDRootPairing 2).root (rootIndex i) : Vec 4) j = (positiveCoords i j : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveCoords, rootIndex, difference, sumRoot, typeDRootPairing_root_val,
      typeDRootEmbedding, typeDRootVector, basisVector, Pi.single_apply, Fin.ext_iff]

private theorem positiveCoords_nonsum (i : Fin 12) :
    ¬ ∃ k : Fin 12, positiveCoords k = positiveCoords i + positiveCoords (diagram i) := by
  revert i
  decide +kernel

private theorem diagram_root_nonsum (i : Fin 12) :
    ¬ ∃ k : Fin 12, (typeDRootPairing 2).root (rootIndex k) =
      (typeDRootPairing 2).root (rootIndex i) +
        (typeDRootPairing 2).root (rootIndex (diagram i)) := by
  rintro ⟨k, h⟩
  apply positiveCoords_nonsum i
  refine ⟨k, ?_⟩
  ext j
  have hj := congrFun (congrArg Subtype.val h) j
  simp only [Submodule.coe_add, Pi.add_apply, positiveCoords_spec] at hj
  exact_mod_cast hj

/-- Curves in one diagram orbit commute over every parameter field. -/
theorem curve_diagram_commute (P : Parameters) (i : Fin 12) (s t : ExtensionField P) :
    Commute (curve P i s) (curve P (diagram i) t) := by
  by_cases h : i = diagram i
  · rw [← h]
    change _ * _ = _ * _
    rw [← curve_add, ← curve_add, add_comm s t]
  · exact nonsumCommute_parameters P i (diagram i) h (diagram_root_nonsum i) s t

-- Reorder the orbit blocks in an arbitrary monoid before specializing to the matrix group.
private theorem prod_blocks {G : Type*} [Monoid G] (f : Fin 12 → G) :
    (List.ofFn f).prod =
      (f 0 * f 1 * f 2) * f 3 * (f 4 * f 5 * f 6) *
      (f 7 * f 8 * f 9) * f 10 * f 11 := by
  simp [List.ofFn_succ, mul_assoc]

private theorem prod_diagram {G : Type*} [Monoid G] (f : Fin 12 → G)
    (h : ∀ i, Commute (f i) (f (diagram i))) :
    (List.ofFn fun i => f (diagram i)).prod = (List.ofFn f).prod := by
  have rot (i : Fin 12) :
      f (diagram i) * f (diagram (diagram i)) * f i =
        f i * f (diagram i) * f (diagram (diagram i)) := by
    have h2 := h (diagram (diagram i))
    rw [diagram_three] at h2
    exact ((h i).mul_right h2.symm).eq.symm.trans (mul_assoc _ _ _).symm
  have h0 := rot 0
  have h4 := rot 4
  have h7 := rot 7
  rw [prod_blocks, prod_blocks]
  change f 1 * f 2 * f 0 = f 0 * f 1 * f 2 at h0
  change f 5 * f 6 * f 4 = f 4 * f 5 * f 6 at h4
  change f 8 * f 9 * f 7 = f 7 * f 8 * f 9 at h7
  change (f 1 * f 2 * f 0) * f 3 * (f 5 * f 6 * f 4) *
      (f 8 * f 9 * f 7) * f 10 * f 11 = _
  rw [h0, h4, h7]

/-- Graph-field action on the actual ordered product of all twelve positive Geck curves.
The three length-three orbits are reordered using their proved commutation laws. -/
theorem graphField_orderedProduct_binary (n : ℕ) (hn : 0 < n)
    (a : Coordinates (binaryParameters n hn)) :
    graphFieldAutomorphism (binaryParameters n hn) (orderedProduct (binaryParameters n hn) a) =
      orderedProduct (binaryParameters n hn) (twist (binaryParameters n hn) a) := by
  unfold orderedProduct
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, graphField_curve_binary]
  have h := prod_diagram
    (fun i => curve (binaryParameters n hn) i (twist (binaryParameters n hn) a i))
    (fun i => curve_diagram_commute (binaryParameters n hn) i _ _)
  simpa only [twist, Equiv.symm_apply_apply] using h

end
end Triality.Standard.PositiveCoordinates
