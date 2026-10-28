module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Inputs
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.WordDescent
public import Mathlib.LinearAlgebra.Matrix.Rank
-- Internal coefficient/torus realization bridges; public definitions stay unchanged.
import all Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding
import all Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Coordinates

/-!
# The binary Ree equation on the short ideal and its quotient

The quotient-to-ideal matrix intertwines ordinary and exceptional root-word
evaluation over the finite Ree coefficient field. At parameter zero the fixed
equation therefore makes it commute with every binary Ree matrix. Base change
 preserves this identity and identifies the short-ideal block with the long
 quotient block, indexed by the fixed root duality.

Invariance of the short ideal makes both blocks genuine actions. The explicit
surjective quotient projection has precisely that ideal as kernel and is
equivariant; no invariance of a long-coordinate complement is used. Conjugacy
in the actual algebraic carrier preserves the displacement rank of each action.
Consequently their ranks agree on every torus presentation of a binary Ree
element, without any element-order restriction. The positive coroot product
has diagonal characters with the positive basis weights.

These are the group-action inputs to the odd-element estimate in
Guralnick--Malle II, Lemma 8.8 (internal p.57), using the F4 conventions of GLS3,
Sections 1.14 and 2.8. Identification with the two published 24-weight tables
is a separate obligation in `Balance`.
-/

public section

open Theory.AlgebraicGroup ReeF4.WordRelations
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.Classification
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
open scoped Matrix
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance

theorem exceptional_intertwines (m : ℕ) (x : SplitGroup m) :
    quotientToIdeal * (x.val : Matrix Coordinate Coordinate (CoefficientField m)) =
      ((exceptionalEndomorphism m x).val : Matrix Coordinate Coordinate (CoefficientField m)) *
        quotientToIdeal := by
  obtain ⟨w, rfl⟩ := splitWordEval_surjective m x
  rw [exceptionalEndomorphism_word, splitWordEval_coe]
  exact eval_intertwines m w

theorem binary_intertwines (x : Model 0) :
    quotientToIdeal * (matrixRepresentation 0 x : Matrix Coordinate Coordinate (CoefficientField 0)) =
      (matrixRepresentation 0 x : Matrix Coordinate Coordinate (CoefficientField 0)) *
        quotientToIdeal := by
  have hfix := (mem_fixedSubgroup_iff 0 x.val).mp x.property
  change exceptionalEndomorphism 0 x.val = x.val at hfix
  have h := exceptional_intertwines 0 (toSplitGroup 0 x)
  rw [toSplitGroup_apply, hfix] at h
  simpa only [matrixRepresentation_apply] using h

variable {F : Type*} [Field F] [IsAlgClosed F]
theorem pointMatrix_splitEmbedding {m : ℕ} (f : CoefficientField m →+* F)
    (x : SplitGroup m) :
    pointMatrix (splitEmbedding f x) = Units.map f.mapMatrix.toMonoidHom x.val := by
  change ambientUnitsEquiv.symm ((F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
    (splitEmbedding f x)) = _
  rw [inclusion_splitEmbedding]
  exact ambientUnitsEquiv.symm_apply_apply _

theorem quotientToIdeal_map {K L : Type*} [Semiring K] [Semiring L] (f : K →+* L) :
    (quotientToIdeal (K := K)).map f = quotientToIdeal (K := L) := by
  classical
  ext i j
  simp only [Matrix.map_apply, quotientToIdeal_apply]
  split_ifs <;> simp only [map_zero, map_one]

theorem embedded_binary_intertwines (f : CoefficientField 0 →+* F) (x : Model 0) :
    quotientToIdeal * (pointMatrix (splitEmbedding f (toSplitGroup 0 x)) :
      Matrix Coordinate Coordinate F) =
    (pointMatrix (splitEmbedding f (toSplitGroup 0 x)) :
      Matrix Coordinate Coordinate F) * quotientToIdeal := by
  have hm : (pointMatrix (splitEmbedding f (toSplitGroup 0 x)) :
      Matrix Coordinate Coordinate F) =
      (matrixRepresentation 0 x : Matrix Coordinate Coordinate (CoefficientField 0)).map f := by
    rw [pointMatrix_splitEmbedding, Units.coe_map, matrixRepresentation_apply,
      toSplitGroup_apply]
    change f.mapMatrix (x.val.val : Matrix Coordinate Coordinate (CoefficientField 0)) = _
    exact RingHom.mapMatrix_apply f _
  rw [hm]
  have h := congrArg f.mapMatrix (binary_intertwines x)
  simpa only [map_mul, RingHom.mapMatrix_apply, quotientToIdeal_map] using h

theorem embedded_binary_short_long_entry (f : CoefficientField 0 →+* F) (x : Model 0)
    (i j : Coordinate) (hi : IsShortCoordinate i) (hj : IsShortCoordinate j) :
    (pointMatrix (splitEmbedding f (toSplitGroup 0 x)) : Matrix Coordinate Coordinate F) i j =
    (pointMatrix (splitEmbedding f (toSplitGroup 0 x)) : Matrix Coordinate Coordinate F)
      (coordinatePermutation i) (coordinatePermutation j) := by
  have hn : ¬ IsShortCoordinate (coordinatePermutation j) := by
    simpa only [coordinatePermutation_short_iff, not_not] using hj
  have h := congrArg (fun A : Matrix Coordinate Coordinate F => A i (coordinatePermutation j))
    (embedded_binary_intertwines f x)
  simpa only [quotientToIdeal_mul, mul_quotientToIdeal, if_neg hn,
    if_pos hi, coordinatePermutation_involutive j] using h.symm

open scoped Classical
noncomputable section

/-- Short-root coordinates together with the two short Cartan coordinates. -/
abbrev ShortIndex := {i : Coordinate // IsShortCoordinate i}

instance shortIndexFintype : Fintype ShortIndex := Subtype.fintype IsShortCoordinate

/-- Matrix of the action on the short ideal. -/
@[expose] def shortBlock (A : Matrix Coordinate Coordinate F) : Matrix ShortIndex ShortIndex F :=
  A.submatrix Subtype.val Subtype.val

/-- Matrix of the quotient action, indexed by dual short coordinates.
The long coordinate span is not asserted to be invariant. -/
@[expose] def quotientBlock (A : Matrix Coordinate Coordinate F) : Matrix ShortIndex ShortIndex F :=
  A.submatrix (fun i => coordinatePermutation i.val) (fun i => coordinatePermutation i.val)

omit [IsAlgClosed F] in
private theorem sum_short (a : Coordinate → F) (ha : ∀ i, ¬IsShortCoordinate i → a i = 0) :
    ∑ i : Coordinate, a i = ∑ i : ShortIndex, a i.val := by
  have h := Fintype.sum_subtype_add_sum_subtype IsShortCoordinate a
  have hz : (∑ i : {i : Coordinate // ¬IsShortCoordinate i}, a i.val) = 0 :=
    Finset.sum_eq_zero (fun i _ => ha i.val i.property)
  rw [hz, add_zero] at h
  exact h.symm

omit [IsAlgClosed F] in
private theorem shortBlock_mul (A B : Matrix Coordinate Coordinate F)
    (hB : ∀ i j, ¬IsShortCoordinate i → IsShortCoordinate j → B i j = 0) :
    shortBlock (A * B) = shortBlock A * shortBlock B := by
  ext i j
  change (∑ k : Coordinate, A i.val k * B k j.val) =
    ∑ k : ShortIndex, A i.val k.val * B k.val j.val
  exact sum_short _ (fun k hk => by rw [hB k j.val hk j.property, mul_zero])

omit [IsAlgClosed F] in
private theorem quotientBlock_mul (A B : Matrix Coordinate Coordinate F)
    (hA : ∀ i j, ¬IsShortCoordinate i → IsShortCoordinate j → A i j = 0) :
    quotientBlock (A * B) = quotientBlock A * quotientBlock B := by
  ext i j
  change (∑ k : Coordinate, A (coordinatePermutation i.val) k *
      B k (coordinatePermutation j.val)) =
    ∑ k : ShortIndex, A (coordinatePermutation i.val) (coordinatePermutation k.val) *
      B (coordinatePermutation k.val) (coordinatePermutation j.val)
  rw [← Equiv.sum_comp coordinatePermutation]
  apply sum_short
  intro k hk
  rw [hA _ _ ((coordinatePermutation_short_iff _).not.mpr (not_not.mpr i.property))
    ((coordinatePermutation_short_iff _).mpr hk), zero_mul]

variable [CharP F 2]

theorem pointMatrix_lowerLeft_zero (c : Steinberg.PointGroup F) (i j : Coordinate)
    (hi : ¬IsShortCoordinate i) (hj : IsShortCoordinate j) :
    (pointMatrix c : Matrix Coordinate Coordinate F) i j = 0 := by
  have h := matrixGroup_preserves_short (pointMatrix c) (pointMatrix_mem c)
    (Pi.single j 1) (Faithfulness.RestrictedAdjoint.shortSupported_single j hj) i hi
  simpa [Matrix.mulVec_single] using h

/-- The genuine action on the short ideal in its coordinate basis. -/
@[expose] def shortAction : Steinberg.PointGroup F →* (Matrix ShortIndex ShortIndex F) where
  toFun c := shortBlock (pointMatrix c : Matrix Coordinate Coordinate F)
  map_one' := by
    simp only [map_one, Units.val_one, shortBlock]
    exact Matrix.submatrix_one _ Subtype.val_injective
  map_mul' c d := by
    simp only [map_mul, Units.val_mul]
    exact shortBlock_mul _ _ (pointMatrix_lowerLeft_zero d)

/-- The genuine action on the quotient by the short ideal. -/
@[expose] def quotientAction : Steinberg.PointGroup F →* (Matrix ShortIndex ShortIndex F) where
  toFun c := quotientBlock (pointMatrix c : Matrix Coordinate Coordinate F)
  map_one' := by
    simp only [map_one, Units.val_one, quotientBlock]
    exact Matrix.submatrix_one _ (coordinatePermutation.injective.comp Subtype.val_injective)
  map_mul' c d := by
    simp only [map_mul, Units.val_mul]
    exact quotientBlock_mul _ _ (pointMatrix_lowerLeft_zero c)

/-- Projection onto quotient coordinates after the fixed root duality. -/
@[expose] def quotientProjection : (Coordinate → F) →ₗ[F] (ShortIndex → F) where
  toFun v i := v (coordinatePermutation i.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsAlgClosed F] [CharP F 2] in
/-- The projection kills exactly the actual short-coordinate ideal. -/
theorem quotientProjection_eq_zero_iff (v : Coordinate → F) :
    quotientProjection v = 0 ↔ Faithfulness.RestrictedAdjoint.ShortSupported v := by
  constructor
  · intro h i hi
    have hs : IsShortCoordinate (coordinatePermutation i) :=
      (coordinatePermutation_short_iff i).mpr hi
    have he := congrFun h ⟨coordinatePermutation i, hs⟩
    change v (coordinatePermutation (coordinatePermutation i)) = 0 at he
    simpa only [coordinatePermutation_involutive i] using he
  · intro h
    funext i
    exact h _ ((coordinatePermutation_short_iff _).not.mpr (not_not.mpr i.property))

/-- The long block is the action induced on the quotient projection. -/
theorem quotientAction_projection (c : Steinberg.PointGroup F) (v : Coordinate → F) :
    quotientProjection ((pointMatrix c : Matrix Coordinate Coordinate F) *ᵥ v) =
      quotientAction c *ᵥ quotientProjection v := by
  funext i
  change (∑ k : Coordinate, (pointMatrix c : Matrix Coordinate Coordinate F)
      (coordinatePermutation i.val) k * v k) =
    ∑ k : ShortIndex, (pointMatrix c : Matrix Coordinate Coordinate F)
      (coordinatePermutation i.val) (coordinatePermutation k.val) *
        v (coordinatePermutation k.val)
  rw [← Equiv.sum_comp coordinatePermutation]
  apply sum_short
  intro k hk
  rw [pointMatrix_lowerLeft_zero c _ _
    ((coordinatePermutation_short_iff _).not.mpr (not_not.mpr i.property))
    ((coordinatePermutation_short_iff _).mpr hk), zero_mul]

omit [CharP F 2] in
/-- The positive coroot product acts by the inverse parameters of the
geometric split-torus convention. -/
theorem pointMatrix_corootTorusElement (t : Fin 4 → Fˣ) :
    pointMatrix (corootTorusElement t) = F4Chevalley.torusElement (t⁻¹) := by
  rw [← positiveTorusHom_eq]
  change ambientUnitsEquiv.symm
    ((F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
      (F4Chevalley.splitTorusMorphism.onPoints
        ((diagonalPointEquiv (F := F)).symm (t⁻¹)))) = _
  rw [F4Chevalley.splitTorusMorphism_inclusion_apply, F4Chevalley.torusAmbientMorphism_matrix]
  change ambientUnitsEquiv.symm (ambientUnitsEquiv (F4Chevalley.torusElement
    (diagonalPointEquiv ((diagonalPointEquiv (F := F)).symm (t⁻¹))))) = _
  rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

omit [IsAlgClosed F] [CharP F 2] in
/-- Every quotient-coordinate vector has an ambient lift. -/
theorem quotientProjection_surjective :
    Function.Surjective (quotientProjection (F := F)) := by
  intro v
  refine ⟨fun i => if h : IsShortCoordinate (coordinatePermutation i) then
    v ⟨coordinatePermutation i, h⟩ else 0, ?_⟩
  funext i
  change (if h : IsShortCoordinate (coordinatePermutation (coordinatePermutation i.val)) then
    v ⟨coordinatePermutation (coordinatePermutation i.val), h⟩ else 0) = v i
  simp only [coordinatePermutation_involutive i.val, dif_pos i.property]

omit [CharP F 2] in
/-- Positive-coroot diagonal entries on the actual Cartan-plus-root lattice. -/
theorem pointMatrix_coroot_diagonal (t : Fin 4 → Fˣ) :
    (pointMatrix (corootTorusElement t) : Matrix Coordinate Coordinate F) =
      Matrix.diagonal (fun i => (corootCharacter t (F4Chevalley.basisWeight i) : F)) := by
  rw [pointMatrix_corootTorusElement]
  change Matrix.diagonal _ = _
  congr 1
  funext i
  have h := F4Chevalley.basisTorusUnit_formula (t⁻¹) i
  simp only [Pi.inv_apply, inv_zpow, inv_inv, zpow_neg, Fin.prod_univ_four] at h
  exact congrArg Units.val h

theorem embedded_actions_eq (f : CoefficientField 0 →+* F) (x : Model 0) :
    shortAction (splitEmbedding f (toSplitGroup 0 x)) =
      quotientAction (splitEmbedding f (toSplitGroup 0 x)) := by
  ext i j
  exact embedded_binary_short_long_entry f x i.val j.val i.property j.property

omit [IsAlgClosed F] [CharP F 2] in
private theorem rank_mul_units {n : Type*} [Fintype n] [DecidableEq n]
    (u v : (Matrix n n F)ˣ) (A : Matrix n n F) :
    ((u : Matrix n n F) * A * (v : Matrix n n F)).rank = A.rank := by
  apply Nat.le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have h : A = (↑u⁻¹ : Matrix n n F) * ((u : Matrix n n F) * A * (v : Matrix n n F)) * (↑v⁻¹ : Matrix n n F) := by
      symm
      calc
        (↑u⁻¹ : Matrix n n F) * ((u : Matrix n n F) * A * (v : Matrix n n F)) *
            (↑v⁻¹ : Matrix n n F) =
            ((↑u⁻¹ : Matrix n n F) * (u : Matrix n n F)) * A *
              ((v : Matrix n n F) * (↑v⁻¹ : Matrix n n F)) := by simp only [Matrix.mul_assoc]
        _ = A := by simp
    calc
      A.rank = ((↑u⁻¹ : Matrix n n F) * ((u : Matrix n n F) * A * (v : Matrix n n F)) * (↑v⁻¹ : Matrix n n F)).rank :=
        congrArg Matrix.rank h
      _ ≤ ((u : Matrix n n F) * A * (v : Matrix n n F)).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

omit [IsAlgClosed F] [CharP F 2] in
private theorem displacement_rank_conjugate {G n : Type*} [Group G] [Fintype n]
    [DecidableEq n] (ρ : G →* Matrix n n F) (c g : G) :
    (ρ (c * g * c⁻¹) - 1).rank = (ρ g - 1).rank := by
  let u : (Matrix n n F)ˣ := Units.map ρ (toUnits c)
  have hu : (u : Matrix n n F) = ρ c := rfl
  have hi : (u⁻¹ : (Matrix n n F)ˣ).val = ρ c⁻¹ := rfl
  have he : ρ (c * g * c⁻¹) - 1 =
      (u : Matrix n n F) * (ρ g - 1) * (↑u⁻¹ : Matrix n n F) := by
    rw [hu, hi, mul_sub, sub_mul, Matrix.mul_one]
    simp only [← map_mul, mul_inv_cancel, map_one]
  rw [he]
  exact rank_mul_units u u⁻¹ _

/-- Conjugacy carries equality of the binary Ree ideal and quotient ranks to
an arbitrary torus presentation. -/
theorem torus_displacement_ranks_eq
    (f : CoefficientField 0 →+* F) (x : Model 0)
    (c : Steinberg.PointGroup F) (t : Fin 4 → Fˣ)
    (he : splitEmbedding f (toSplitGroup 0 x) = c * corootTorusElement t * c⁻¹) :
    (shortAction (corootTorusElement t) - 1).rank =
      (quotientAction (corootTorusElement t) - 1).rank := by
  have h := congrArg (fun A : Matrix ShortIndex ShortIndex F => (A - 1).rank)
    (embedded_actions_eq f x)
  rw [he, displacement_rank_conjugate, displacement_rank_conjugate] at h
  exact h

end
end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance
