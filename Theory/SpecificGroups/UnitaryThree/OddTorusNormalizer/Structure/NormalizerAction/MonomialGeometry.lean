module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Frames
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.PermutationAction
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore.CoordinateAction
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The geometric permutation action of frame monomial matrices

The subgroup is the inverse image of the stabilizer of the three punctured
coordinate axes under the literal change of basis. Nonzero column supports
construct its permutation action, and matrix multiplication gives its precise
conjugation formula on all diagonal matrices. In the special unitary group the
kernel is exactly the published frame torus. No claim about the full normalizer
or surjectivity is assumed here.

Source: GLS4, Chapter 4, Lemma 3.11(c), used in Chapter 2, Lemma 17.4.
The column-support construction extends the one in
`SU3/OddThreeLocal/Monomial/LocalCore/CoordinateAction.lean` to GL, retaining
its geometric specification for the actual conjugation calculation.
-/

@[expose] public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
open scoped Pointwise
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

def frameCoordinateHom (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    J.specialSubgroup →* GL (Fin 3) E :=
  (MulAut.conj P.val⁻¹).toMonoidHom.comp J.specialSubgroup.subtype

def coordinateStabilizer : Subgroup (GL (Fin 3) E) :=
  MulAction.stabilizer _ (OddThreeLocal.Monomial.coordinateVectors (E := E))

def specialFrameMonomial (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Subgroup J.specialSubgroup := (coordinateStabilizer (E := E)).comap (frameCoordinateHom J P)

def projectiveFrameMonomial (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (specialFrameMonomial J P).map J.specialToProjective

theorem coordinate_column_support (x : coordinateStabilizer (E := E)) (i : Fin 3) :
    ∃ j : Fin 3, x.val.val j i ≠ 0 ∧ ∀ k : Fin 3, k ≠ j → x.val.val k i = 0 := by
  have hx : x.val • OddThreeLocal.Monomial.coordinateVectors (E := E) =
      OddThreeLocal.Monomial.coordinateVectors := x.property
  have hi := Set.smul_mem_smul_set (a := x.val)
    (OddThreeLocal.Monomial.single_mem_coordinateVectors i (one_ne_zero : (1 : E) ≠ 0))
  rw [hx] at hi
  change x.val.val *ᵥ Pi.single i 1 ∈ OddThreeLocal.Monomial.coordinateVectors at hi
  simpa only [Matrix.mulVec_single_one, OddThreeLocal.Monomial.coordinateVectors,
    Matrix.col_apply, Set.mem_ofPred_eq] using hi

noncomputable def coordinateIndex (x : coordinateStabilizer (E := E)) (i : Fin 3) : Fin 3 :=
  (coordinate_column_support x i).choose

theorem coordinateIndex_spec (x : coordinateStabilizer (E := E)) (i : Fin 3) :
    x.val.val (coordinateIndex x i) i ≠ 0 ∧
      ∀ k : Fin 3, k ≠ coordinateIndex x i → x.val.val k i = 0 :=
  (coordinate_column_support x i).choose_spec

theorem coordinateIndex_eq_of_ne_zero (x : coordinateStabilizer (E := E)) (i j : Fin 3)
    (h : x.val.val j i ≠ 0) : coordinateIndex x i = j := by
  by_contra hne
  exact h ((coordinateIndex_spec x i).2 j (Ne.symm hne))

theorem coordinateIndex_one (i : Fin 3) :
    coordinateIndex (1 : coordinateStabilizer (E := E)) i = i := by
  apply coordinateIndex_eq_of_ne_zero
  change (1 : Matrix (Fin 3) (Fin 3) E) i i ≠ 0
  simp

theorem coordinate_mul_entry (x y : coordinateStabilizer (E := E)) (k i : Fin 3) :
    (x * y).val.val k i = x.val.val k (coordinateIndex y i) *
      y.val.val (coordinateIndex y i) i := by
  change (x.val.val * y.val.val) k i = _
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single (coordinateIndex y i)
  · intro j _ hj
    rw [(coordinateIndex_spec y i).2 j hj, mul_zero]
  · simp

theorem coordinateIndex_mul (x y : coordinateStabilizer (E := E)) (i : Fin 3) :
    coordinateIndex (x * y) i = coordinateIndex x (coordinateIndex y i) := by
  apply coordinateIndex_eq_of_ne_zero
  rw [coordinate_mul_entry]
  exact mul_ne_zero (coordinateIndex_spec x (coordinateIndex y i)).1
    (coordinateIndex_spec y i).1

noncomputable def coordinatePermutation (x : coordinateStabilizer (E := E)) :
    Equiv.Perm (Fin 3) where
  toFun := coordinateIndex x
  invFun := coordinateIndex x⁻¹
  left_inv i := by rw [← coordinateIndex_mul, inv_mul_cancel, coordinateIndex_one]
  right_inv i := by rw [← coordinateIndex_mul, mul_inv_cancel, coordinateIndex_one]

noncomputable def coordinateAction : coordinateStabilizer (E := E) →* Equiv.Perm (Fin 3) where
  toFun := coordinatePermutation
  map_one' := Equiv.ext coordinateIndex_one
  map_mul' x y := Equiv.ext (coordinateIndex_mul x y)

theorem coordinateAction_eq_one_iff (x : coordinateStabilizer (E := E)) :
    coordinateAction x = 1 ↔ Matrix.IsDiag x.val.val := by
  constructor
  · intro hx i j hij
    have hfix (i : Fin 3) : coordinateIndex x i = i :=
      congrArg (fun p : Equiv.Perm (Fin 3) => p i) hx
    exact (coordinateIndex_spec x j).2 i (by simpa only [hfix] using hij)
  · intro hx
    apply Equiv.ext
    intro i
    change coordinateIndex x i = i
    by_contra hne
    exact (coordinateIndex_spec x i).1 (hx hne)

theorem coordinateAction_conjugate (g : coordinateStabilizer (E := E))
    (a : Fin 3 → Eˣ) :
    g.val * diagonalHom a * g.val⁻¹ = diagonalHom (fun i => a ((coordinateAction g)⁻¹ i)) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Units.ext
  ext i j
  change (g.val.val * Matrix.diagonal (fun i => (a i : E))) i j =
    (Matrix.diagonal (fun i => (a ((coordinateAction g)⁻¹ i) : E)) * g.val.val) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = coordinateAction g j
  · subst i
    simp [mul_comm]
  · have hz := (coordinateIndex_spec g j).2 i h
    simp [hz]

theorem diagonal_range_iff_isDiag (g : GL (Fin 3) E) :
    g ∈ (diagonalHom (E := E)).range ↔ Matrix.IsDiag g.val := by
  constructor
  · rintro ⟨a, rfl⟩
    exact Matrix.isDiag_diagonal _
  · intro h
    have hu : IsUnit (fun i => g.val i i) :=
      by
        apply Matrix.isUnit_diagonal.mp
        change IsUnit (Matrix.diagonal g.val.diag)
        rw [h.diagonal_diag]
        exact g.isUnit
    obtain ⟨a, ha⟩ := hu
    refine ⟨fun i => Units.map (Pi.evalMonoidHom _ i) a, ?_⟩
    apply Units.ext
    change Matrix.diagonal (fun i => a.val i) = g.val
    rw [ha]
    exact h.diagonal_diag

def specialMonomialCoordinates (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    specialFrameMonomial J P →* coordinateStabilizer (E := E) :=
  ((frameCoordinateHom J P).comp (specialFrameMonomial J P).subtype).codRestrict
    coordinateStabilizer (fun x => x.property)

noncomputable def specialMonomialAction (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    specialFrameMonomial J P →* Equiv.Perm (Fin 3) :=
  coordinateAction.comp (specialMonomialCoordinates J P)

theorem specialMonomialAction_ker (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (specialMonomialAction J P).ker =
      (specialFrameTorus J P).subgroupOf (specialFrameMonomial J P) := by
  ext g
  exact (coordinateAction_eq_one_iff _).trans (diagonal_range_iff_isDiag _).symm

theorem specialMonomialAction_action (J : HermitianForm 3 E) (P : OrthogonalFrame J)
    (g : specialFrameMonomial J P) :
    HasSpecialFrameAction J P g.val (specialMonomialAction J P g) := by
  have hpair (y : normOne J × normOne J) :
      frameCoordinateHom J P (specialPairHom J P y) = diagonalHom (pairDiagonal J y) := by
    change P.val⁻¹ * (P.val * diagonalHom (pairDiagonal J y) * P.val⁻¹) * (P.val⁻¹)⁻¹ = _
    simp [mul_assoc]
  have htr (y : normOne J × normOne J) (i : Fin 3) :
      pairDiagonal J y i = (frameTriple J y i).val := by
    fin_cases i <;> rfl
  intro x
  apply (show Function.Injective (frameCoordinateHom J P) from
    (MulAut.conj P.val⁻¹).injective.comp J.specialSubgroup.subtype_injective)
  rw [map_mul, map_mul, map_inv, hpair, hpair]
  have h := coordinateAction_conjugate (specialMonomialCoordinates J P g) (pairDiagonal J x)
  have hp : (fun i => pairDiagonal J x ((specialMonomialAction J P g)⁻¹ i)) =
      pairDiagonal J (permuteFramePair J (specialMonomialAction J P g) x) := by
    funext i
    simp only [htr]
    exact (congrArg Subtype.val (frameTriple_permute J (specialMonomialAction J P g) x i)).symm
  change frameCoordinateHom J P g.val * diagonalHom (pairDiagonal J x) *
    (frameCoordinateHom J P g.val)⁻¹ =
      diagonalHom (fun i => pairDiagonal J x ((specialMonomialAction J P g)⁻¹ i)) at h
  exact h.trans (congrArg diagonalHom hp)


end UnitaryThree.OddTorusNormalizer
