module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.Frobenius
public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Morphism.Operations

/-!
# The literal octonion automorphism group as an affine algebraic group

Inside GL₈, preservation of each coordinate of each octonion product is a
polynomial equation. Its common zero locus is therefore a closed subgroup,
whose points are multiplicatively equivalent to `Atlas.G2.Model K`. The
centralizer of an actual model element is the closed equalizer of left and
right translation; its point equivalence identifies it with the ordinary
subgroup centralizer, including all nonregular elements.

The coordinates are the eight-by-eight matrix entries and the inverse
determinant. The comparison lemmas retain these coordinates so that literal
coefficient Frobenius can subsequently be realized as a regular morphism.
No connectedness, reductivity or simply connected structure is asserted here.

Source: GLS III, Sections 2.1 and 2.8 (`refs/KGroup/GLS3/chapter2.tex`), and
Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 8.5 and 12.5. The octonion table
comes from the licensed ATLAS port; see `LICENSES/ATLAS.txt`.
-/

@[expose] public section

open Theory.AlgebraicGroup Atlas.SplitOctonion
open scoped BigOperators
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [IsAlgClosed K]

def linearPointEquiv : Variety.Point (glVariety 8 : Variety K) ≃*
    (Carrier K ≃ₗ[K] Carrier K) :=
  (translationGLPointMulEquiv 8).trans
    ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8))).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Carrier K)))

theorem linearPointEquiv_apply (p : Variety.Point (glVariety 8 : Variety K))
    (x : Carrier K) (i : Fin 8) :
    linearPointEquiv p x i = ∑ j, p.val (Sum.inl (i,j)) * x j := by
  change ((Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8))
    (glPointEquiv 8 p)).toLinearEquiv x) i = _
  rw [Matrix.GeneralLinearGroup.toLin'_apply]
  simp [Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    Matrix.mulVec, dotProduct, Pi.single_apply, glPointEquiv, glMatrixOfPoint]

def modelSubgroup : Subgroup (Variety.Point (glVariety 8 : Variety K)) :=
  (Atlas.Algebra.multiplicativeLinearAut (R := K) (@mul K _)).comap
    linearPointEquiv.toMonoidHom

def actionPolynomial (x : Carrier K) (i : Fin 8) :
    MvPolynomial (glCoordinates 8) K :=
  ∑ j, MvPolynomial.X (Sum.inl (i,j)) * MvPolynomial.C (x j)

theorem eval_actionPolynomial (p : Variety.Point (glVariety 8 : Variety K))
    (x : Carrier K) (i : Fin 8) :
    evalPolynomial p.val (actionPolynomial x i) = linearPointEquiv p x i := by
  rw [linearPointEquiv_apply]
  simp [actionPolynomial, evalPolynomial]

def multiplicationEquation (x y : Carrier K) (i : Fin 8) :
    MvPolynomial (glCoordinates 8) K :=
  actionPolynomial (mul x y) i - mul (actionPolynomial x) (actionPolynomial y) i

theorem eval_multiplicationEquation (p : Variety.Point (glVariety 8 : Variety K))
    (x y : Carrier K) (i : Fin 8) :
    evalPolynomial p.val (multiplicationEquation x y i) =
      linearPointEquiv p (mul x y) i -
        mul (linearPointEquiv p x) (linearPointEquiv p y) i := by
  fin_cases i <;> simp [multiplicationEquation, mul, evalPolynomial,
    actionPolynomial, linearPointEquiv_apply]

theorem modelSubgroup_isClosed : IsZariskiClosed (glVariety 8 : Variety K)
    (modelSubgroup (K := K) : Set (Variety.Point (glVariety 8 : Variety K))) := by
  refine ⟨Set.range (fun t : Carrier K × Carrier K × Fin 8 =>
    multiplicationEquation t.1 t.2.1 t.2.2), ?_⟩
  ext p
  constructor
  · intro hp f hf
    obtain ⟨⟨x,y,i⟩,rfl⟩ := hf
    rw [eval_multiplicationEquation]
    exact sub_eq_zero.mpr (congrFun (hp x y) i)
  · intro hp x y
    ext i
    exact sub_eq_zero.mp ((eval_multiplicationEquation p x y i).symm.trans
      (hp _ ⟨(x,y,i),rfl⟩))

def modelClosedSubgroup : ClosedSubgroup (glVariety 8 : Variety K) :=
  ClosedSubgroup.ofSubgroup modelSubgroup modelSubgroup_isClosed

abbrev modelVariety (K : Type*) [Field K] [IsAlgClosed K] : Variety K :=
  (modelClosedSubgroup (K := K)).carrierVariety

instance : AlgebraicGroup (modelVariety K) :=
  modelClosedSubgroup.carrierAlgebraicGroup

def modelPointEquiv : Variety.Point (modelVariety K) ≃* Model K where
  toFun p := ⟨linearPointEquiv ((modelClosedSubgroup.pointEquiv p).val),
    (modelClosedSubgroup.pointEquiv p).property⟩
  invFun g := modelClosedSubgroup.pointEquiv.symm
    ⟨linearPointEquiv.symm g.val, by
      change linearPointEquiv (linearPointEquiv.symm g.val) ∈
        Atlas.Algebra.multiplicativeLinearAut (R := K) (@mul K _)
      rw [MulEquiv.apply_symm_apply]
      exact g.property⟩
  left_inv p := by
    apply modelClosedSubgroup.pointEquiv.injective
    apply Subtype.ext
    exact linearPointEquiv.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    exact linearPointEquiv.apply_symm_apply _
  map_mul' p q := by
    apply Subtype.ext
    exact linearPointEquiv.map_mul _ _

theorem modelPointEquiv_entry (p : Variety.Point (modelVariety K)) (i j : Fin 8) :
    (FieldExtension.coordinateMatrix (modelPointEquiv p) : Matrix (Fin 8) (Fin 8) K) i j =
      p.val (Sum.inl (i,j)) := by
  rw [coordinateMatrix_entry]
  change linearPointEquiv (modelClosedSubgroup.pointEquiv p).val (basisVector j) i = _
  rw [linearPointEquiv_apply]
  simp only [basisVector, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

theorem modelPointEquiv_scalar (p : Variety.Point (modelVariety K)) :
    p.val (Sum.inr PUnit.unit) =
      (FieldExtension.coordinateMatrix (modelPointEquiv p) :
        Matrix (Fin 8) (Fin 8) K).det⁻¹ := by
  have h := glScalarOfPoint_eq_inv_det 8 (modelClosedSubgroup.pointEquiv p).val
  change p.val (Sum.inr PUnit.unit) = _ at h
  rw [h]
  congr 2
  ext i j
  exact (modelPointEquiv_entry p i j).symm

def centralizerClosedSubgroup (g : Model K) : ClosedSubgroup (modelVariety K) :=
  ClosedSubgroup.ofSubgroup (Subgroup.centralizer {modelPointEquiv.symm g}) (by
    have h := Variety.Morphism.isZariskiClosed_equalizer
      (leftMulMorphism (modelVariety K) (modelPointEquiv.symm g))
      (rightMulMorphism (modelVariety K) (modelPointEquiv.symm g))
    convert h using 1
    ext x
    change x ∈ Subgroup.centralizer {modelPointEquiv.symm g} ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm)

abbrev centralizerVariety (g : Model K) : Variety K :=
  (centralizerClosedSubgroup g).carrierVariety

instance (g : Model K) : AlgebraicGroup (centralizerVariety g) :=
  (centralizerClosedSubgroup g).carrierAlgebraicGroup

def centralizerPointEquiv (g : Model K) : Variety.Point (centralizerVariety g) ≃*
    Subgroup.centralizer ({g} : Set (Model K)) where
  toFun p := ⟨modelPointEquiv ((centralizerClosedSubgroup g).pointEquiv p).val, by
    have h := ((centralizerClosedSubgroup g).pointEquiv p).property
    change _ ∈ Subgroup.centralizer {modelPointEquiv.symm g} at h
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg modelPointEquiv h⟩
  invFun z := (centralizerClosedSubgroup g).pointEquiv.symm
    ⟨modelPointEquiv.symm z.val, by
      change modelPointEquiv.symm z.val ∈ Subgroup.centralizer {modelPointEquiv.symm g}
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply modelPointEquiv.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        Subgroup.mem_centralizer_singleton_iff.mp z.property⟩
  left_inv p := by
    apply (centralizerClosedSubgroup g).pointEquiv.injective
    apply Subtype.ext
    exact modelPointEquiv.symm_apply_apply _
  right_inv z := by
    apply Subtype.ext
    exact modelPointEquiv.apply_symm_apply _
  map_mul' p q := by
    apply Subtype.ext
    exact modelPointEquiv.map_mul _ _

theorem centralizerPointEquiv_entry (g : Model K)
    (p : Variety.Point (centralizerVariety g)) (i j : Fin 8) :
    (FieldExtension.coordinateMatrix (centralizerPointEquiv g p).val :
      Matrix (Fin 8) (Fin 8) K) i j = p.val (Sum.inl (i,j)) :=
  modelPointEquiv_entry ((centralizerClosedSubgroup g).pointEquiv p).val i j

theorem centralizerPointEquiv_scalar (g : Model K)
    (p : Variety.Point (centralizerVariety g)) :
    p.val (Sum.inr PUnit.unit) =
      (FieldExtension.coordinateMatrix (centralizerPointEquiv g p).val :
        Matrix (Fin 8) (Fin 8) K).det⁻¹ :=
  modelPointEquiv_scalar ((centralizerClosedSubgroup g).pointEquiv p).val

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
