module

public import Theory.SpecificGroups.Monster.Construction.LocalC.TensorSpace
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechFullIsometries
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechVisibleSymmetries

/-!
# The real extension of the full Leech isometry group

Extend the actual rational action `fullIsometryEquiv` by casting its matrix
entries to the reals, with the fixed `coordinateMarking` of `ShortVectors`.
The normalization of `leechVector` is preserved exactly. The lattice vectors
`8e_i` span the real space, so agreement on the lattice proves uniqueness,
the group laws, faithfulness, and preservation of `naturalForm`.

Source: Aschbacher, *Sporadic Groups*, Sections 22–23 and the construction
of `C₂` in Section 27, printed pp. 147–148. The rational extension and the
integral lattice are the attributed ATLAS constructions of Gerald Höhn.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Atlas.Codes Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC

/-- The matrix of the left action in the fixed real coordinates. -/
def realLeechMatrix (g : LeechIsometryGroup) : Matrix (Fin 24) (Fin 24) ℝ :=
  ((LinearMap.toMatrix' (fullIsometryEquiv g).val.toLinearMap).map (Rat.castHom ℝ)).submatrix
    coordinateMarking coordinateMarking

def realLeechMap (g : LeechIsometryGroup) : NaturalSpace →ₗ[ℝ] NaturalSpace :=
  Matrix.mulVecLin (realLeechMatrix g)

theorem realLeechMap_agrees (g : LeechIsometryGroup) (x : leech) :
    realLeechMap g (leechVector x) = leechVector (g.val x) := by
  ext i
  have h := congrFun (LinearMap.toMatrix'_mulVec
    (fullIsometryEquiv g).val.toLinearMap (rationalEmbedding x.val)) (coordinateMarking i)
  change (∑ j, LinearMap.toMatrix' (rationalExtension g.val).toLinearMap
    (coordinateMarking i) j * (x.val j : ℚ)) = (rationalExtension g.val
      (rationalEmbedding x.val)) (coordinateMarking i) at h
  rw [rationalExtension_agrees] at h
  have hr := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at hr
  change (∑ j, realLeechMatrix g i j * leechVector x j) = _
  simp only [realLeechMatrix, Matrix.submatrix_apply, Matrix.map_apply,
    leechVector, ← mul_div_assoc, ← Finset.sum_div]
  change (∑ j : Fin 24, ((LinearMap.toMatrix' (rationalExtension g.val).toLinearMap
    (coordinateMarking i) (coordinateMarking j) : ℚ) : ℝ) * (x.val (coordinateMarking j) : ℝ)) /
      Real.sqrt 8 = _
  rw [coordinateMarking.sum_comp (fun j =>
    ((LinearMap.toMatrix' (rationalExtension g.val).toLinearMap (coordinateMarking i) j : ℚ) : ℝ) *
      (x.val j : ℝ))]
  simpa [rationalEmbedding] using congrArg (fun z : ℝ => z / Real.sqrt 8) hr

def leechAxis (i : Fin 24) : leech :=
  ⟨coordinateVector (coordinateMarking i) 8, coordinate_eight_mem _⟩

theorem leechVector_axis (i : Fin 24) :
    leechVector (leechAxis i) = (8 / Real.sqrt 8) • (Pi.basisFun ℝ (Fin 24)) i := by
  ext j
  by_cases h : i = j
  · subst j; simp [leechVector, leechAxis, coordinateVector, Pi.basisFun_apply]
  · have hij := coordinateMarking.injective.ne h
    simp [leechVector, leechAxis, coordinateVector, Pi.basisFun_apply, h, hij]

theorem leechVector_injective : Function.Injective leechVector := by
  intro x y h
  apply Subtype.ext
  ext j
  obtain ⟨i, rfl⟩ := coordinateMarking.surjective j
  have hi := congrFun h i
  change (_ / Real.sqrt 8) = (_ / Real.sqrt 8) at hi
  have hs : Real.sqrt (8 : ℝ) ≠ 0 := by positivity
  exact_mod_cast (div_left_inj' hs).mp hi

/-- Real linear maps agreeing on the actual lattice agree everywhere. -/
theorem realLeech_ext {M : Type*} [AddCommGroup M] [Module ℝ M]
    {f h : NaturalSpace →ₗ[ℝ] M}
    (he : ∀ x : leech, f (leechVector x) = h (leechVector x)) : f = h := by
  apply (Pi.basisFun ℝ (Fin 24)).ext
  intro i
  have hi := he (leechAxis i)
  rw [leechVector_axis, map_smul, map_smul] at hi
  exact (smul_right_injective _ (by positivity : (8 / Real.sqrt (8 : ℝ)) ≠ 0)) hi

theorem realLeechMap_one : realLeechMap 1 = LinearMap.id := by
  apply realLeech_ext
  intro x
  exact realLeechMap_agrees 1 x

theorem realLeechMap_mul (g h : LeechIsometryGroup) :
    realLeechMap (g * h) = (realLeechMap g).comp (realLeechMap h) := by
  apply realLeech_ext
  intro x
  simp only [LinearMap.comp_apply, realLeechMap_agrees]
  rfl

def realLeechEquiv (g : LeechIsometryGroup) : NaturalSpace ≃ₗ[ℝ] NaturalSpace where
  toFun := fun x => realLeechMap g x
  map_add' := (realLeechMap g).map_add
  map_smul' := (realLeechMap g).map_smul
  invFun := realLeechMap g⁻¹
  left_inv x := by
    have h := congrArg (fun f : NaturalSpace →ₗ[ℝ] NaturalSpace => f x)
      (realLeechMap_mul g⁻¹ g)
    simpa only [inv_mul_cancel, realLeechMap_one, LinearMap.id_apply,
      LinearMap.comp_apply] using h.symm
  right_inv x := by
    have h := congrArg (fun f : NaturalSpace →ₗ[ℝ] NaturalSpace => f x)
      (realLeechMap_mul g g⁻¹)
    simpa only [mul_inv_cancel, realLeechMap_one, LinearMap.id_apply,
      LinearMap.comp_apply] using h.symm

/-- The faithful real representation extending the full lattice action. -/
def realLeechRepresentation : LeechIsometryGroup →* (NaturalSpace ≃ₗ[ℝ] NaturalSpace) where
  toFun := realLeechEquiv
  map_one' := LinearEquiv.toLinearMap_injective realLeechMap_one
  map_mul' g h := LinearEquiv.toLinearMap_injective (realLeechMap_mul g h)

@[simp] theorem realLeechRepresentation_agrees (g : LeechIsometryGroup) (x : leech) :
    realLeechRepresentation g (leechVector x) = leechVector (g.val x) :=
  realLeechMap_agrees g x

theorem realLeechRepresentation_unique (g : LeechIsometryGroup)
    (f : NaturalSpace →ₗ[ℝ] NaturalSpace)
    (hf : ∀ x : leech, f (leechVector x) = leechVector (g.val x)) :
    f = (realLeechRepresentation g).toLinearMap := by
  apply realLeech_ext
  intro x
  exact (hf x).trans (realLeechRepresentation_agrees g x).symm

theorem realLeechRepresentation_faithful : Function.Injective realLeechRepresentation := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply leechVector_injective
  simpa only [realLeechRepresentation_agrees] using
    congrArg (fun f : NaturalSpace ≃ₗ[ℝ] NaturalSpace => f (leechVector x)) he

theorem realLeechRepresentation_form (g : LeechIsometryGroup) (v w : NaturalSpace) :
    naturalForm (realLeechRepresentation g v) (realLeechRepresentation g w) =
      naturalForm v w := by
  have h : naturalForm.comp (realLeechRepresentation g).toLinearMap
      (realLeechRepresentation g).toLinearMap = naturalForm := by
    apply realLeech_ext
    intro x
    apply realLeech_ext
    intro y
    change naturalForm (realLeechRepresentation g (leechVector x))
      (realLeechRepresentation g (leechVector y)) = naturalForm (leechVector x) (leechVector y)
    simp only [realLeechRepresentation_agrees]
    change (∑ i, leechVector (g.val x) i * leechVector (g.val y) i) =
      ∑ i, leechVector x i * leechVector y i
    rw [leechVector_dot, leechVector_dot, g.prop]
  exact congrArg (fun B : LinearMap.BilinForm ℝ NaturalSpace => B v w) h

@[simp] theorem realLeechRepresentation_negation :
    realLeechRepresentation negationIsometry = LinearEquiv.neg ℝ := by
  apply LinearEquiv.toLinearMap_injective
  apply realLeech_ext
  intro x
  change realLeechRepresentation negationIsometry (leechVector x) = -leechVector x
  rw [realLeechRepresentation_agrees, negationIsometry_apply, leechVector_neg]

end Sporadic.Monster.Construction.LocalC
