module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Sections
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Matrix.Block

/-!
# Descent through a certified HS row quotient

The certificate's right inverse makes its concatenated rows independent.
Their span is the actual lifted space, and the kernel rows form an actual
subspace of it. Forward invariance under the two generators extends to the
whole finite carrier. Right multiplication by `T(g⁻¹)` defines a left action,
which restricts to these spaces and descends to their literal quotient.

The quotient is identified with the lift coefficient space. Standard duality
and evaluation at the lifted rows recover the raw target matrices: the kernel
correction terms vanish, and the two inverses cancel. The final `markedAction`
is the carrier-descent consumer of all these constructions.

Source: the exact row-section equations in `Small.Sections`, documented with
ATLAS attribution and permutation conventions in `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Small.Descent
open scoped BigOperators Matrix
open Sporadic.LeechRelated.HS (Carrier)
noncomputable section

private theorem generators_closure :
    Subgroup.closure ({permutationA, permutationB} : Set Carrier) = ⊤ := by
  have he : (Sporadic.LeechRelated.HS.generated.subtype ⁻¹'
      {Sporadic.LeechRelated.HS.generatorA, Sporadic.LeechRelated.HS.generatorB}) =
      ({permutationA, permutationB} : Set Carrier) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff,
      Subgroup.subtype_apply]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl) <;> simp [permutationA, permutationB]
  rw [← he]
  exact Subgroup.closure_preimage_eq_top _

variable (T : Carrier →* Matrix (Fin 190) (Fin 190) (ZMod 2))
  (hA : T permutationA = ambientGenerator 0) (hB : T permutationB = ambientGenerator 1)

include hA hB in
/-- Forward invariance under the two generators extends to the entire finite carrier. -/
theorem rows_invariant {m : Type*} [Fintype m]
    (R : Matrix m (Fin 190) (ZMod 2))
    (B : Fin 2 → Matrix m m (ZMod 2))
    (h : ∀ s, R * ambientGenerator s = B s * R)
    (g : Carrier) :
    ∀ v ∈ LinearMap.range R.vecMulLinear, v ᵥ* T g ∈ LinearMap.range R.vecMulLinear := by
  let P : Submonoid Carrier :=
    { carrier := {g | ∀ v ∈ LinearMap.range R.vecMulLinear,
          v ᵥ* T g ∈ LinearMap.range R.vecMulLinear}
      one_mem' := by intro v hv; simpa using hv
      mul_mem' := by
        intro g k hg hk v hv
        simpa only [map_mul, ← Matrix.vecMul_vecMul] using hk _ (hg v hv) }
  have hs (s : Fin 2) (g : Carrier) (hg : T g = ambientGenerator s) : g ∈ P := by
    rintro v ⟨x, rfl⟩
    refine ⟨x ᵥ* B s, ?_⟩
    simp only [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, hg, h s]
  have hp : Submonoid.closure ({permutationA, permutationB} : Set Carrier) ≤ P := by
    rw [Submonoid.closure_le]
    rintro g (rfl | rfl)
    · exact hs 0 _ hA
    · exact hs 1 _ hB
  apply hp
  rw [← Subgroup.closure_toSubmonoid_of_finite, generators_closure]
  trivial

variable {i : Fin 4} {r : ℕ} (S : SectionCertificate i r)

abbrev Coefficients := (Fin r ⊕ Fin (binaryDegree i)) → ZMod 2
abbrev RowSpace := Fin 190 → ZMod 2

def rows : Matrix (Fin r ⊕ Fin (binaryDegree i)) (Fin 190) (ZMod 2) :=
  sectionRows S.kernelRows S.liftRows

def extended (s : Fin 2) :
    Matrix (Fin r ⊕ Fin (binaryDegree i)) (Fin r ⊕ Fin (binaryDegree i)) (ZMod 2) :=
  Matrix.fromBlocks (S.kernelAction s) 0 (S.corrections s) (targetGenerator i s)

theorem rows_generator (s : Fin 2) :
    rows S * ambientGenerator s = extended S s * rows S := by
  ext k j
  cases k with
  | inl k =>
    change (S.kernelRows * ambientGenerator s) k j =
      ∑ l, extended S s (Sum.inl k) l * rows S l j
    rw [Fintype.sum_sum_type]
    change (S.kernelRows * ambientGenerator s) k j =
      (S.kernelAction s * S.kernelRows) k j + ∑ l, (0 : ZMod 2) * S.liftRows l j
    simp only [zero_mul, Finset.sum_const_zero, add_zero, S.kernel_invariant]
  | inr k =>
    change (S.liftRows * ambientGenerator s) k j =
      ∑ l, extended S s (Sum.inr k) l * rows S l j
    rw [Fintype.sum_sum_type]
    exact congrFun (congrFun (S.lift_action s) k) j

theorem rows_injective : Function.Injective (rows S).vecMulLinear := by
  intro x y h
  have hh := congrArg (fun v => v ᵥ* S.retract) h
  simpa only [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
    rows, S.independent, Matrix.vecMul_one] using hh

abbrev LiftSpace := LinearMap.range (rows S).vecMulLinear
abbrev KernelSpace := LinearMap.range S.kernelRows.vecMulLinear

def liftEquiv : Coefficients (i := i) (r := r) ≃ₗ[ZMod 2] LiftSpace S :=
  LinearEquiv.ofInjective (rows S).vecMulLinear (rows_injective S)

def coefficientProjection : Coefficients (i := i) (r := r) →ₗ[ZMod 2] Vector i where
  toFun v j := v (Sum.inr j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projection : LiftSpace S →ₗ[ZMod 2] Vector i :=
  coefficientProjection.comp (liftEquiv S).symm.toLinearMap

theorem projection_lift (x : Coefficients (i := i) (r := r)) :
    projection S (liftEquiv S x) = coefficientProjection x := by
  simp [projection]

theorem projection_surjective : Function.Surjective (projection S) := by
  intro v
  refine ⟨liftEquiv S (Sum.elim 0 v), ?_⟩
  rw [projection_lift]
  rfl

/-- The kernel row space, viewed inside the space spanned by all certified rows. -/
def kernelInside : Submodule (ZMod 2) (LiftSpace S) := LinearMap.ker (projection S)

theorem lift_kernel (x : Fin r → ZMod 2) :
    (rows S).vecMulLinear (Sum.elim x 0) = S.kernelRows.vecMulLinear x := by
  classical
  ext j
  change (Sum.elim x 0 ᵥ* rows S) j = (x ᵥ* S.kernelRows) j
  rw [Matrix.vecMul, dotProduct, Fintype.sum_sum_type]
  change (∑ k, x k * S.kernelRows k j) + ∑ k, (0 : ZMod 2) * S.liftRows k j = _
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rfl

/-- The kernel rows lie in the actual certified row span. -/
theorem kernel_le_lift : KernelSpace S ≤ LiftSpace S := by
  rintro v ⟨x, rfl⟩
  exact ⟨Sum.elim x 0, lift_kernel S x⟩

theorem mem_kernelInside (v : LiftSpace S) :
    v ∈ kernelInside S ↔ v.val ∈ KernelSpace S := by
  obtain ⟨x, rfl⟩ := (liftEquiv S).surjective v
  change projection S (liftEquiv S x) = 0 ↔ _
  rw [projection_lift]
  constructor
  · intro hx
    have he : x = Sum.elim (fun k => x (Sum.inl k)) 0 := by
      funext k
      cases k with
      | inl k => rfl
      | inr k => exact congrFun hx k
    refine ⟨fun k => x (Sum.inl k), ?_⟩
    change _ = (rows S).vecMulLinear x
    conv_rhs => rw [he, lift_kernel]
  · rintro ⟨y, hy⟩
    have he : Sum.elim y 0 = x := rows_injective S ((lift_kernel S y).trans hy)
    rw [← he]
    rfl

/-- Left row action: inversion corrects the order of right matrix multiplication. -/
def rowAction : Representation (ZMod 2) Carrier RowSpace where
  toFun g :=
    { toFun v := v ᵥ* T g⁻¹
      map_add' x y := Matrix.add_vecMul _ x y
      map_smul' c v := Matrix.smul_vecMul c v _ }
  map_one' := by
    apply LinearMap.ext
    intro v
    change v ᵥ* T (1 : Carrier)⁻¹ = v
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change v ᵥ* T (g * h)⁻¹ = (v ᵥ* T h⁻¹) ᵥ* T g⁻¹
    exact (congrArg (fun a : Carrier => v ᵥ* T a) (mul_inv_rev g h)).trans
      ((congrArg (fun M => v ᵥ* M) (T.map_mul h⁻¹ g⁻¹)).trans
        (Matrix.vecMul_vecMul v (T h⁻¹) (T g⁻¹)).symm)

include hA hB in
theorem lift_invariant (g : Carrier) :
    LiftSpace S ≤ (LiftSpace S).comap (rowAction T g) :=
  rows_invariant T hA hB (rows S) (extended S) (rows_generator S) g⁻¹

def liftAction : Representation (ZMod 2) Carrier (LiftSpace S) :=
  (rowAction T).subrepresentation (LiftSpace S) (lift_invariant T hA hB S)

theorem liftAction_val (g : Carrier) (v : LiftSpace S) :
    (liftAction T hA hB S g v).val = v.val ᵥ* T g⁻¹ := by
  simp only [liftAction, Representation.subrepresentation_apply, LinearMap.restrict_apply]
  rfl

theorem kernel_invariant (g : Carrier) :
    kernelInside S ≤ (kernelInside S).comap (liftAction T hA hB S g) := by
  intro v hv
  change (liftAction T hA hB S g v) ∈ kernelInside S
  rw [mem_kernelInside]
  rw [liftAction_val]
  exact rows_invariant T hA hB S.kernelRows S.kernelAction S.kernel_invariant g⁻¹
    v.val ((mem_kernelInside S v).mp hv)

abbrev QuotientSpace := LiftSpace S ⧸ kernelInside S

def quotientAction : Representation (ZMod 2) Carrier (QuotientSpace S) :=
  (liftAction T hA hB S).quotient (kernelInside S) (kernel_invariant T hA hB S)

def quotientEquiv : QuotientSpace S ≃ₗ[ZMod 2] Vector i :=
  (projection S).quotKerEquivOfSurjective (projection_surjective S)

abbrev DualSpace := Module.Dual (ZMod 2) (QuotientSpace S)

def dualAction : Representation (ZMod 2) Carrier (DualSpace S) :=
  (quotientAction T hA hB S).dual

def dualCoordinates : DualSpace S ≃ₗ[ZMod 2] Vector i :=
  (quotientEquiv S).symm.dualMap.trans
    ((Pi.basisFun (ZMod 2) (Fin (binaryDegree i))).constr (ZMod 2)).symm

def quotientRow (j : Fin (binaryDegree i)) : QuotientSpace S :=
  (kernelInside S).mkQ (liftEquiv S (Pi.single (Sum.inr j) 1))

/-- The distinguished quotient representative is exactly the supplied lifted row. -/
theorem lifted_row_val (j : Fin (binaryDegree i)) :
    (liftEquiv S (Pi.single (Sum.inr j) 1)).val = S.liftRows j := by
  change Pi.single (Sum.inr j) 1 ᵥ* rows S = S.liftRows j
  rw [Matrix.single_one_vecMul]
  rfl

theorem quotientEquiv_row (j : Fin (binaryDegree i)) :
    quotientEquiv S (quotientRow S j) = Pi.single j 1 := by
  change projection S (liftEquiv S _) = _
  rw [projection_lift]
  ext k
  simp [coefficientProjection, Pi.single_apply]

theorem dualCoordinates_apply (f : DualSpace S) (j : Fin (binaryDegree i)) :
    dualCoordinates S f j = f (quotientRow S j) := by
  change f ((quotientEquiv S).symm ((Pi.basisFun (ZMod 2) (Fin (binaryDegree i))) j)) = _
  congr 1
  apply (quotientEquiv S).injective
  rw [LinearEquiv.apply_symm_apply, quotientEquiv_row]
  exact Pi.basisFun_apply _ _ _

def coordinateAction : Representation (ZMod 2) Carrier (Vector i) :=
  ((dualCoordinates S).conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp
    (dualAction T hA hB S)

theorem dual_eval_lift (f : DualSpace S) (x : Coefficients (i := i) (r := r)) :
    f ((kernelInside S).mkQ (liftEquiv S x)) =
      ∑ j, x (Sum.inr j) * dualCoordinates S f j := by
  have hz (k : Fin r) :
      (kernelInside S).mkQ (liftEquiv S (Pi.single (Sum.inl k) 1)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change projection S (liftEquiv S _) = 0
    rw [projection_lift]
    ext j
    simp [coefficientProjection]
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [map_sum, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Fintype.sum_sum_type]
  simp only [hz, map_zero, mul_zero, Finset.sum_const_zero, zero_add,
    dualCoordinates_apply, quotientRow]

theorem liftAction_inverse_lift (s : Fin 2) (g : Carrier)
    (hg : T g = ambientGenerator s) (x : Coefficients (i := i) (r := r)) :
    liftAction T hA hB S g⁻¹ (liftEquiv S x) =
      liftEquiv S (x ᵥ* extended S s) := by
  apply Subtype.ext
  rw [liftAction_val]
  change (x ᵥ* rows S) ᵥ* T (g⁻¹)⁻¹ = (x ᵥ* extended S s) ᵥ* rows S
  have hi : T (g⁻¹)⁻¹ = ambientGenerator s := (congrArg T (inv_inv g)).trans hg
  calc
    (x ᵥ* rows S) ᵥ* T (g⁻¹)⁻¹ = (x ᵥ* rows S) ᵥ* ambientGenerator s := congrArg _ hi
    _ = x ᵥ* (rows S * ambientGenerator s) := Matrix.vecMul_vecMul _ _ _
    _ = x ᵥ* (extended S s * rows S) := congrArg _ (rows_generator S s)
    _ = (x ᵥ* extended S s) ᵥ* rows S := (Matrix.vecMul_vecMul _ _ _).symm

/-- Evaluation on the quotient lifts recovers the raw marked matrix, without a transpose. -/
theorem coordinateAction_generator (s : Fin 2) (g : Carrier)
    (hg : T g = ambientGenerator s) :
    coordinateAction T hA hB S g = Matrix.toLinAlgEquiv' (targetGenerator i s) := by
  apply LinearMap.ext
  intro v
  funext j
  change dualCoordinates S
    (dualAction T hA hB S g ((dualCoordinates S).symm v)) j = _
  rw [dualCoordinates_apply]
  change ((dualCoordinates S).symm v)
    ((kernelInside S).mkQ
      (liftAction T hA hB S g⁻¹ (liftEquiv S (Pi.single (Sum.inr j) 1)))) = _
  rw [liftAction_inverse_lift T hA hB S s g hg, Matrix.single_one_vecMul,
    dual_eval_lift, LinearEquiv.apply_symm_apply]
  rfl

/-- Carrier descent from independent rows and the two literal section equations. -/
def markedAction : MarkedAction i where
  action := coordinateAction T hA hB S
  matrix_a := by
    rw [coordinateAction_generator T hA hB S 0 permutationA hA]
    exact LinearMap.toMatrixAlgEquiv'.apply_symm_apply _
  matrix_b := by
    rw [coordinateAction_generator T hA hB S 1 permutationB hB]
    exact LinearMap.toMatrixAlgEquiv'.apply_symm_apply _

end
end Representation.HigmanSims.LargeModels.Binary.Small.Descent
