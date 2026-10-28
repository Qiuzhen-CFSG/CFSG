module
public import Theory.Representation.HigmanSims.Twenty.Comparison.Certificates
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The marked permutation-to-matrix comparison for HS

The certified 21 independent rows identify their coefficient space with a
subspace of the degree-100 permutation module. Pullback by each generator
preserves this subspace; finite-group generation extends preservation to the
whole literal HS carrier. The last row is the all-one vector and is fixed.

We quotient by its line and dualize the resulting pullback anti-action.
Evaluation on the twenty remaining rows identifies this dual with the standard
20-dimensional binary vector space. The checked row identities give exactly
the published matrices A and B, without inversion or transpose. Generation
then puts the image in the specified matrix subgroup.

`markedComparison` and `nonempty_markedComparison` require neither simplicity
nor an order calculation. The existing `MarkedComparison.equiv` can use the
simplicity inherited by a source consumer to obtain the carrier isomorphism.
`liftSpaceQuotientEquiv` identifies the coordinate quotient with the literal
quotient of the subspace of the permutation module by its all-one line.

Source: ATLAS HSG1-p100B0 and HSG1-f2r20B0. See `Twenty/source/README.md`
for the preserved source files and the untrusted discovery certificate;
`Comparison.Certificates` checks every identity used here.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.Twenty.Comparison
open scoped BigOperators Matrix
noncomputable section

abbrev Coefficients := Fin 21 → ZMod 2
abbrev PermutationSpace := Fin 100 → ZMod 2
abbrev LiftSpace := LinearMap.range lifts.vecMulLinear

def pull (g : Equiv.Perm (Fin 100)) : Module.End (ZMod 2) PermutationSpace where
  toFun v := v ∘ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_lift (g : Equiv.Perm (Fin 100))
    (M : Matrix (Fin 21) (Fin 21) (ZMod 2))
    (h : (fun i j => lifts i (g j)) = M * lifts) (v : Coefficients) :
    pull g (lifts.vecMulLinear v) = lifts.vecMulLinear (v ᵥ* M) := by
  rw [Matrix.vecMulLinear_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, ← h]
  rfl

private def preserving : Submonoid (Equiv.Perm (Fin 100)) where
  carrier := {g | ∀ v ∈ LinearMap.range lifts.vecMulLinear,
    pull g v ∈ LinearMap.range lifts.vecMulLinear}
  one_mem' := fun _ hv => hv
  mul_mem' := by
    intro g h hg hh v hv
    exact hh (pull g v) (hg v hv)

theorem pull_mem (g : HS.Carrier) (v : LiftSpace) :
    pull g.val v.val ∈ LinearMap.range lifts.vecMulLinear := by
  have hgen : Submonoid.closure {HS.generatorA, HS.generatorB} ≤ preserving := by
    rw [Submonoid.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · intro v hv
      obtain ⟨x, rfl⟩ := hv
      exact ⟨x ᵥ* extendedA, (pull_lift _ _ pull_lifts_a x).symm⟩
    · have he := Set.mem_singleton_iff.mp hg
      subst g
      intro v hv
      obtain ⟨x, rfl⟩ := hv
      exact ⟨x ᵥ* extendedB, (pull_lift _ _ pull_lifts_b x).symm⟩
  have hg : g.val ∈ Submonoid.closure {HS.generatorA, HS.generatorB} := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact g.property
  exact hgen hg v v.property

def liftEquiv : Coefficients ≃ₗ[ZMod 2] LiftSpace :=
  LinearEquiv.ofInjective lifts.vecMulLinear lifts_injective

def pullRange (g : HS.Carrier) : Module.End (ZMod 2) LiftSpace where
  toFun v := ⟨pull g.val v.val, pull_mem g v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pullCoefficients (g : HS.Carrier) : Module.End (ZMod 2) Coefficients :=
  liftEquiv.symm.toLinearMap.comp ((pullRange g).comp liftEquiv.toLinearMap)

theorem lift_pull (g : HS.Carrier) (v : Coefficients) :
    lifts.vecMulLinear (pullCoefficients g v) = pull g.val (lifts.vecMulLinear v) := by
  exact LinearEquiv.ofInjective_symm_apply _ (h := lifts_injective) _

theorem pullCoefficients_one : pullCoefficients 1 = 1 := by
  apply LinearMap.ext
  intro v
  apply lifts_injective
  rw [lift_pull]
  rfl

theorem pullCoefficients_mul (g h : HS.Carrier) :
    pullCoefficients (g * h) = pullCoefficients h * pullCoefficients g := by
  apply LinearMap.ext
  intro v
  apply lifts_injective
  simp only [Module.End.mul_apply, lift_pull]
  rfl

def lastVector : Coefficients := Pi.single (Fin.last 20) 1

theorem lift_last : lifts.vecMulLinear lastVector = fun _ => 1 := by
  change Pi.single (Fin.last 20) 1 ᵥ* lifts = _
  rw [Matrix.single_one_vecMul, Matrix.row_apply']
  exact lifts_last

theorem pullCoefficients_last (g : HS.Carrier) :
    pullCoefficients g lastVector = lastVector := by
  apply lifts_injective
  rw [lift_pull, lift_last]
  rfl

def projection : Coefficients →ₗ[ZMod 2] Vector where
  toFun v i := v i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem projection_surjective : Function.Surjective projection := by
  intro v
  exact ⟨Fin.snoc v 0, by ext i; simp [projection]⟩

def constantLine : Submodule (ZMod 2) Coefficients := LinearMap.ker projection

theorem mem_constantLine (v : Coefficients) :
    v ∈ constantLine ↔ v = v (Fin.last 20) • lastVector := by
  constructor
  · intro hv
    have hz : projection v = 0 := hv
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [lastVector]
    · change v j.castSucc = v (Fin.last 20) * lastVector j.castSucc
      rw [lastVector, Pi.single_eq_of_ne (Fin.castSucc_ne_last j), mul_zero]
      exact congrFun hz j
  · intro hv
    rw [hv]
    change projection (_ • lastVector) = 0
    ext i
    change v (Fin.last 20) * lastVector i.castSucc = 0
    rw [lastVector, Pi.single_eq_of_ne (Fin.castSucc_ne_last i), mul_zero]

theorem constantLine_eq_span : constantLine = Submodule.span (ZMod 2) {lastVector} := by
  ext v
  rw [mem_constantLine, Submodule.mem_span_singleton]
  constructor
  · exact fun h => ⟨v (Fin.last 20), h.symm⟩
  · rintro ⟨c, rfl⟩
    simp [lastVector]

theorem pull_constantLine (g : HS.Carrier) :
    constantLine ≤ constantLine.comap (pullCoefficients g) := by
  intro v hv
  rw [mem_constantLine] at hv
  change pullCoefficients g v ∈ constantLine
  rw [hv, map_smul, pullCoefficients_last]
  apply (mem_constantLine _).mpr
  simp [lastVector]

abbrev QuotientSpace := Coefficients ⧸ constantLine

/-- The constant vector inside the actual subspace of the permutation module. -/
def onesVector : LiftSpace := liftEquiv lastVector

theorem onesVector_val : (onesVector : PermutationSpace) = fun _ => 1 := lift_last

def liftConstantLine : Submodule (ZMod 2) LiftSpace :=
  Submodule.span (ZMod 2) {onesVector}

/-- Identify the coordinate quotient with the literal quotient of the lift space
by its all-one line. -/
def liftSpaceQuotientEquiv : QuotientSpace ≃ₗ[ZMod 2] LiftSpace ⧸ liftConstantLine :=
  Submodule.Quotient.equiv constantLine liftConstantLine liftEquiv (by
    rw [constantLine_eq_span, Submodule.map_span, Set.image_singleton]
    rfl)

def quotientEquiv : QuotientSpace ≃ₗ[ZMod 2] Vector :=
  projection.quotKerEquivOfSurjective projection_surjective

def quotientPull (g : HS.Carrier) : Module.End (ZMod 2) QuotientSpace :=
  constantLine.mapQ constantLine (pullCoefficients g) (pull_constantLine g)

theorem quotientPull_mk (g : HS.Carrier) (v : Coefficients) :
    quotientPull g (constantLine.mkQ v) = constantLine.mkQ (pullCoefficients g v) := rfl

theorem quotientPull_one : quotientPull 1 = 1 := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := constantLine.mkQ_surjective q
  rw [quotientPull_mk, pullCoefficients_one]
  rfl

theorem quotientPull_mul (g h : HS.Carrier) :
    quotientPull (g * h) = quotientPull h * quotientPull g := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := constantLine.mkQ_surjective q
  simp only [Module.End.mul_apply, quotientPull_mk, pullCoefficients_mul]

abbrev DualSpace := Module.Dual (ZMod 2) QuotientSpace

def dualAction : Representation (ZMod 2) HS.Carrier DualSpace where
  toFun g := (quotientPull g).dualMap
  map_one' := by rw [quotientPull_one]; rfl
  map_mul' g h := by
    rw [quotientPull_mul]
    rfl

def dualCoordinates : DualSpace ≃ₗ[ZMod 2] Vector :=
  quotientEquiv.symm.dualMap.trans ((Pi.basisFun (ZMod 2) (Fin 20)).constr (ZMod 2)).symm

def quotientRow (i : Fin 20) : QuotientSpace :=
  constantLine.mkQ (Pi.single i.castSucc 1)

theorem quotientEquiv_row (i : Fin 20) :
    quotientEquiv (quotientRow i) = Pi.single i 1 := by
  change projection (Pi.single i.castSucc 1) = _
  ext j
  simp [projection, Pi.single_apply]

theorem dualCoordinates_apply (f : DualSpace) (i : Fin 20) :
    dualCoordinates f i = f (quotientRow i) := by
  change f (quotientEquiv.symm ((Pi.basisFun (ZMod 2) (Fin 20)) i)) = _
  congr 1
  apply quotientEquiv.injective
  rw [quotientEquiv.apply_symm_apply, quotientEquiv_row]
  exact Pi.basisFun_apply _ _ _

def coordinateAction : Representation (ZMod 2) HS.Carrier Vector :=
  (dualCoordinates.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp dualAction


theorem dual_eval_mk (f : DualSpace) (v : Coefficients) :
    f (constantLine.mkQ v) = ∑ i : Fin 20, v i.castSucc * dualCoordinates f i := by
  have hz : constantLine.mkQ (Pi.single (Fin.last 20) 1) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero constantLine).mpr
    apply (mem_constantLine _).mpr
    simp [lastVector]
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Fin.sum_univ_castSucc]
  simp only [hz, map_zero, mul_zero, add_zero, dualCoordinates_apply, quotientRow]

theorem pullCoefficients_of_matrix (g : HS.Carrier)
    (M : Matrix (Fin 21) (Fin 21) (ZMod 2))
    (h : (fun i j => lifts i (g.val j)) = M * lifts) (v : Coefficients) :
    pullCoefficients g v = v ᵥ* M := by
  apply lifts_injective
  rw [lift_pull, pull_lift _ _ h]

theorem coordinateAction_of_matrix (g : HS.Carrier)
    (M : Matrix (Fin 21) (Fin 21) (ZMod 2)) (N : BinaryMatrix)
    (h : (fun i j => lifts i (g.val j)) = M * lifts)
    (ht : M.submatrix Fin.castSucc Fin.castSucc = N) :
    coordinateAction g = Matrix.toLinAlgEquiv' N := by
  apply LinearMap.ext
  intro v
  funext i
  change dualCoordinates ((quotientPull g).dualMap (dualCoordinates.symm v)) i = _
  rw [dualCoordinates_apply]
  change (dualCoordinates.symm v) (quotientPull g (quotientRow i)) = _
  rw [quotientRow, quotientPull_mk, pullCoefficients_of_matrix _ _ h,
    Matrix.single_one_vecMul, dual_eval_mk, dualCoordinates.apply_symm_apply]
  change (∑ j : Fin 20, M i.castSucc j.castSucc * v j) = ∑ j : Fin 20, N i j * v j
  rw [← ht]
  rfl

theorem coordinateAction_a : coordinateAction permutationA = Matrix.toLinAlgEquiv' aMatrix :=
  coordinateAction_of_matrix permutationA extendedA aMatrix pull_lifts_a extendedA_top

theorem coordinateAction_b : coordinateAction permutationB = Matrix.toLinAlgEquiv' bMatrix :=
  coordinateAction_of_matrix permutationB extendedB bMatrix pull_lifts_b extendedB_top

/-- Matrices of the left action on the dual of the twenty-dimensional quotient. -/
def ambientHom : HS.Carrier →* Ambient :=
  MonoidHom.toHomUnits
    (Matrix.toLinAlgEquiv'.symm.toAlgHom.toMonoidHom.comp coordinateAction)

theorem ambientHom_a : ambientHom permutationA = generatorA := by
  apply Units.ext
  change Matrix.toLinAlgEquiv'.symm (coordinateAction permutationA) = aMatrix
  rw [coordinateAction_a, AlgEquiv.symm_apply_apply]

theorem ambientHom_b : ambientHom permutationB = generatorB := by
  apply Units.ext
  change Matrix.toLinAlgEquiv'.symm (coordinateAction permutationB) = bMatrix
  rw [coordinateAction_b, AlgEquiv.symm_apply_apply]

theorem ambientHom_mem (g : HS.Carrier) : ambientHom g ∈ matrixGroup := by
  let K := (matrixGroup.comap ambientHom).map HS.generated.subtype
  have hk : HS.generated ≤ K := by
    change Subgroup.closure {HS.generatorA, HS.generatorB} ≤ K
    rw [Subgroup.closure_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · refine ⟨permutationA, ?_, rfl⟩
      change ambientHom permutationA ∈ matrixGroup
      rw [ambientHom_a]
      exact a.property
    · have he := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨permutationB, ?_, rfl⟩
      change ambientHom permutationB ∈ matrixGroup
      rw [ambientHom_b]
      exact b.property
  obtain ⟨x, hx, hxg⟩ := hk g.property
  have he : x = g := Subtype.ext hxg
  subst x
  exact hx

/-- The marked comparison, constructed without an order or simplicity premise. -/
def markedComparison : MarkedComparison where
  hom :=
    { toFun g := ⟨ambientHom g, ambientHom_mem g⟩
      map_one' := Subtype.ext (map_one ambientHom)
      map_mul' g h := Subtype.ext (map_mul ambientHom g h) }
  map_a := Subtype.ext ambientHom_a
  map_b := Subtype.ext ambientHom_b

theorem nonempty_markedComparison : Nonempty MarkedComparison := ⟨markedComparison⟩

end
end Sporadic.LeechRelated.HS.Twenty.Comparison
