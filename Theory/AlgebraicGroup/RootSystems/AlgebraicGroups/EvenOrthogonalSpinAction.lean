module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitPBW
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Tactic

/-!
# The Clifford Spin action in every characteristic

This module constructs `cliffordSpinAction`, the homomorphism from Mathlib's
Clifford `spinGroup Q` to the quadratic isometry group of `Q`, and proves its
exact Clifford conjugation formula.  The explicit hypothesis
`CliffordAlgebra.ActionForm Q` records a bilinear form with quadratic map `-Q`.
Split hyperbolic spaces have such a triangular form in every characteristic,
including characteristic two.  Consequently the construction supplies the
action fields of `EvenOrthogonalModel` without imposing that two be invertible.

Mathlib's corresponding vector-range theorem assumes that two is invertible.
Its proof uses that hypothesis only to infer that `Q a` is invertible when the
Clifford vector `ι Q a` is invertible.  The action form and
`CliffordAlgebra.changeFormEquiv` identify the Clifford algebra linearly with
the exterior algebra, proving nontriviality and injectivity of `ι`.  Over a
field, the relation `(ι Q a)^2 = Q a` then makes `Q a` nonzero, hence
invertible.  The usual generator-and-closure argument preserves the vector
range.  Restricting Clifford conjugation to that range and transporting across
`ι` gives the linear action; squaring its conjugation formula proves
preservation of `Q`.

The generator calculation follows
`Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup`.  The companion-form
equivalence uses `CliffordAlgebra.changeFormEquiv` from the same library's
contraction construction.
-/

universe u

open CliffordAlgebra MulAction
open scoped Pointwise

namespace CliffordAlgebra

variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V]
variable (Q : QuadraticForm k V)

/-- A bilinear change-of-form datum identifying the Clifford algebra of `Q`
with the exterior algebra.  Split quadratic spaces supply this using their
triangular hyperbolic companion, also in characteristic two. -/
public structure ActionForm where
  bilinear : LinearMap.BilinForm k V
  compatible : bilinear.toQuadraticMap = (0 : QuadraticForm k V) - Q

private noncomputable def exteriorEquivOfActionForm (h : ActionForm Q) :
    CliffordAlgebra Q ≃ₗ[k] ExteriorAlgebra k V :=
  changeFormEquiv h.compatible

/-- Given an action form, the canonical vector map into a Clifford algebra
over a field is injective, with no restriction on the characteristic. -/
public theorem ι_injective_of_actionForm (h : ActionForm Q) :
    Function.Injective (ι Q) := by
  intro x y hxy
  apply (ExteriorAlgebra.ι_leftInverse (R := k) (M := V)).injective
  have hxy' := congrArg (exteriorEquivOfActionForm Q h) hxy
  simpa [exteriorEquivOfActionForm, changeFormEquiv, changeForm_ι] using hxy'

@[instance_reducible] private noncomputable def invertibleQuadraticOfInvertibleι
    (h : ActionForm Q) (a : V) [Invertible (ι Q a)] : Invertible (Q a) := by
  let : Nontrivial (CliffordAlgebra Q) :=
    (exteriorEquivOfActionForm Q h).symm.injective.nontrivial
  apply invertibleOfNonzero
  intro ha
  have hu : IsUnit (ι Q a * ι Q a) :=
    isUnit_mul_self_iff.mpr (isUnit_of_invertible _)
  apply hu.ne_zero
  rw [ι_sq_scalar, ha, map_zero]

end CliffordAlgebra

namespace lipschitzGroup

variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V]
variable {Q : QuadraticForm k V}

/-- Clifford conjugation by a Lipschitz element sends an embedded vector to an
embedded vector over any field.  This is the characteristic-free field version
of `lipschitzGroup.conjAct_smul_ι_mem_range_ι`. -/
public theorem conjAct_smul_ι_mem_range_ι_of_field
    (h : CliffordAlgebra.ActionForm Q)
    {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) (m : V) :
    ConjAct.toConjAct x • CliffordAlgebra.ι Q m ∈
      LinearMap.range (CliffordAlgebra.ι Q) := by
  unfold lipschitzGroup at hx
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  induction hx using Subgroup.closure_induction'' generalizing m with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (CliffordAlgebra.ι Q a) := by rwa [ha]
    let : Invertible (Q a) :=
      CliffordAlgebra.invertibleQuadraticOfInvertibleι Q h a
    simp_rw [← invOf_units x, ← ha, CliffordAlgebra.ι_mul_ι_mul_invOf_ι,
      LinearMap.mem_range_self]
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (CliffordAlgebra.ι Q a) := by rwa [ha]
    let : Invertible (Q a) :=
      CliffordAlgebra.invertibleQuadraticOfInvertibleι Q h a
    simp_rw [← invOf_units x, inv_inv, ← ha,
      CliffordAlgebra.invOf_ι_mul_ι_mul_ι, LinearMap.mem_range_self]
  | one =>
    simp_rw [inv_one, Units.val_one, one_mul, mul_one, LinearMap.mem_range_self]
  | mul y z _ _ hy hz =>
    simp_rw [mul_inv_rev, Units.val_mul]
    suffices ↑y * (↑z * CliffordAlgebra.ι Q m * ↑z⁻¹) * ↑y⁻¹ ∈ _ by
      simpa only [mul_assoc] using this
    obtain ⟨z', hz'⟩ := hz m
    obtain ⟨y', hy'⟩ := hy z'
    simp_rw [← hz', ← hy', LinearMap.mem_range_self]

/-- Clifford conjugation by a Lipschitz element stabilizes the full vector
range over any field. -/
public theorem conjAct_smul_range_ι_of_field
    (h : CliffordAlgebra.ActionForm Q)
    {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) :
    ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q) := by
  suffices ∀ x ∈ lipschitzGroup Q,
      ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) ≤
        LinearMap.range (CliffordAlgebra.ι Q) by
    apply le_antisymm
    · exact this _ hx
    · have h := smul_mono_right (ConjAct.toConjAct x) (this _ (inv_mem hx))
      refine Eq.trans_le ?_ h
      simp only [map_inv, smul_inv_smul]
  intro x hx
  rw [Submodule.pointwise_smul_def, Submodule.map_le_iff_le_comap]
  rintro _ ⟨m, rfl⟩
  exact conjAct_smul_ι_mem_range_ι_of_field h hx m

end lipschitzGroup

namespace spinGroup

variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V]
variable {Q : QuadraticForm k V}

/-- Clifford conjugation by a Spin element sends an embedded vector to an
embedded vector over any field. -/
public theorem conjAct_smul_ι_mem_range_ι_of_field
    (h : CliffordAlgebra.ActionForm Q)
    {x : (CliffordAlgebra Q)ˣ} (hx : (x : CliffordAlgebra Q) ∈ spinGroup Q)
    (m : V) :
    ConjAct.toConjAct x • CliffordAlgebra.ι Q m ∈
      LinearMap.range (CliffordAlgebra.ι Q) :=
  lipschitzGroup.conjAct_smul_ι_mem_range_ι_of_field h
    (units_mem_lipschitzGroup hx) m

/-- Clifford conjugation by a Spin element stabilizes the full vector range
over any field. -/
public theorem conjAct_smul_range_ι_of_field
    (h : CliffordAlgebra.ActionForm Q)
    {x : (CliffordAlgebra Q)ˣ} (hx : (x : CliffordAlgebra Q) ∈ spinGroup Q) :
    ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q) :=
  lipschitzGroup.conjAct_smul_range_ι_of_field h
    (units_mem_lipschitzGroup hx)

end spinGroup

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V]
variable (Q : QuadraticForm k V)

private noncomputable def cliffordιEquivRange
    (h : CliffordAlgebra.ActionForm Q) :
    V ≃ₗ[k] LinearMap.range (CliffordAlgebra.ι Q) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι Q)
    (CliffordAlgebra.ι_injective_of_actionForm Q h)

private noncomputable def cliffordConjLinearEquiv (x : spinGroup Q) :
    CliffordAlgebra Q ≃ₗ[k] CliffordAlgebra Q :=
  DistribMulAction.toLinearEquiv k (CliffordAlgebra Q)
    (ConjAct.toConjAct (spinGroup.toUnits x))

private noncomputable def cliffordConjRangeEquiv
    (h : CliffordAlgebra.ActionForm Q) (x : spinGroup Q) :
    LinearMap.range (CliffordAlgebra.ι Q) ≃ₗ[k]
      LinearMap.range (CliffordAlgebra.ι Q) :=
  (cliffordConjLinearEquiv Q x).submoduleMap
      (LinearMap.range (CliffordAlgebra.ι Q)) |>.trans
    (LinearEquiv.ofEq _ _
      (spinGroup.conjAct_smul_range_ι_of_field h
        (x := spinGroup.toUnits x) x.property))

private noncomputable def cliffordSpinActionLinearEquiv
    (h : CliffordAlgebra.ActionForm Q) (x : spinGroup Q) :
    V ≃ₗ[k] V :=
  (cliffordιEquivRange Q h).trans <|
    (cliffordConjRangeEquiv Q h x).trans (cliffordιEquivRange Q h).symm

private lemma cliffordSpinActionLinearEquiv_spec
    (h : CliffordAlgebra.ActionForm Q) (x : spinGroup Q) (v : V) :
    CliffordAlgebra.ι Q (cliffordSpinActionLinearEquiv Q h x v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) := by
  change CliffordAlgebra.ι Q
      ((cliffordιEquivRange Q h).symm
        (cliffordConjRangeEquiv Q h x (cliffordιEquivRange Q h v))) = _
  have hrange := congrArg Subtype.val
    ((cliffordιEquivRange Q h).apply_symm_apply
      (cliffordConjRangeEquiv Q h x (cliffordιEquivRange Q h v)))
  change ((cliffordιEquivRange Q h)
    ((cliffordιEquivRange Q h).symm
      (cliffordConjRangeEquiv Q h x (cliffordιEquivRange Q h v)))).val = _
  rw [hrange]
  rfl

private lemma cliffordSpinActionLinearEquiv_preserves
    (h : CliffordAlgebra.ActionForm Q) (x : spinGroup Q) (v : V) :
    Q (cliffordSpinActionLinearEquiv Q h x v) = Q v := by
  let u := spinGroup.toUnits x
  have hs := congrArg (fun z : CliffordAlgebra Q => z * z)
    (cliffordSpinActionLinearEquiv_spec Q h x v)
  rw [CliffordAlgebra.ι_sq_scalar] at hs
  have hconj :
      (↑u * CliffordAlgebra.ι Q v * ↑u⁻¹) *
          (↑u * CliffordAlgebra.ι Q v * ↑u⁻¹) =
        algebraMap k (CliffordAlgebra Q) (Q v) := by
    calc
      (↑u * CliffordAlgebra.ι Q v * ↑u⁻¹) *
            (↑u * CliffordAlgebra.ι Q v * ↑u⁻¹) =
          ↑u * CliffordAlgebra.ι Q v * (↑u⁻¹ * ↑u) *
            CliffordAlgebra.ι Q v * ↑u⁻¹ := by noncomm_ring
      _ = ↑u * (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) * ↑u⁻¹ := by
        rw [Units.inv_mul]
        simp [mul_assoc]
      _ = ↑u * algebraMap k (CliffordAlgebra Q) (Q v) * ↑u⁻¹ := by
        rw [CliffordAlgebra.ι_sq_scalar]
      _ = algebraMap k (CliffordAlgebra Q) (Q v) * ↑u * ↑u⁻¹ := by
        rw [Algebra.commutes]
      _ = algebraMap k (CliffordAlgebra Q) (Q v) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
  change algebraMap k (CliffordAlgebra Q)
      (Q (cliffordSpinActionLinearEquiv Q h x v)) =
    (↑u * CliffordAlgebra.ι Q v * ↑u⁻¹) *
      (↑u * CliffordAlgebra.ι Q v * ↑u⁻¹) at hs
  rw [hconj] at hs
  let : Nontrivial (CliffordAlgebra Q) :=
    (CliffordAlgebra.exteriorEquivOfActionForm Q h).symm.injective.nontrivial
  exact (FaithfulSMul.algebraMap_injective k (CliffordAlgebra Q)) hs

private noncomputable def cliffordSpinActionGL
    (h : CliffordAlgebra.ActionForm Q) :
    spinGroup Q →* LinearMap.GeneralLinearGroup k V where
  toFun x := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (cliffordSpinActionLinearEquiv Q h x)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply CliffordAlgebra.ι_injective_of_actionForm Q h
    change CliffordAlgebra.ι Q (cliffordSpinActionLinearEquiv Q h 1 v) =
      CliffordAlgebra.ι Q v
    rw [cliffordSpinActionLinearEquiv_spec]
    simp
  map_mul' x y := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply CliffordAlgebra.ι_injective_of_actionForm Q h
    change CliffordAlgebra.ι Q (cliffordSpinActionLinearEquiv Q h (x * y) v) =
      CliffordAlgebra.ι Q
        (cliffordSpinActionLinearEquiv Q h x
          (cliffordSpinActionLinearEquiv Q h y v))
    rw [cliffordSpinActionLinearEquiv_spec,
      cliffordSpinActionLinearEquiv_spec,
      cliffordSpinActionLinearEquiv_spec]
    simp only [map_mul, Units.val_mul, mul_inv_rev]
    simp [mul_assoc]

private noncomputable def cliffordSpinActionLinear
    (h : CliffordAlgebra.ActionForm Q) :
    spinGroup Q →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp
    (cliffordSpinActionGL Q h)

/-- The characteristic-free Clifford conjugation action of the Spin group on
the quadratic space. -/
public noncomputable def cliffordSpinAction (h : CliffordAlgebra.ActionForm Q) :
    spinGroup Q →* quadraticIsometrySubgroup Q :=
  (cliffordSpinActionLinear Q h).codRestrict (quadraticIsometrySubgroup Q)
    (fun x => (mem_quadraticIsometrySubgroup Q _).2
      (fun v => cliffordSpinActionLinearEquiv_preserves Q h x v))

/-- The action on vectors is exactly conjugation inside the Clifford algebra. -/
public theorem cliffordSpinAction_spec
    (h : CliffordAlgebra.ActionForm Q) (x : spinGroup Q) (v : V) :
    CliffordAlgebra.ι Q ((cliffordSpinAction Q h x).1 v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) := by
  exact cliffordSpinActionLinearEquiv_spec Q h x v

/-- The same specification with the inverse written as a Spin element. -/
public theorem cliffordSpinAction_spec_inv
    (h : CliffordAlgebra.ActionForm Q) (x : spinGroup Q) (v : V) :
    CliffordAlgebra.ι Q ((cliffordSpinAction Q h x).1 v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (x⁻¹ : spinGroup Q) := by
  exact cliffordSpinAction_spec Q h x v

section Split

variable [FiniteDimensional k V]

/-- The triangular companion form supplied by a split quadratic witness. -/
public noncomputable def SplitQuadraticForm.actionForm
    (s : SplitQuadraticForm Q) : CliffordAlgebra.ActionForm Q :=
  ⟨s.bilinear, s.bilinear_toQuadraticMap⟩

/-- The characteristic-free Spin action attached to an explicit split witness. -/
public noncomputable def cliffordSpinActionOfSplit
    (s : SplitQuadraticForm Q) :
    spinGroup Q →* quadraticIsometrySubgroup Q :=
  cliffordSpinAction Q s.actionForm

/-- Conjugation specification for the action attached to a split witness. -/
public theorem cliffordSpinActionOfSplit_spec
    (s : SplitQuadraticForm Q) (x : spinGroup Q) (v : V) :
    CliffordAlgebra.ι Q ((cliffordSpinActionOfSplit Q s x).1 v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) := by
  exact cliffordSpinAction_spec Q s.actionForm x v

/-- Inverse-form conjugation specification for a split witness. -/
public theorem cliffordSpinActionOfSplit_spec_inv
    (s : SplitQuadraticForm Q) (x : spinGroup Q) (v : V) :
    CliffordAlgebra.ι Q ((cliffordSpinActionOfSplit Q s x).1 v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (x⁻¹ : spinGroup Q) := by
  exact cliffordSpinAction_spec_inv Q s.actionForm x v

end Split

end Theory.AlgebraicGroup
