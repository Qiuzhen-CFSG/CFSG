module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinAction
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_c
public import Theory.AlgebraicGroup.RootSystems.OddOrthogonalCarrier
public import Theory.AlgebraicGroup.RootSystems.CliffordSpinCarrier
public import Theory.AlgebraicGroup.RootSystems.SpinOddCenter
public import Theory.LinearAlgebra.QuadraticForm.CartanDieudonne
public import Theory.AlgebraicGroup.Bor1.ConjugationRational
public import Theory.AlgebraicGroup.Representations.Algebraic.Natural
public import Theory.AlgebraicGroup.Representations.RationalBasis
public import Theory.AlgebraicGroup.Morphism.CodRestrict

/-!
# The odd Spin-to-special-orthogonal isogeny

For a nondegenerate quadratic form of dimension `2 * m + 1` over an
algebraically closed field with invertible `2`, this module constructs the
Clifford-conjugation homomorphism from `spinGroup Q` to the determinant-one
quadratic isometries.  It proves the exact Clifford formula, determinant one,
surjectivity by the Cartan--Dieudonne reflection factorization, and finiteness
of the kernel by embedding it in the computed odd Spin center.

The point homomorphism is made algebraic by viewing the closed Spin carrier
through its left-regular representation.  Conjugation on the full Clifford
endomorphism algebra is rational; matrix coefficients on the embedded vector
left-multiplications give the desired regular map into `GL(V)`, which is then
restricted to the closed special-orthogonal carrier.  The resulting point
formula supplies both ambient-representation compatibility and the exact
`spinCover_points` field of the assembled `OddOrthogonalModel`.
-/

universe u

open CliffordAlgebra MulAction
open scoped Pointwise

namespace Theory.AlgebraicGroup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {k V : Type u} [Field k] [IsAlgClosed k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (Q : QuadraticForm k V)

private noncomputable def oddActionForm
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    CliffordAlgebra.ActionForm Q where
  bilinear := (-Q).toBilin b
  compatible := by
    simpa using QuadraticMap.toQuadraticMap_toBilin (-Q) b

private noncomputable def lipschitzIotaEquivRange
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    V ≃ₗ[k] LinearMap.range (CliffordAlgebra.ι Q) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι Q)
    (CliffordAlgebra.ι_injective_of_actionForm Q (oddActionForm Q b))

private noncomputable def lipschitzConjLinearEquiv
    (x : (CliffordAlgebra Q)ˣ) :
    CliffordAlgebra Q ≃ₗ[k] CliffordAlgebra Q :=
  DistribMulAction.toLinearEquiv k (CliffordAlgebra Q)
    (ConjAct.toConjAct x)

private noncomputable def lipschitzConjRangeEquiv
    (x : (CliffordAlgebra Q)ˣ) (hx : x ∈ lipschitzGroup Q) :
    LinearMap.range (CliffordAlgebra.ι Q) ≃ₗ[k]
      LinearMap.range (CliffordAlgebra.ι Q) :=
  (lipschitzConjLinearEquiv Q x).submoduleMap
      (LinearMap.range (CliffordAlgebra.ι Q)) |>.trans
    (LinearEquiv.ofEq _ _ (lipschitzGroup.conjAct_smul_range_ι hx))

private noncomputable def lipschitzLinearEquiv
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : (CliffordAlgebra Q)ˣ) (hx : x ∈ lipschitzGroup Q) : V ≃ₗ[k] V :=
  (lipschitzIotaEquivRange Q b).trans <|
    (lipschitzConjRangeEquiv Q x hx).trans (lipschitzIotaEquivRange Q b).symm

private lemma lipschitzLinearEquiv_spec
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : (CliffordAlgebra Q)ˣ) (hx : x ∈ lipschitzGroup Q) (v : V) :
    CliffordAlgebra.ι Q (lipschitzLinearEquiv Q b x hx v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑(x⁻¹) : CliffordAlgebra Q) := by
  change CliffordAlgebra.ι Q
      ((lipschitzIotaEquivRange Q b).symm
        (lipschitzConjRangeEquiv Q x hx (lipschitzIotaEquivRange Q b v))) = _
  have hrange := congrArg Subtype.val
    ((lipschitzIotaEquivRange Q b).apply_symm_apply
      (lipschitzConjRangeEquiv Q x hx (lipschitzIotaEquivRange Q b v)))
  change ((lipschitzIotaEquivRange Q b)
    ((lipschitzIotaEquivRange Q b).symm
      (lipschitzConjRangeEquiv Q x hx
        (lipschitzIotaEquivRange Q b v)))).val = _
  rw [hrange]
  rfl

private lemma lipschitzLinearEquiv_one
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    lipschitzLinearEquiv Q b 1 (one_mem (lipschitzGroup Q)) = 1 := by
  ext v
  apply CliffordAlgebra.ι_injective_of_actionForm Q (oddActionForm Q b)
  rw [lipschitzLinearEquiv_spec]
  simp

private lemma lipschitzLinearEquiv_mul
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x y : (CliffordAlgebra Q)ˣ) (hx : x ∈ lipschitzGroup Q)
    (hy : y ∈ lipschitzGroup Q) :
    lipschitzLinearEquiv Q b (x * y) (mul_mem hx hy) =
      lipschitzLinearEquiv Q b x hx * lipschitzLinearEquiv Q b y hy := by
  ext v
  apply CliffordAlgebra.ι_injective_of_actionForm Q (oddActionForm Q b)
  rw [lipschitzLinearEquiv_spec, LinearEquiv.mul_apply,
    lipschitzLinearEquiv_spec, lipschitzLinearEquiv_spec]
  simp only [Units.val_mul, mul_inv_rev]
  simp [mul_assoc]

private lemma lipschitzLinearEquiv_inv
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : (CliffordAlgebra Q)ˣ) (hx : x ∈ lipschitzGroup Q) :
    lipschitzLinearEquiv Q b x⁻¹ (inv_mem hx) =
      (lipschitzLinearEquiv Q b x hx)⁻¹ := by
  apply mul_left_cancel (a := lipschitzLinearEquiv Q b x hx)
  rw [← lipschitzLinearEquiv_mul]
  simp only [mul_inv_cancel]
  rw [lipschitzLinearEquiv_one]

private lemma negativeReflection_det_one
    (hodd : Odd (Module.finrank k V)) (v : V) (hv : Q v ≠ 0) :
    LinearEquiv.det
      ((LinearEquiv.neg k : V ≃ₗ[k] V) *
        QuadraticForm.anisotropicReflection Q v hv) = 1 := by
  have hneg : LinearEquiv.det (LinearEquiv.neg k : V ≃ₗ[k] V) =
      (-1 : kˣ) ^ Module.finrank k V := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det (-(LinearMap.id : V →ₗ[k] V)) = _
    have hlin : -(LinearMap.id : V →ₗ[k] V) =
        (-1 : k) • (LinearMap.id : V →ₗ[k] V) := by simp
    rw [hlin, LinearMap.det_smul]
    simp
  rw [map_mul, hneg, QuadraticForm.anisotropicReflection_det,
    hodd.neg_one_pow]
  simp

private lemma lipschitzLinearEquiv_generator
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : (CliffordAlgebra Q)ˣ)
    (hx : x ∈ ((↑) : (CliffordAlgebra Q)ˣ → CliffordAlgebra Q) ⁻¹'
      Set.range (CliffordAlgebra.ι Q))
    (hxL : x ∈ lipschitzGroup Q) :
    ∃ v : V, ∃ hv : Q v ≠ 0,
      lipschitzLinearEquiv Q b x hxL =
        (LinearEquiv.neg k : V ≃ₗ[k] V) *
          QuadraticForm.anisotropicReflection Q v hv := by
  obtain ⟨v, hvx⟩ := hx
  let _ := x.invertible
  let _ : Invertible (CliffordAlgebra.ι Q v) := by rwa [hvx]
  let _ : Invertible (Q v) := CliffordAlgebra.invertibleOfInvertibleι Q v
  have hv : Q v ≠ 0 := isUnit_iff_ne_zero.mp (isUnit_of_invertible (Q v))
  have hinv : (↑(x⁻¹) : CliffordAlgebra Q) =
      ⅟(CliffordAlgebra.ι Q v) := by
    calc
      (↑(x⁻¹) : CliffordAlgebra Q) =
          1 * (↑(x⁻¹) : CliffordAlgebra Q) := (one_mul _).symm
      _ = (⅟(CliffordAlgebra.ι Q v) * CliffordAlgebra.ι Q v) *
          (↑(x⁻¹) : CliffordAlgebra Q) := by rw [invOf_mul_self]
      _ = ⅟(CliffordAlgebra.ι Q v) *
          (CliffordAlgebra.ι Q v * (↑(x⁻¹) : CliffordAlgebra Q)) := by
            rw [mul_assoc]
      _ = ⅟(CliffordAlgebra.ι Q v) *
          ((x : CliffordAlgebra Q) * (↑(x⁻¹) : CliffordAlgebra Q)) := by
            congr 1
            exact congrArg
              (fun z : CliffordAlgebra Q => z * (↑(x⁻¹) : CliffordAlgebra Q)) hvx
      _ = ⅟(CliffordAlgebra.ι Q v) := by rw [Units.mul_inv, mul_one]
  refine ⟨v, hv, ?_⟩
  ext w
  apply CliffordAlgebra.ι_injective_of_actionForm Q (oddActionForm Q b)
  rw [lipschitzLinearEquiv_spec]
  change (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q w *
      (↑(x⁻¹) : CliffordAlgebra Q) =
    CliffordAlgebra.ι Q
      (-QuadraticForm.anisotropicReflection Q v hv w)
  rw [← hvx, hinv]
  rw [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  apply congrArg (CliffordAlgebra.ι Q)
  rw [QuadraticForm.anisotropicReflection_apply]
  have hpolar : QuadraticMap.polar Q v w =
      2 * QuadraticMap.associated Q v w := by
    have h := DFunLike.congr_fun (DFunLike.congr_fun
      (QuadraticMap.two_nsmul_associated k Q) v) w
    simpa [two_smul, two_mul] using h.symm
  rw [hpolar, invOf_eq_inv]
  module

private lemma lipschitzLinearEquiv_det_one
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hodd : Odd (Module.finrank k V))
    (x : (CliffordAlgebra Q)ˣ) (hx : x ∈ lipschitzGroup Q) :
    LinearEquiv.det (lipschitzLinearEquiv Q b x hx) = 1 := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
      have hxL : x ∈ lipschitzGroup Q := Subgroup.subset_closure hx
      obtain ⟨v, hv, hact⟩ := lipschitzLinearEquiv_generator Q b x hx hxL
      rw [hact]
      exact negativeReflection_det_one Q hodd v hv
  | inv_mem x hx =>
      have hxL : x ∈ lipschitzGroup Q := Subgroup.subset_closure hx
      obtain ⟨v, hv, hact⟩ := lipschitzLinearEquiv_generator Q b x hx hxL
      rw [lipschitzLinearEquiv_inv Q b x hxL, hact, map_inv,
        negativeReflection_det_one Q hodd v hv, inv_one]
  | one =>
      rw [lipschitzLinearEquiv_one, map_one]
  | mul x y hx hy ihx ihy =>
      have hxL : x ∈ lipschitzGroup Q := hx
      have hyL : y ∈ lipschitzGroup Q := hy
      rw [lipschitzLinearEquiv_mul Q b x y hxL hyL,
        map_mul, ihx, ihy, mul_one]

private lemma cliffordSpinAction_eq_lipschitzLinearEquiv
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (x : spinGroup Q) :
    (cliffordSpinAction Q (oddActionForm Q b) x).1 =
      lipschitzLinearEquiv Q b (spinGroup.toUnits x)
        (spinGroup.units_mem_lipschitzGroup x.property) := by
  ext v
  apply CliffordAlgebra.ι_injective_of_actionForm Q (oddActionForm Q b)
  rw [cliffordSpinAction_spec, lipschitzLinearEquiv_spec]
  change (↑(spinGroup.toUnits x) : CliffordAlgebra Q) *
      CliffordAlgebra.ι Q v *
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) = _
  rfl

private lemma cliffordSpinAction_det_one
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hodd : Odd (Module.finrank k V)) (x : spinGroup Q) :
    LinearEquiv.det ((cliffordSpinAction Q (oddActionForm Q b) x).1) = 1 := by
  rw [cliffordSpinAction_eq_lipschitzLinearEquiv Q b x]
  exact lipschitzLinearEquiv_det_one Q b hodd _ _

public noncomputable def oddCliffordSpinAction
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hodd : Odd (Module.finrank k V)) :
    spinGroup Q →* specialOrthogonalPointGroup Q :=
  let linearAction : spinGroup Q →* (V ≃ₗ[k] V) :=
    (quadraticIsometrySubgroup Q).subtype.comp
      (cliffordSpinAction Q (oddActionForm Q b))
  linearAction.codRestrict (specialOrthogonalPointGroup Q) fun x =>
    (mem_specialOrthogonalPointGroup Q _).2
      ⟨(mem_quadraticIsometrySubgroup Q _).1
          (cliffordSpinAction Q (oddActionForm Q b) x).property,
        cliffordSpinAction_det_one Q b hodd x⟩

public lemma oddCliffordSpinAction_spec
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hodd : Odd (Module.finrank k V)) (x : spinGroup Q) (v : V) :
    CliffordAlgebra.ι Q ((oddCliffordSpinAction Q b hodd x).1 v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) := by
  exact cliffordSpinAction_spec Q (oddActionForm Q b) x v

private lemma oddCliffordSpinAction_ker_le_center
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hodd : Odd (Module.finrank k V)) :
    (oddCliffordSpinAction Q b hodd).ker ≤ Subgroup.center (spinGroup Q) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  change (y : CliffordAlgebra Q) * (x : CliffordAlgebra Q) =
    (x : CliffordAlgebra Q) * (y : CliffordAlgebra Q)
  have hcomm (z : CliffordAlgebra Q) :
      z * (x : CliffordAlgebra Q) = (x : CliffordAlgebra Q) * z := by
    induction z using CliffordAlgebra.induction with
    | algebraMap r => exact Algebra.commutes r (x : CliffordAlgebra Q)
    | ι v =>
        have haction : oddCliffordSpinAction Q b hodd x = 1 :=
          MonoidHom.mem_ker.mp hx
        have h := oddCliffordSpinAction_spec Q b hodd x v
        rw [haction] at h
        change CliffordAlgebra.ι Q v =
          (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
            (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) at h
        have h' := congrArg
          (fun z : CliffordAlgebra Q =>
            z * (↑(spinGroup.toUnits x) : CliffordAlgebra Q)) h
        change CliffordAlgebra.ι Q v *
            (↑(spinGroup.toUnits x) : CliffordAlgebra Q) =
          (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v
        have h'' : CliffordAlgebra.ι Q v *
              (↑(spinGroup.toUnits x) : CliffordAlgebra Q) =
            (x : CliffordAlgebra Q) *
              (CliffordAlgebra.ι Q v *
                ((↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) *
                  (↑(spinGroup.toUnits x) : CliffordAlgebra Q))) := by
          simpa only [mul_assoc] using h'
        rw [Units.inv_mul, mul_one] at h''
        exact h''
    | mul a c ha hc =>
        calc
          a * c * (x : CliffordAlgebra Q) = a * (c * x) := by rw [mul_assoc]
          _ = a * (x * c) := by rw [hc]
          _ = (a * x) * c := by rw [mul_assoc]
          _ = (x * a) * c := by rw [ha]
          _ = x * (a * c) := by rw [mul_assoc]
    | add a c ha hc =>
        calc
          (a + c) * (x : CliffordAlgebra Q) = a * x + c * x := add_mul _ _ _
          _ = x * a + x * c := by rw [ha, hc]
          _ = x * (a + c) := (mul_add _ _ _).symm
  exact hcomm y

private theorem oddSpinCenterFinite
    (m : ℕ) (hm : 2 ≤ m) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1) :
    Finite (Subgroup.center (spinGroup Q)) :=
  Finite.of_injective (spinGroup_center_iso_rootsOfUnity_two m hm hQ hdim)
    (spinGroup_center_iso_rootsOfUnity_two m hm hQ hdim).injective

private theorem oddCliffordSpinActionKernelFinite
    (m : ℕ) (hm : 2 ≤ m) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1)
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Finite (oddCliffordSpinAction Q b ⟨m, hdim⟩).ker := by
  let _ : Finite (Subgroup.center (spinGroup Q)) :=
    oddSpinCenterFinite Q m hm hQ hdim
  let toCenter : (oddCliffordSpinAction Q b ⟨m, hdim⟩).ker →
      Subgroup.center (spinGroup Q) := fun x =>
    ⟨x.1, oddCliffordSpinAction_ker_le_center Q b ⟨m, hdim⟩ x.2⟩
  exact Finite.of_injective toCenter fun a c h =>
    Subtype.ext (show a.1 = c.1 from
      congrArg (fun z : Subgroup.center (spinGroup Q) => z.1) h)

private noncomputable def reflectionNormalizingScalar
    (a : {v : V // Q v ≠ 0}) : k :=
  Classical.choose (IsAlgClosed.exists_eq_mul_self (-(Q a.1)⁻¹))

private lemma reflectionNormalizingScalar_spec
    (a : {v : V // Q v ≠ 0}) :
    -(Q a.1)⁻¹ = reflectionNormalizingScalar Q a *
      reflectionNormalizingScalar Q a :=
  Classical.choose_spec (IsAlgClosed.exists_eq_mul_self (-(Q a.1)⁻¹))

private noncomputable def normalizedReflectionVector
    (a : {v : V // Q v ≠ 0}) : V :=
  reflectionNormalizingScalar Q a • a.1

private lemma normalizedReflectionVector_norm
    (a : {v : V // Q v ≠ 0}) :
    Q (normalizedReflectionVector Q a) = -1 := by
  rw [normalizedReflectionVector, QuadraticMap.map_smul]
  simp only [smul_eq_mul]
  rw [← reflectionNormalizingScalar_spec Q a]
  simp [a.2]

private lemma normalizedReflectionVector_ne_zero
    (a : {v : V // Q v ≠ 0}) :
    Q (normalizedReflectionVector Q a) ≠ 0 := by
  rw [normalizedReflectionVector_norm]
  exact neg_ne_zero.mpr one_ne_zero

private lemma normalized_anisotropicReflection
    (a : {v : V // Q v ≠ 0}) :
    QuadraticForm.anisotropicReflection Q (normalizedReflectionVector Q a)
        (normalizedReflectionVector_ne_zero Q a) =
      QuadraticForm.anisotropicReflection Q a.1 a.2 := by
  ext v
  rw [QuadraticForm.anisotropicReflection_apply,
    QuadraticForm.anisotropicReflection_apply]
  rw [normalizedReflectionVector_norm]
  simp only [normalizedReflectionVector, inv_neg, inv_one,
    LinearMap.map_smul, smul_smul]
  have hc := reflectionNormalizingScalar_spec Q a
  apply congrArg (fun z : V => v - z)
  apply congrArg (fun z : k => z • a.1)
  simp only [LinearMap.smul_apply, smul_eq_mul]
  calc
    2 * -1 *
          (reflectionNormalizingScalar Q a * QuadraticMap.associated Q a.1 v) *
          reflectionNormalizingScalar Q a =
        -2 * (reflectionNormalizingScalar Q a * reflectionNormalizingScalar Q a) *
          QuadraticMap.associated Q a.1 v := by ring
    _ = -2 * (-(Q a.1)⁻¹) * QuadraticMap.associated Q a.1 v := by
      rw [← hc]
    _ = 2 * (Q a.1)⁻¹ * QuadraticMap.associated Q a.1 v := by ring

private noncomputable def normalizedReflectionUnit
    (a : {v : V // Q v ≠ 0}) : (CliffordAlgebra Q)ˣ where
  val := CliffordAlgebra.ι Q (normalizedReflectionVector Q a)
  inv := -CliffordAlgebra.ι Q (normalizedReflectionVector Q a)
  val_inv := by simp [CliffordAlgebra.ι_sq_scalar,
    normalizedReflectionVector_norm]
  inv_val := by simp [CliffordAlgebra.ι_sq_scalar,
    normalizedReflectionVector_norm]

@[simp]
private lemma normalizedReflectionUnit_val
    (a : {v : V // Q v ≠ 0}) :
    (normalizedReflectionUnit Q a : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (normalizedReflectionVector Q a) := rfl

private lemma normalizedReflectionVector_mem_pinGroup
    (a : {v : V // Q v ≠ 0}) :
    CliffordAlgebra.ι Q (normalizedReflectionVector Q a) ∈ pinGroup Q := by
  rw [pinGroup.mem_iff]
  refine ⟨?_, ?_⟩
  · refine ⟨normalizedReflectionUnit Q a, ?_, rfl⟩
    exact Subgroup.subset_closure
      ⟨normalizedReflectionVector Q a, normalizedReflectionUnit_val Q a⟩
  · exact ⟨by simp [normalizedReflectionVector_norm],
      by simp [normalizedReflectionVector_norm]⟩

private lemma normalizedReflectionUnits_prod_mem_pinGroup
    (vs : List {v : V // Q v ≠ 0}) :
    ((vs.map (normalizedReflectionUnit Q)).prod : CliffordAlgebra Q) ∈ pinGroup Q := by
  induction vs with
  | nil => simp
  | cons a vs ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul,
        normalizedReflectionUnit_val]
      exact mul_mem (normalizedReflectionVector_mem_pinGroup Q a) ih

private lemma normalizedReflectionUnits_prod_mem_evenOdd
    (vs : List {v : V // Q v ≠ 0}) :
    ((vs.map (normalizedReflectionUnit Q)).prod : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (vs.length : ZMod 2) := by
  induction vs with
  | nil => simpa using
      (SetLike.one_mem_graded (A := CliffordAlgebra.evenOdd Q))
  | cons a vs ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul,
        normalizedReflectionUnit_val, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      simpa [add_comm] using SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mem_evenOdd_one Q (normalizedReflectionVector Q a)) ih

private noncomputable def evenReflectionSpinLift
    (vs : List {v : V // Q v ≠ 0}) (hvs : Even vs.length) : spinGroup Q := by
  let p := (vs.map (normalizedReflectionUnit Q)).prod
  refine ⟨(p : CliffordAlgebra Q), ?_⟩
  rw [spinGroup.mem_iff]
  refine ⟨normalizedReflectionUnits_prod_mem_pinGroup Q vs, ?_⟩
  have hgrade := normalizedReflectionUnits_prod_mem_evenOdd Q vs
  have hcast : (vs.length : ZMod 2) = 0 := hvs.natCast_zmod_two
  rwa [hcast] at hgrade

private lemma normalizedReflectionUnit_conjugation
    (a : {v : V // Q v ≠ 0}) (v : V) :
    (normalizedReflectionUnit Q a : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q v *
          (↑((normalizedReflectionUnit Q a)⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q
        (-QuadraticForm.anisotropicReflection Q a.1 a.2 v) := by
  change CliffordAlgebra.ι Q (normalizedReflectionVector Q a) *
      CliffordAlgebra.ι Q v *
        (-CliffordAlgebra.ι Q (normalizedReflectionVector Q a)) = _
  let _ : Invertible (Q (normalizedReflectionVector Q a)) :=
    invertibleOfNonzero (normalizedReflectionVector_ne_zero Q a)
  let _ : Invertible
      (CliffordAlgebra.ι Q (normalizedReflectionVector Q a)) :=
    CliffordAlgebra.invertibleιOfInvertible Q (normalizedReflectionVector Q a)
  have hinv : -CliffordAlgebra.ι Q (normalizedReflectionVector Q a) =
      ⅟(CliffordAlgebra.ι Q (normalizedReflectionVector Q a)) := by
    rw [CliffordAlgebra.invOf_ι, invOf_eq_inv,
      normalizedReflectionVector_norm]
    simp
  rw [hinv]
  rw [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  apply congrArg (CliffordAlgebra.ι Q)
  rw [← normalized_anisotropicReflection Q a,
    QuadraticForm.anisotropicReflection_apply]
  have hpolar :
      QuadraticMap.polar Q (normalizedReflectionVector Q a) v =
        2 * QuadraticMap.associated Q (normalizedReflectionVector Q a) v := by
    have h := DFunLike.congr_fun (DFunLike.congr_fun
      (QuadraticMap.two_nsmul_associated k Q)
        (normalizedReflectionVector Q a)) v
    simpa [two_smul, two_mul] using h.symm
  rw [hpolar, invOf_eq_inv]
  module

private lemma normalizedReflectionUnits_prod_conjugation
    (vs : List {v : V // Q v ≠ 0}) (v : V) :
    CliffordAlgebra.ι Q
        (((-1 : k) ^ vs.length) •
          QuadraticForm.anisotropicReflectionsProduct Q vs v) =
      ((vs.map (normalizedReflectionUnit Q)).prod : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q v *
          (↑((vs.map (normalizedReflectionUnit Q)).prod⁻¹) :
            CliffordAlgebra Q) := by
  induction vs with
  | nil => simp
  | cons a vs ih =>
      have hvec :
          ((-1 : k) ^ (a :: vs).length) •
              QuadraticForm.anisotropicReflectionsProduct Q (a :: vs) v =
            -QuadraticForm.anisotropicReflection Q a.1 a.2
              (((-1 : k) ^ vs.length) •
                QuadraticForm.anisotropicReflectionsProduct Q vs v) := by
        simp only [List.length_cons,
          QuadraticForm.anisotropicReflectionsProduct_cons,
          LinearEquiv.mul_apply, map_smul, pow_succ]
        module
      rw [hvec, ← normalizedReflectionUnit_conjugation, ih]
      simp only [List.map_cons, List.prod_cons, Units.val_mul, mul_inv_rev]
      simp [mul_assoc]

private lemma evenReflectionSpinLift_action
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hodd : Odd (Module.finrank k V))
    (vs : List {v : V // Q v ≠ 0}) (hvs : Even vs.length) :
    (oddCliffordSpinAction Q b hodd (evenReflectionSpinLift Q vs hvs)).1 =
      QuadraticForm.anisotropicReflectionsProduct Q vs := by
  ext v
  apply CliffordAlgebra.ι_injective_of_actionForm Q (oddActionForm Q b)
  rw [oddCliffordSpinAction_spec]
  let p := (vs.map (normalizedReflectionUnit Q)).prod
  have hp : spinGroup.toUnits (evenReflectionSpinLift Q vs hvs) = p := by
    apply Units.ext
    rfl
  have hpval : (evenReflectionSpinLift Q vs hvs : CliffordAlgebra Q) =
      (p : CliffordAlgebra Q) := by
    rfl
  rw [hp]
  rw [hpval]
  rw [← normalizedReflectionUnits_prod_conjugation Q vs v]
  rw [Even.neg_one_pow hvs, one_smul]

public lemma oddCliffordSpinAction_surjective
    (m : ℕ) (_hm : 2 ≤ m) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1)
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Function.Surjective (oddCliffordSpinAction Q b ⟨m, hdim⟩) := by
  intro g
  obtain ⟨vs, _hlen, hvs, hfac⟩ :=
    QuadraticForm.cartanDieudonne_det_one Q hQ g.1
      ((mem_specialOrthogonalPointGroup Q g.1).1 g.2).1
      ((mem_specialOrthogonalPointGroup Q g.1).1 g.2).2
  refine ⟨evenReflectionSpinLift Q vs hvs, ?_⟩
  apply Subtype.ext
  rw [evenReflectionSpinLift_action Q b ⟨m, hdim⟩ vs hvs]
  exact hfac.symm

private noncomputable def oddSpinCarrierRepresentation
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    RationalRepresentation S.carrierVariety (CliffordAlgebra Q) := by
  let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
  letI := S.carrierAlgebraicGroup
  exact ⟨
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k
        (CliffordAlgebra Q)).symm.toMonoidHom.comp
      ((Units.mulLeftLinearEquiv k (CliffordAlgebra Q)).comp
        (spinGroup.toUnits.comp
          (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e).toMonoidHom))⟩

private lemma oddSpinCarrierRepresentation_action
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    ∀ g,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
          ((oddSpinCarrierRepresentation Q hQ hpos hodd b e).action g) =
        (spinGroup.toUnits
          (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e g)).mulLeftLinearEquiv
            k (CliffordAlgebra Q) := by
  dsimp only
  intro g
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (CliffordAlgebra Q)).apply_symm_apply _

private lemma oddSpinCarrierRepresentation_isRational
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    IsRationalRepresentation
      (oddSpinCarrierRepresentation Q hQ hpos hodd b e) := by
  dsimp only
  refine ⟨e, (oddSpinClosedSubgroup Q hQ hpos hodd b e).inclusion, ?_⟩
  intro g
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (CliffordAlgebra Q)).injective
  rw [oddSpinCarrierRepresentation_action Q hQ hpos hodd b e]
  exact oddSpinClosedSubgroup_linear_points Q hQ hpos hodd b e g

private def cliffordVectorLeftEmbedding :
    V →ₗ[k] Module.End k (CliffordAlgebra Q) :=
  (Algebra.lmul k (CliffordAlgebra Q)).toLinearMap.comp (CliffordAlgebra.ι Q)

private lemma cliffordVectorLeftEmbedding_injective
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Function.Injective (cliffordVectorLeftEmbedding Q) := by
  intro v w hvw
  apply CliffordAlgebra.ι_injective_of_actionForm Q (oddActionForm Q b)
  have h := LinearMap.congr_fun hvw 1
  simpa [cliffordVectorLeftEmbedding] using h

private noncomputable def cliffordVectorLeftEquivRange
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    V ≃ₗ[k] LinearMap.range (cliffordVectorLeftEmbedding Q) :=
  LinearEquiv.ofInjective (cliffordVectorLeftEmbedding Q)
    (cliffordVectorLeftEmbedding_injective Q b)

private noncomputable def cliffordVectorLeftBasis
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Module.Basis (Fin (Module.finrank k V)) k
      (LinearMap.range (cliffordVectorLeftEmbedding Q)) :=
  b.map (cliffordVectorLeftEquivRange Q b)

private noncomputable def oddSpinCarrierAction
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    Variety.Point S.carrierVariety →* LinearMap.GeneralLinearGroup k V := by
  let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
  letI := S.carrierAlgebraicGroup
  exact
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).symm.toMonoidHom.comp
      ((specialOrthogonalPointGroup Q).subtype.comp
        ((oddCliffordSpinAction Q b hodd).comp
          (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e).toMonoidHom))

private lemma oddSpinCarrierAction_linearEquiv
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    ∀ g,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (oddSpinCarrierAction Q hQ hpos hodd b e g) =
        (oddCliffordSpinAction Q b hodd
          (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e g)).1 := by
  dsimp only
  intro g
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).apply_symm_apply _

private lemma oddSpinCarrier_conj_vectorLeft
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    ∀ g v,
      Bor1.conjEndLinearMap
          ((oddSpinCarrierRepresentation Q hQ hpos hodd b e).action g)
          (cliffordVectorLeftEmbedding Q v) =
        cliffordVectorLeftEmbedding Q
          ((oddSpinCarrierAction Q hQ hpos hodd b e g : Module.End k V) v) := by
  dsimp only
  intro g v
  let x := oddSpinClosedSubgroupPoints Q hQ hpos hodd b e g
  have hleft := oddSpinCarrierRepresentation_action Q hQ hpos hodd b e g
  have haction := oddSpinCarrierAction_linearEquiv Q hQ hpos hodd b e g
  have hleftGL :
      (oddSpinCarrierRepresentation Q hQ hpos hodd b e).action g =
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (CliffordAlgebra Q)).symm
            ((spinGroup.toUnits x).mulLeftLinearEquiv k (CliffordAlgebra Q)) := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k
      (CliffordAlgebra Q)).injective
    simpa using hleft
  apply LinearMap.ext
  intro z
  change
    ((oddSpinCarrierRepresentation Q hQ hpos hodd b e).action g :
        Module.End k (CliffordAlgebra Q))
      (CliffordAlgebra.ι Q v *
        (↑(((oddSpinCarrierRepresentation Q hQ hpos hodd b e).action g)⁻¹) :
          Module.End k (CliffordAlgebra Q)) z) =
      CliffordAlgebra.ι Q ((oddSpinCarrierAction Q hQ hpos hodd b e g :
        Module.End k V) v) * z
  rw [hleftGL]
  change (x : CliffordAlgebra Q) *
      (CliffordAlgebra.ι Q v *
        ((↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) * z)) = _
  rw [← mul_assoc, ← mul_assoc]
  rw [← oddCliffordSpinAction_spec Q b hodd x v]
  rw [← haction]
  rfl

private noncomputable def oddSpinCarrierRationalRepresentation
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    RationalRepresentation S.carrierVariety V := by
  let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
  letI := S.carrierAlgebraicGroup
  exact ⟨oddSpinCarrierAction Q hQ hpos hodd b e⟩

private theorem oddSpinCarrierRationalRepresentation_isRational
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    IsRationalRepresentation
      (oddSpinCarrierRationalRepresentation Q hQ hpos hodd b e) := by
  let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
  letI := S.carrierAlgebraicGroup
  letI : Module.Finite k (CliffordAlgebra Q) := Module.Finite.of_basis e
  let ρ := oddSpinCarrierRepresentation Q hQ hpos hodd b e
  let σ := Bor1.conjEndRationalRepresentation ρ
  obtain ⟨c, f, hf⟩ := Bor1.conjEndRationalRepresentation_isRational ρ
    (oddSpinCarrierRepresentation_isRational Q hQ hpos hodd b e)
  let U := LinearMap.range (cliffordVectorLeftEmbedding Q)
  let cU := cliffordVectorLeftBasis Q b
  let matrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → S.carrierVariety.PolynomialFunction := fun i j =>
    rationalRepresentationLinearMatrixCoefficient σ c f
      (Subspace.dualLift U (cU.dualBasis i)) (cU j : Module.End k (CliffordAlgebra Q))
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr (((oddSpinCarrierAction Q hQ hpos hodd b e g :
          Module.End k V)) (b j)) i := by
    intro i j g
    rw [show matrixCoefficient i j =
      rationalRepresentationLinearMatrixCoefficient σ c f
        (Subspace.dualLift U (cU.dualBasis i))
          (cU j : Module.End k (CliffordAlgebra Q)) by rfl]
    rw [rationalRepresentationLinearMatrixCoefficient_apply σ c f hf]
    change (Subspace.dualLift U (cU.dualBasis i))
      (Bor1.conjEndLinearMap (ρ.action g)
        (cU j : Module.End k (CliffordAlgebra Q))) = _
    have hcUj : (cU j : Module.End k (CliffordAlgebra Q)) =
        cliffordVectorLeftEmbedding Q (b j) := by
      rw [show cU = cliffordVectorLeftBasis Q b by rfl,
        cliffordVectorLeftBasis, Module.Basis.map_apply]
      rfl
    rw [hcUj]
    rw [show ρ = oddSpinCarrierRepresentation Q hQ hpos hodd b e by rfl]
    rw [oddSpinCarrier_conj_vectorLeft Q hQ hpos hodd b e]
    let y : U := cliffordVectorLeftEquivRange Q b
      ((oddSpinCarrierAction Q hQ hpos hodd b e g : Module.End k V) (b j))
    change (Subspace.dualLift U (cU.dualBasis i)) (y : Module.End k
      (CliffordAlgebra Q)) = _
    rw [Subspace.dualLift_of_subtype]
    rw [Module.Basis.dualBasis_apply]
    rw [show cU = cliffordVectorLeftBasis Q b by rfl,
      cliffordVectorLeftBasis, Module.Basis.map_repr]
    simp [y, cliffordVectorLeftEquivRange]
  let inverseMatrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → S.carrierVariety.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism S.carrierVariety)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr (((((oddSpinCarrierAction Q hQ hpos hodd b e g)⁻¹ :
          LinearMap.GeneralLinearGroup k V) : Module.End k V)) (b j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let F := generalLinearRepresentationMorphismOfInverseMatrixCoefficient b
    (oddSpinCarrierAction Q hQ hpos hodd b e) matrixCoefficient
      inverseMatrixCoefficient matrixCoefficient_apply inverseMatrixCoefficient_apply
  refine ⟨b, F, ?_⟩
  intro g
  change glPointEquivOf k V b
    (generalLinearRepresentationPoint b
      (oddSpinCarrierAction Q hQ hpos hodd b e g)) = _
  exact glPointEquivOf_generalLinearRepresentationPoint b _

private noncomputable def oddSpinAmbientActionMorphism
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    AlgebraicGroup.Morphism S.carrierVariety (glVarietyOf k V) := by
  let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
  letI := S.carrierAlgebraicGroup
  exact Classical.choose
    (IsRationalRepresentation.exists_morphism_in_basis
      (oddSpinCarrierRationalRepresentation_isRational Q hQ hpos hodd b e) b)

private lemma oddSpinAmbientActionMorphism_points
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := S.carrierAlgebraicGroup
    ∀ g,
      glPointEquivOf k V b
          ((oddSpinAmbientActionMorphism Q hQ hpos hodd b e).onPoints g) =
        oddSpinCarrierAction Q hQ hpos hodd b e g := by
  dsimp only
  intro g
  exact (Classical.choose_spec
    (IsRationalRepresentation.exists_morphism_in_basis
      (oddSpinCarrierRationalRepresentation_isRational Q hQ hpos hodd b e) b)) g

/-- Clifford conjugation, realized as an algebraic morphism from the closed
Spin carrier to the closed special-orthogonal carrier. -/
public noncomputable def oddSpinCoverMorphism
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    let O := oddSpecialOrthogonalClosedSubgroup Q b
    letI := S.carrierAlgebraicGroup
    letI := O.carrierAlgebraicGroup
    AlgebraicGroup.Morphism S.carrierVariety O.carrierVariety := by
  let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
  let O := oddSpecialOrthogonalClosedSubgroup Q b
  letI := S.carrierAlgebraicGroup
  letI := O.carrierAlgebraicGroup
  exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup
    (oddSpinAmbientActionMorphism Q hQ hpos hodd b e) O fun g => by
      rw [oddSpecialOrthogonalClosedSubgroup_carrier]
      rw [oddSpinAmbientActionMorphism_points Q hQ hpos hodd b e]
      rw [oddSpinCarrierAction_linearEquiv Q hQ hpos hodd b e]
      exact (oddCliffordSpinAction Q b hodd
        (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e g)).2

/-- The ambient linear map of the algebraic cover is the Clifford action. -/
public theorem oddSpinCoverMorphism_ambient_points
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    let O := oddSpecialOrthogonalClosedSubgroup Q b
    letI := S.carrierAlgebraicGroup
    letI := O.carrierAlgebraicGroup
    ∀ g,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V b
            (O.inclusion.onPoints
              ((oddSpinCoverMorphism Q hQ hpos hodd b e).onPoints g))) =
        (oddCliffordSpinAction Q b hodd
          (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e g)).1 := by
  dsimp only
  intro g
  rw [oddSpinCoverMorphism]
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  rw [oddSpinAmbientActionMorphism_points Q hQ hpos hodd b e]
  exact oddSpinCarrierAction_linearEquiv Q hQ hpos hodd b e g

/-- Under the two carrier point equivalences, the algebraic cover is exactly
the Clifford-conjugation homomorphism. -/
public theorem oddSpinCoverMorphism_points
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    let O := oddSpecialOrthogonalClosedSubgroup Q b
    letI := S.carrierAlgebraicGroup
    letI := O.carrierAlgebraicGroup
    ∀ g,
      oddSpecialOrthogonalClosedSubgroupPoints Q b
          ((oddSpinCoverMorphism Q hQ hpos hodd b e).onPoints g) =
        oddCliffordSpinAction Q b hodd
          (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e g) := by
  dsimp only
  intro g
  apply Subtype.ext
  rw [← oddSpecialOrthogonalClosedSubgroup_linear_points Q b
    ((oddSpinCoverMorphism Q hQ hpos hodd b e).onPoints g)]
  exact oddSpinCoverMorphism_ambient_points Q hQ hpos hodd b e g

/-- The algebraic Spin cover is surjective on algebraically closed points. -/
public theorem oddSpinCoverMorphism_surjective
    (m : ℕ) (hm : 2 ≤ m) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let hpos : 0 < Module.finrank k V := by omega
    let hodd : Odd (Module.finrank k V) := ⟨m, hdim⟩
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    let O := oddSpecialOrthogonalClosedSubgroup Q b
    letI := S.carrierAlgebraicGroup
    letI := O.carrierAlgebraicGroup
    Function.Surjective (oddSpinCoverMorphism Q hQ hpos hodd b e).onPoints := by
  dsimp only
  intro y
  let hpos : 0 < Module.finrank k V := by omega
  let hodd : Odd (Module.finrank k V) := ⟨m, hdim⟩
  obtain ⟨x, hx⟩ := oddCliffordSpinAction_surjective Q m hm hQ hdim b
    (oddSpecialOrthogonalClosedSubgroupPoints Q b y)
  let g := (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e).symm x
  refine ⟨g, ?_⟩
  apply (oddSpecialOrthogonalClosedSubgroupPoints Q b).injective
  rw [oddSpinCoverMorphism_points Q hQ hpos hodd b e]
  rw [(oddSpinClosedSubgroupPoints Q hQ hpos hodd b e).apply_symm_apply]
  exact hx

/-- The point kernel of the algebraic Spin cover is finite. -/
public theorem oddSpinCoverMorphism_kernel_finite
    (m : ℕ) (hm : 2 ≤ m) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let hpos : 0 < Module.finrank k V := by omega
    let hodd : Odd (Module.finrank k V) := ⟨m, hdim⟩
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    let O := oddSpecialOrthogonalClosedSubgroup Q b
    letI := S.carrierAlgebraicGroup
    letI := O.carrierAlgebraicGroup
    Finite (oddSpinCoverMorphism Q hQ hpos hodd b e).kernel := by
  dsimp only
  let hpos : 0 < Module.finrank k V := by omega
  let hodd : Odd (Module.finrank k V) := ⟨m, hdim⟩
  let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
  let O := oddSpecialOrthogonalClosedSubgroup Q b
  letI := S.carrierAlgebraicGroup
  letI := O.carrierAlgebraicGroup
  let A := oddCliffordSpinAction Q b hodd
  letI : Finite A.ker := oddCliffordSpinActionKernelFinite Q m hm hQ hdim b
  let toActionKernel : (oddSpinCoverMorphism Q hQ hpos hodd b e).kernel →
      A.ker := fun z => ⟨oddSpinClosedSubgroupPoints Q hQ hpos hodd b e z.1, by
    apply MonoidHom.mem_ker.mpr
    have hz := MonoidHom.mem_ker.mp z.2
    have hz' := congrArg (oddSpecialOrthogonalClosedSubgroupPoints Q b) hz
    rw [oddSpinCoverMorphism_points Q hQ hpos hodd b e] at hz'
    simpa [A] using hz'⟩
  exact Finite.of_injective toActionKernel fun a c hac => by
    apply Subtype.ext
    apply (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e).injective
    exact congrArg Subtype.val hac

/-- The Clifford-conjugation morphism is the odd Spin isogeny. -/
public theorem oddSpinCoverMorphism_isIsogeny
    (m : ℕ) (hm : 2 ≤ m) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let hpos : 0 < Module.finrank k V := by omega
    let hodd : Odd (Module.finrank k V) := ⟨m, hdim⟩
    let S := oddSpinClosedSubgroup Q hQ hpos hodd b e
    let O := oddSpecialOrthogonalClosedSubgroup Q b
    letI := S.carrierAlgebraicGroup
    letI := O.carrierAlgebraicGroup
    IsIsogeny (oddSpinCoverMorphism Q hQ hpos hodd b e) := by
  dsimp only
  exact ⟨oddSpinCoverMorphism_surjective Q m hm hQ hdim b e,
    oddSpinCoverMorphism_kernel_finite Q m hm hQ hdim b e⟩

/-- The concrete odd orthogonal model assembled from the closed Spin and SO
carriers and their Clifford-conjugation isogeny. -/
public noncomputable def oddOrthogonalModel
    (m : ℕ) (hm : 2 ≤ m) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) : OddOrthogonalModel Q := by
  let hpos : 0 < Module.finrank k V := by omega
  let hodd : Odd (Module.finrank k V) := ⟨m, hdim⟩
  exact {
    basis := b
    cliffordBasis := e
    spin := oddSpinClosedSubgroup Q hQ hpos hodd b e
    spin_carrier := oddSpinClosedSubgroup_carrier Q hQ hpos hodd b e
    specialOrthogonal := oddSpecialOrthogonalClosedSubgroup Q b
    specialOrthogonal_carrier := oddSpecialOrthogonalClosedSubgroup_carrier Q b
    spinPoints := oddSpinClosedSubgroupPoints Q hQ hpos hodd b e
    specialOrthogonalPoints := oddSpecialOrthogonalClosedSubgroupPoints Q b
    specialOrthogonalLinear_points :=
      oddSpecialOrthogonalClosedSubgroup_linear_points Q b
    spinAction := oddCliffordSpinAction Q b hodd
    spinAction_clifford := oddCliffordSpinAction_spec Q b hodd
    spinCover := oddSpinCoverMorphism Q hQ hpos hodd b e
    spinCoverIsogeny := oddSpinCoverMorphism_isIsogeny Q m hm hQ hdim b e
    spinCover_points := by
      intro x
      rw [oddSpinCoverMorphism_points Q hQ hpos hodd b e]
      rw [(oddSpinClosedSubgroupPoints Q hQ hpos hodd b e).apply_symm_apply]
  }

end Theory.AlgebraicGroup
