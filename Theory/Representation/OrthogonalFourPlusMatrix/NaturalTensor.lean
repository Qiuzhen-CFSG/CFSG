module
public import Theory.Representation.OrthogonalFourPlusMatrix.AmbientSemilinear
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.NaturalComparison
public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Theory.Representation.BinaryOffender.PerfectNormalizer

/-!
# Natural tensors in determinant coordinates and their normalizer displacement

Outer-product coordinates carry the natural tensor to the literal action
M ↦ A M B⁻¹, retaining the first factor's given automorphism and the second
factor's inverse transpose. The scalar commutant constructs a field action
of the entire linear normalizer, including exchanges. A nonidentity linear
operator moves at least one dimension over this field; an operator moving
the field moves at least half the binary space. Thus every nonidentity
normalizer element moves at least the coefficient-field degree.

The original central Hall seed in Chapter 10 consumes the exact factor
marking and this bound. They are the module geometry used in the ambient
exclusion of the orthogonal-plus tensor; they do not exclude the tensor.
Source: Aschbacher--Smith 9.1.2(1), 9.2.3, printed pp.729--730,
and D.3.7, pp.197--199, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Matrix Representation
open Representation.QuadraticFourGroup.TensorClassification
open Representation.BinaryOffender
open scoped MatrixGroups TensorProduct
namespace ClassicalOrthogonal.FourPlusMatrix.NaturalTensor
variable {F : Type*} [Field F]

/-- Inverse transpose on the second special-linear factor. -/
def dual : MulAut SL(2,F) where
  toFun g := g⁻¹.transpose
  invFun g := g⁻¹.transpose
  left_inv g := by
    apply Subtype.ext
    change (g.val.adjugate.transpose).adjugate.transpose = g.val
    rw [← Matrix.adjugate_transpose, Matrix.transpose_transpose,
      Matrix.adjugate_adjugate _ (by simp), g.det_coe]
    simp
  right_inv g := by
    apply Subtype.ext
    change (g.val.adjugate.transpose).adjugate.transpose = g.val
    rw [← Matrix.adjugate_transpose, Matrix.transpose_transpose,
      Matrix.adjugate_adjugate _ (by simp), g.det_coe]
    simp
  map_mul' g h := by
    apply Subtype.ext
    change ((g*h)⁻¹).val.transpose = (g⁻¹).val.transpose * (h⁻¹).val.transpose
    rw [_root_.mul_inv_rev]
    exact Matrix.transpose_mul _ _

/-- The right inverse in determinant coordinates is the original transpose. -/
theorem dual_inv_val (g : SL(2,F)) : (dual g)⁻¹.val = g.val.transpose := by
  change (g.val.adjugate.transpose).adjugate = g.val.transpose
  rw [← Matrix.adjugate_transpose, Matrix.adjugate_adjugate _ (by simp), g.det_coe]
  simp

/-- A pure tensor maps to its outer-product matrix. -/
def coordinates : ((Fin 2 → F) ⊗[F] (Fin 2 → F)) ≃ₗ[F] Mat (F := F) :=
  (TensorProduct.comm F (Fin 2 → F) (Fin 2 → F)).trans
    (TensorProduct.piScalarRight F F (Fin 2 → F) (Fin 2))

/-- The ordered factors are retained in the outer product. -/
theorem coordinates_tmul (x y : Fin 2 → F) :
    coordinates (x ⊗ₜ[F] y) = Matrix.vecMulVec x y := by
  ext i j
  change (TensorProduct.piScalarRight F F (Fin 2 → F) (Fin 2))
    (y ⊗ₜ[F] x) i j = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

/-- The original first-factor twist and the second-factor duality. -/
def marking (α : MulAut SL(2,F)) : MulAut (PairSL (F := F)) :=
  α.symm.prodCongr dual

/-- The natural tensor is the literal determinant representation along its marking. -/
def tensorEquiv (α : MulAut SL(2,F)) :
    (externalTensor
      ((SL2.BinarySmall.embeddedNatural (RingHom.id F)).comp α.symm.toMonoidHom)
      (SL2.BinarySmall.embeddedNatural (RingHom.id F))).Equiv
      (representation.comp (marking α).toMonoidHom) := by
  refine Representation.Equiv.mk coordinates ?_
  intro g
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simpa only [map_add] using congrArg₂ (· + ·) hu hv
  | tmul x y =>
    change coordinates ((α.symm g.1).val.mulVec x ⊗ₜ[F] g.2.val.mulVec y) =
      representation (marking α g) (coordinates (x ⊗ₜ[F] y))
    rw [coordinates_tmul,coordinates_tmul,representation_apply]
    change _ = (α.symm g.1).val * Matrix.vecMulVec x y * (dual g.2)⁻¹.val
    rw [dual_inv_val,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.vecMul_transpose]

variable [Algebra (ZMod 2) F]
/-- The same intertwiner after restriction to the binary prime field. -/
def binaryTensorEquiv (α : MulAut SL(2,F)) :
    (restrictScalars (k := ZMod 2) (externalTensor
      ((SL2.BinarySmall.embeddedNatural (RingHom.id F)).comp α.symm.toMonoidHom)
      (SL2.BinarySmall.embeddedNatural (RingHom.id F)))).Equiv
      ((restrictScalars (k := ZMod 2) (representation (F := F))).comp
        (marking α).toMonoidHom) :=
  Representation.Equiv.mk ((tensorEquiv α).toLinearEquiv.restrictScalars (ZMod 2))
    (fun g => by
      apply LinearMap.ext
      intro v
      exact LinearMap.congr_fun ((tensorEquiv α).isIntertwining' g) v)

variable [Finite F] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The entire normalizer acts semilinearly on the actual matrix coefficient field. -/
theorem normalizer_semilinear
    (σ : Representation (ZMod 2) (PairSL (F := F)) V) (hσ : Function.Injective σ)
    (e : MulAut (PairSL (F := F))) (f : V ≃ₗ[ZMod 2] Mat (F := F))
    (hf : ∀ g v, f (σ g v) = representation (e g) (f v)) :
    ∃ φ : linearNormalizer σ →* (F ≃+* F), ∀ a c v,
      f (normalizerRepresentation σ a (f.symm (c • f v))) =
        φ a c • f (normalizerRepresentation σ a v) := by
  let N := (actionImage σ).subgroupOf (linearNormalizer σ)
  let hN : actionImage σ ≤ linearNormalizer σ := (actionImage σ).le_normalizer
  let : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr le_rfl
  let b : N ≃* PairSL (F := F) :=
    ((Subgroup.subgroupOfEquivOfLe hN).trans (PerfectNormalizer.imageEquiv σ hσ).symm).trans e
  let ρ : Representation (ZMod 2) (linearNormalizer σ) (Mat (F := F)) :=
    f.conjRingEquiv.toMonoidHom.comp (normalizerRepresentation σ)
  have hnat (g : N) (v : Mat (F := F)) : ρ g v = matrixAction (b g) v := by
    let x := (PerfectNormalizer.imageEquiv σ hσ).symm
      (Subgroup.subgroupOfEquivOfLe hN g)
    have hx : σ.asGroupHom x = g.val.val := congrArg Subtype.val
      ((PerfectNormalizer.imageEquiv σ hσ).apply_symm_apply _)
    change f (g.val.val.val (f.symm v)) = representation (e x) v
    rw [←hx]
    change f (σ x (f.symm v)) = representation (e x) v
    rw [hf,f.apply_symm_apply]
  obtain ⟨φ,hφ⟩ := normal_ambient_semilinear N b ρ hnat
  refine ⟨φ,fun a c v => ?_⟩
  have hh := hφ a c (f v)
  change f (normalizerRepresentation σ a (f.symm (c • f v))) =
    φ a c • f (normalizerRepresentation σ a (f.symm (f v))) at hh
  simpa only [f.symm_apply_apply] using hh

/-- Every nonidentity semilinear operator on four-space moves at least the field degree. -/
theorem semilinear_displacement_ge
    (t : Mat (F := F) ≃ₗ[ZMod 2] Mat (F := F))
    (φ : F ≃+* F) (hφ : ∀ c v, t (c • v) = φ c • t v)
    (ht : t ≠ 1) :
    Module.finrank (ZMod 2) F ≤
      Representation.BinaryOffender.NaturalTensor.operatorFixedCodim t.toLinearMap := by
  open Representation.BinaryOffender.NaturalTensor in
  by_cases hlin : ∀ c : F, φ c = c
  · let tF : Mat (F := F) →ₗ[F] Mat (F := F) :=
      { toFun := t, map_add' := t.map_add, map_smul' := by intro c v; exact (hφ c v).trans (by rw [hlin]; rfl) }
    let eF := LinearEquiv.ofBijective tF t.bijective
    have heF : eF.restrictScalars (ZMod 2) = t := by ext v; rfl
    have hd := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) eF
    rw [heF] at hd
    have hp : 0 < Module.finrank F (eF.toLinearMap - LinearMap.id).range := by
      by_contra! hz
      have hz' : eF.toLinearMap - LinearMap.id = 0 :=
        LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz))
      have he : eF = 1 := LinearEquiv.toLinearMap_injective (sub_eq_zero.mp hz')
      apply ht
      rw [←heF,he]
      rfl
    change _ ≤ Module.finrank (ZMod 2) (t.toLinearMap - LinearMap.id).range
    rw [hd]
    exact Nat.le_mul_of_pos_right _ hp
  · push Not at hlin
    have hb := finrank_le_twice_operatorFixedCodim t.toLinearMap φ.toRingHom hlin hφ
    have hd : Module.finrank (ZMod 2) (Mat (F := F)) = Module.finrank (ZMod 2) F * 4 := by
      rw [←Module.finrank_mul_finrank (ZMod 2) F]
      congr 1
      change Module.finrank F (Matrix (Fin 2) (Fin 2) F) = 4
      rw [Module.finrank_matrix]
      norm_num
    rw [hd] at hb
    omega

/-- The displacement bound on the original carrier, with its normalizer unchanged. -/
theorem normalizer_displacement_ge
    (σ : Representation (ZMod 2) (PairSL (F := F)) V) (hσ : Function.Injective σ)
    (e : MulAut (PairSL (F := F))) (f : V ≃ₗ[ZMod 2] Mat (F := F))
    (hf : ∀ g v, f (σ g v) = representation (e g) (f v))
    (a : linearNormalizer σ) (ha : a ≠ 1) :
    Module.finrank (ZMod 2) F ≤
      Representation.BinaryOffender.NaturalTensor.operatorFixedCodim (normalizerRepresentation σ a) := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.equiv f.symm
  obtain ⟨φ,hφ⟩ := normalizer_semilinear σ hσ e f hf
  let u := LinearMap.GeneralLinearGroup.toLinearEquiv a.val
  let t := f.symm.trans (u.trans f)
  have ht : t ≠ 1 := by
    intro he
    apply ha
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply f.injective
    have hh := LinearEquiv.congr_fun he (f v)
    change f (a.val.val v) = f v
    change f (a.val.val (f.symm (f v))) = f v at hh
    simpa only [f.symm_apply_apply] using hh
  have htφ (c : F) (v : Mat (F := F)) : t (c • v) = φ a c • t v := by
    have hh := hφ a c (f.symm v)
    change f (a.val.val (f.symm (c • v))) = φ a c • f (a.val.val (f.symm v))
    change f (a.val.val (f.symm (c • f (f.symm v)))) =
      φ a c • f (a.val.val (f.symm v)) at hh
    simpa only [f.apply_symm_apply] using hh
  have hb := semilinear_displacement_ge t (φ a) htφ ht
  have hr := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
    (normalizerRepresentation σ a) t.toLinearMap f (fun v => by
      change f (u v) = f (u (f.symm (f v)))
      rw [f.symm_apply_apply])
  exact hb.trans_eq hr.symm
end ClassicalOrthogonal.FourPlusMatrix.NaturalTensor
