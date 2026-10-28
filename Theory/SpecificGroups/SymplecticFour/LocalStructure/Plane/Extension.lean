module

public import Theory.SpecificGroups.SymplecticFour.LocalFactors
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.CharP.Two

/-!
# The actual plane-local extension in symplectic four-space

Restriction to the standard isotropic plane is its upper-left matrix block.
The determinant character therefore gives a surjection from the published
`planeLocal` to SL₂, with the explicit section `diag(A,(A⁻¹)ᵀ)`.

The kernel consists exactly of the shears `fromBlocks 1 B 0 1` with `B`
symmetric. Their multiplication is addition of symmetric matrices, so in
characteristic two the kernel is elementary abelian of exponent two.
Conjugation by a local element with upper-left block `A` sends `B` to `ABAᵀ`.
All these statements concern the original symplectic matrix subgroup.

This supplies the matrix extension calculation for Aschbacher--Smith,
F.1.12(I)(2), printed pp.262--264 of the combined manuscript of 1 March 2004.
The commutator generation and the central quotient's natural-module
identification are separate consequences of this congruence action.
-/

@[expose] public section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.Plane
noncomputable section
variable {F : Type*} [Field F]

/-- Restriction to the plane in its standard coordinates. -/
def upperLeft : planeParabolic (F := F) →* Matrix (Fin 2) (Fin 2) F where
  toFun g := g.val.val.toBlocks₁₁
  map_one' := by ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  map_mul' g h := by
    ext i j
    have hz := mem_planeParabolic_iff h.val |>.mp h.property
    simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, hz]

theorem upperLeft_eq_matrix (g : planeParabolic (F := F)) :
    upperLeft g = LinearMap.toMatrix'
      ((planeEquiv.toLinearMap).comp ((restriction (plane F) g).toLinearMap.comp
        planeEquiv.symm.toLinearMap)) := by
  ext i j
  change g.val.val (.inl i) (.inl j) =
    (g.val • (planeEquiv.symm (Pi.single j 1)).val) (.inl i)
  have he : ((planeEquiv (F := F)).symm (Pi.single j 1)).val = e j := by
    ext k
    change Sum.elim (Pi.single j (1 : F)) 0 k = (Pi.single (.inl j) (1 : F) : Vector F) k
    cases k <;> simp [Pi.single_apply]
  simp [he, smul_eq_mulVec, e, Matrix.mulVec_single]

theorem upperLeft_det (g : planeParabolic (F := F)) :
    (upperLeft g).det = (determinantCharacter (plane F) g : F) := by
  rw [upperLeft_eq_matrix, LinearMap.det_toMatrix']
  rw [LinearMap.det_conj]
  exact (LinearEquiv.coe_det _).symm

theorem mem_local_iff (g : Sp F) :
    g ∈ planeLocal ↔ ∃ _h : g ∈ planeParabolic,
      g.val.toBlocks₁₁.det = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    change determinantCharacter (plane F) x = 1 at hx
    exact (upperLeft_det ⟨x.val, x.property⟩).trans
      (congrArg (fun u : Fˣ => (u : F)) hx)
  · rintro ⟨h, hd⟩
    refine ⟨⟨g, h⟩, ?_, rfl⟩
    apply Units.ext
    change (determinantCharacter (plane F) ⟨g, h⟩ : F) = 1
    exact (upperLeft_det ⟨g, h⟩).symm.trans hd

/-- The determinant-one restriction map on the actual local factor. -/
def quotientMap : planeLocal (F := F) →* SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨g.val.val.toBlocks₁₁, ((mem_local_iff g.val).mp g.property).choose_spec⟩
  map_one' := by apply Subtype.ext; exact upperLeft.map_one
  map_mul' g h := by
    apply Subtype.ext
    exact upperLeft.map_mul ⟨g.val, planeLocal_le g.property⟩
      ⟨h.val, planeLocal_le h.property⟩

@[simp] theorem quotientMap_val (g : planeLocal (F := F)) :
    (quotientMap g).val = g.val.val.toBlocks₁₁ := rfl

/-- The block-diagonal symplectic lift of a special linear matrix. -/
def leviSp (A : SpecialLinearGroup (Fin 2) F) : Sp F :=
  ⟨fromBlocks A.val 0 0 (A⁻¹).valᵀ, by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp only [mul_zero, transpose_zero, zero_mul, transpose_transpose,
      sub_zero, true_and]
    rw [← transpose_mul]
    have h : (A⁻¹).val * A.val = 1 := congrArg Subtype.val (inv_mul_cancel A)
    rw [h, transpose_one]⟩

/-- The same lift lies in the determinant kernel. -/
def levi (A : SpecialLinearGroup (Fin 2) F) : planeLocal (F := F) :=
  ⟨leviSp A, mem_local_iff _ |>.mpr ⟨by
    rw [mem_planeParabolic_iff]
    intro i j
    rfl, A.property⟩⟩

@[simp] theorem quotientMap_levi (A : SpecialLinearGroup (Fin 2) F) :
    quotientMap (levi A) = A := rfl

theorem quotientMap_surjective : Function.Surjective (quotientMap (F := F)) :=
  fun A => ⟨levi A, rfl⟩

/-- The plane-local unipotent radical, as the kernel of restriction. -/
def radical : Subgroup (planeLocal (F := F)) := quotientMap.ker

instance radical_normal : (radical (F := F)).Normal := inferInstanceAs quotientMap.ker.Normal

/-- Additive symmetric matrices, the actual upper-right radical coordinates. -/
def symmetricMatrices (F : Type*) [Field F] : Submodule F (Matrix (Fin 2) (Fin 2) F) where
  carrier := {B | B.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' hB hC := hB.add hC
  smul_mem' a _ hB := hB.smul a

/-- The symplectic shear with a symmetric upper-right block. -/
def shearSp (B : symmetricMatrices F) : Sp F :=
  ⟨fromBlocks 1 B.val 0 1, by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp only [mul_zero, transpose_zero, zero_mul, transpose_one, one_mul, mul_one,
      sub_zero, and_true, true_and]
    exact B.property⟩

/-- Symmetric shears lie in the published determinant kernel. -/
def shear (B : symmetricMatrices F) : planeLocal (F := F) :=
  ⟨shearSp B, mem_local_iff _ |>.mpr ⟨by
    rw [mem_planeParabolic_iff]
    intro i j
    rfl, Matrix.det_one⟩⟩

@[simp] theorem quotientMap_shear (B : symmetricMatrices F) : quotientMap (shear B) = 1 := rfl

@[simp] theorem shear_zero : shear (0 : symmetricMatrices F) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact Matrix.fromBlocks_one

@[simp] theorem shear_add (B C : symmetricMatrices F) : shear (B + C) = shear B * shear C := by
  apply Subtype.ext
  apply Subtype.ext
  change fromBlocks 1 (B.val + C.val) 0 1 = fromBlocks 1 B.val 0 1 * fromBlocks 1 C.val 0 1
  simp [Matrix.fromBlocks_multiply, add_comm]

theorem radical_blocks (q : radical (F := F)) :
    q.val.val.val.toBlocks₁₁ = 1 ∧ q.val.val.val.toBlocks₂₁ = 0 ∧
      q.val.val.val.toBlocks₂₂ = 1 ∧ q.val.val.val.toBlocks₁₂.IsSymm := by
  have hA : q.val.val.val.toBlocks₁₁ = 1 :=
    congrArg Subtype.val (show quotientMap q.val = 1 from q.property)
  have hC : q.val.val.val.toBlocks₂₁ = 0 := by
    ext i j
    exact (mem_planeParabolic_iff _).mp (planeLocal_le q.val.property) i j
  have hs := q.val.val.property
  rw [← q.val.val.val.fromBlocks_toBlocks] at hs
  have hb := SymplecticGroup.fromBlocks_mem_iff.mp hs
  simp only [hA, hC, transpose_one, one_mul, mul_zero, transpose_zero, zero_mul,
    sub_zero, true_and] at hb
  have hD := hb.2
  have hB : q.val.val.val.toBlocks₁₂.IsSymm := by
    change _ᵀ = _
    simpa [hD] using hb.1
  exact ⟨hA, hC, hD, hB⟩

theorem radical_matrix (q : radical (F := F)) :
    q.val.val.val = fromBlocks 1 q.val.val.val.toBlocks₁₂ 0 1 := by
  nth_rw 1 [← q.val.val.val.fromBlocks_toBlocks]
  rw [(radical_blocks q).1, (radical_blocks q).2.1, (radical_blocks q).2.2.1]

/-- Coordinates identify the kernel with the additive group of symmetric matrices. -/
def radicalEquiv : radical (F := F) ≃* Multiplicative (symmetricMatrices F) where
  toFun q := Multiplicative.ofAdd ⟨q.val.val.val.toBlocks₁₂, (radical_blocks q).2.2.2⟩
  invFun B := ⟨shear B.toAdd, quotientMap_shear _⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact (radical_matrix q).symm
  right_inv B := rfl
  map_mul' q r := by
    apply Subtype.ext
    change (q.val.val.val * r.val.val.val).toBlocks₁₂ =
      q.val.val.val.toBlocks₁₂ + r.val.val.val.toBlocks₁₂
    rw [radical_matrix q, radical_matrix r]
    simp [Matrix.fromBlocks_multiply, add_comm]

@[simp] theorem radicalEquiv_apply (q : radical (F := F)) :
    (radicalEquiv q).toAdd.val = q.val.val.val.toBlocks₁₂ := rfl

@[simp] theorem radicalEquiv_symm_val (B : Multiplicative (symmetricMatrices F)) :
    (radicalEquiv.symm B).val = shear B.toAdd := rfl

theorem local_matrix (g : planeLocal (F := F)) :
    g.val.val = fromBlocks g.val.val.toBlocks₁₁ g.val.val.toBlocks₁₂ 0
      g.val.val.toBlocks₂₂ := by
  have hC : g.val.val.toBlocks₂₁ = 0 := by
    ext i j
    exact (mem_planeParabolic_iff _).mp (planeLocal_le g.property) i j
  nth_rw 1 [← g.val.val.fromBlocks_toBlocks]
  rw [hC]

theorem local_pairing (g : planeLocal (F := F)) :
    g.val.val.toBlocks₁₁ᵀ * g.val.val.toBlocks₂₂ = 1 := by
  have hs := g.val.property
  rw [local_matrix g] at hs
  simpa using (SymplecticGroup.fromBlocks_mem_iff.mp hs).2.2

/-- Congruence is the action on symmetric radical coordinates. -/
def congruence (A : SpecialLinearGroup (Fin 2) F) (B : symmetricMatrices F) :
    symmetricMatrices F :=
  ⟨A.val * B.val * A.valᵀ, by
    change (_ * _ * _)ᵀ = _
    rw [transpose_mul, transpose_mul, transpose_transpose, B.property]
    exact (Matrix.mul_assoc _ _ _).symm⟩

theorem conjugate_shear (g : planeLocal (F := F)) (B : symmetricMatrices F) :
    g * shear B * g⁻¹ = shear (congruence (quotientMap g) B) := by
  apply (mul_left_inj g).mp
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply Subtype.ext
  apply Subtype.ext
  change g.val.val * fromBlocks 1 B.val 0 1 =
    fromBlocks 1 (g.val.val.toBlocks₁₁ * B.val * g.val.val.toBlocks₁₁ᵀ) 0 1 * g.val.val
  conv_lhs => rw [local_matrix g]
  conv_rhs => rhs; rw [local_matrix g]
  simp only [Matrix.fromBlocks_multiply, mul_one, mul_zero, zero_mul, one_mul,
    add_zero, zero_add]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, local_pairing g, mul_one, add_comm]

/-- Conjugation by a local element, restricted to its normal radical. -/
def conjugate (g : planeLocal (F := F)) (q : radical (F := F)) : radical (F := F) :=
  ⟨g * q.val * g⁻¹, by
    change quotientMap (g * q.val * g⁻¹) = 1
    simp [show quotientMap q.val = 1 from q.property]⟩

theorem radicalEquiv_conjugate (g : planeLocal (F := F)) (q : radical (F := F)) :
    (radicalEquiv (conjugate g q)).toAdd =
      congruence (quotientMap g) (radicalEquiv q).toAdd := by
  have hq : q.val = shear (radicalEquiv q).toAdd := by
    apply Subtype.ext
    apply Subtype.ext
    exact radical_matrix q
  apply Subtype.ext
  change (g * q.val * g⁻¹).val.val.toBlocks₁₂ = _
  rw [hq, conjugate_shear]
  rfl

/-- The radical is abelian over every field. -/
theorem radical_mul_comm (q r : radical (F := F)) : q * r = r * q := by
  apply radicalEquiv.injective
  simp only [map_mul]
  exact mul_comm _ _

/-- In characteristic two every radical element squares to the identity. -/
theorem radical_sq [CharP F 2] (q : radical (F := F)) : q ^ 2 = 1 := by
  apply radicalEquiv.injective
  rw [map_pow, map_one, pow_two]
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  ext i j
  exact CharTwo.add_self_eq_zero _

instance radical_elementaryAbelian [CharP F 2] :
    IsElementaryAbelian 2 (radical (F := F)) where
  is_comm := ⟨radical_mul_comm⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr radical_sq

@[simp] theorem quotientMap_ker : (quotientMap (F := F)).ker = radical := rfl

@[simp] theorem levi_matrix (A : SpecialLinearGroup (Fin 2) F) :
    (levi A).val.val = fromBlocks A.val 0 0 (A⁻¹).valᵀ := rfl

@[simp] theorem shear_matrix (B : symmetricMatrices F) :
    (shear B).val.val = fromBlocks 1 B.val 0 1 := rfl

@[simp] theorem conjugate_val (g : planeLocal (F := F)) (q : radical (F := F)) :
    (conjugate g q).val = g * q.val * g⁻¹ := rfl

instance radical_nontrivial : Nontrivial (radical (F := F)) := by
  let B : symmetricMatrices F := ⟨1, Matrix.isSymm_one⟩
  let q : radical (F := F) := ⟨shear B, quotientMap_shear B⟩
  refine ⟨⟨q, 1, ?_⟩⟩
  intro h
  have hh := congrArg (fun r : radical (F := F) => r.val.val.val (.inl 0) (.inr 0)) h
  change (1 : F) = 0 at hh
  exact one_ne_zero hh

/-- The nontrivial elementary radical has exponent exactly two. -/
theorem radical_exponent [Finite F] [CharP F 2] :
    Monoid.exponent (radical (F := F)) = 2 :=
  IsElementaryAbelian.exponent_eq_prime

end
end Theory.SpecificGroups.SymplecticFour.Plane
