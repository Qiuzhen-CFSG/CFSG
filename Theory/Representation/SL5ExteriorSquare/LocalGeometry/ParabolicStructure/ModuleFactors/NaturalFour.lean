module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Stabilizers
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FixedSpaces
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Four-dimensional natural factors of the binary exterior square

The line parabolic acts on Γ₁ ∧ Γ by its lower-right SL₄ block. The
four-space parabolic acts on V/Λ²Γ₄ by its upper-left SL₄ block, in exterior
coordinates 3, 6, 8, 9. Both comparisons are actual linear equivalences with
pointwise intertwining identities.

The latter coordinates also identify the quotient, as an additive group, with
the shared last-column shear subgroup. Multiplying the literal matrices proves
that this isomorphism intertwines the exterior action with conjugation. No
identification of the shear subgroup with a two-core is used here.

The block determinants are one because each block has an inverse and the base
field is F₂. A nonzero singleton diagonal entry is likewise one. These facts
reduce the exterior minors to the asserted natural matrices.

Source: Aschbacher–Smith, Lemma 12.5.2(3–4), printed p.817/PDF p.834.
-/

@[expose] public section

open scoped BigOperators
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The literal upper-left four-by-four block. -/
def upperFourBlock (g : Group) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => g.val i.castSucc j.castSucc

/-- The literal lower-right four-by-four block. -/
def lowerFourBlock (g : Group) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => g.val i.succ j.succ

theorem parabolic_four_last_diagonal (g : Group) (hg : g ∈ parabolic 4) :
    g.val 4 4 = 1 := by
  have hz := (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg
  have h0 := hz 4 0 (by decide) (by decide)
  have h1 := hz 4 1 (by decide) (by decide)
  have h2 := hz 4 2 (by decide) (by decide)
  have h3 := hz 4 3 (by decide) (by decide)
  apply (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1)
  intro h4
  apply g.det_ne_zero
  apply Matrix.det_eq_zero_of_row_eq_zero 4
  intro j
  fin_cases j <;> assumption

theorem parabolic_one_first_diagonal (g : Group) (hg : g ∈ parabolic 1) :
    g.val 0 0 = 1 := by
  have hz := (mem_parabolic_iff_lowerLeft_zero 1 g).mp hg
  have h1 := hz 1 0 (by decide) (by decide)
  have h2 := hz 2 0 (by decide) (by decide)
  have h3 := hz 3 0 (by decide) (by decide)
  have h4 := hz 4 0 (by decide) (by decide)
  apply (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1)
  intro h0
  apply g.det_ne_zero
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro j
  fin_cases j <;> assumption

@[simp] theorem upperFourBlock_one : upperFourBlock 1 = 1 := by
  ext i j
  simp [upperFourBlock, Matrix.one_apply]

@[simp] theorem lowerFourBlock_one : lowerFourBlock 1 = 1 := by
  ext i j
  simp [lowerFourBlock, Matrix.one_apply]

theorem upperFourBlock_mul (g h : Group) (hh : h ∈ parabolic 4) :
    upperFourBlock (g * h) = upperFourBlock g * upperFourBlock h := by
  ext i j
  change (∑ k : Fin 5, g.val i.castSucc k * h.val k j.castSucc) =
    ∑ k : Fin 4, g.val i.castSucc k.castSucc * h.val k.castSucc j.castSucc
  rw [Fin.sum_univ_castSucc]
  have hz : h.val (Fin.last 4) j.castSucc = 0 :=
    (mem_parabolic_iff_lowerLeft_zero 4 h).mp hh _ _ (by decide) j.isLt
  rw [hz, mul_zero, add_zero]

theorem lowerFourBlock_mul (g h : Group) (hg : g ∈ parabolic 1) :
    lowerFourBlock (g * h) = lowerFourBlock g * lowerFourBlock h := by
  ext i j
  change (∑ k : Fin 5, g.val i.succ k * h.val k j.succ) =
    ∑ k : Fin 4, g.val i.succ k.succ * h.val k.succ j.succ
  rw [Fin.sum_univ_succ]
  have hz : g.val i.succ 0 = 0 :=
    (mem_parabolic_iff_lowerLeft_zero 1 g).mp hg _ _ (by simp) (by decide)
  rw [hz, zero_mul, zero_add]

theorem upperFourBlock_det (g : Group) (hg : g ∈ parabolic 4) :
    (upperFourBlock g).det = 1 := by
  have he := congrArg Matrix.det
    (upperFourBlock_mul g g⁻¹ ((parabolic 4).inv_mem hg))
  rw [mul_inv_cancel, upperFourBlock_one, Matrix.det_one, Matrix.det_mul] at he
  exact (by decide : ∀ a b : ZMod 2, a * b = 1 → a = 1) _ _ he.symm

theorem lowerFourBlock_det (g : Group) (hg : g ∈ parabolic 1) :
    (lowerFourBlock g).det = 1 := by
  have he := congrArg Matrix.det (lowerFourBlock_mul g g⁻¹ hg)
  rw [mul_inv_cancel, lowerFourBlock_one, Matrix.det_one, Matrix.det_mul] at he
  exact (by decide : ∀ a b : ZMod 2, a * b = 1 → a = 1) _ _ he.symm

/-- The upper block as an actual determinant-one matrix, with its multiplication law. -/
def upperFourProjection : parabolic 4 →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) where
  toFun g := ⟨upperFourBlock g.val, upperFourBlock_det g.val g.property⟩
  map_one' := Subtype.ext upperFourBlock_one
  map_mul' g h := Subtype.ext (upperFourBlock_mul g.val h.val h.property)

/-- The lower block as an actual determinant-one matrix, with its multiplication law. -/
def lowerFourProjection : parabolic 1 →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) where
  toFun g := ⟨lowerFourBlock g.val, lowerFourBlock_det g.val g.property⟩
  map_one' := Subtype.ext lowerFourBlock_one
  map_mul' g h := Subtype.ext (lowerFourBlock_mul g.val h.val g.property)

/-- The four wedge coordinates in Γ₁ ∧ Γ, in their source order. -/
noncomputable def V₄Equiv : V₄ ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun v := ![coordinates v.val 0, coordinates v.val 1, coordinates v.val 2,
    coordinates v.val 3]
  invFun w := ⟨coordinates.symm ![w 0, w 1, w 2, w 3, 0, 0, 0, 0, 0, 0], by
    apply (mem_coordinateSpan _ _).mpr
    intro i hi
    fin_cases i <;> simp_all [-coordinates_apply]⟩
  left_inv v := by
    apply Subtype.ext
    apply coordinates.injective
    have h := (mem_coordinateSpan _ _).mp v.property
    have h4 := h 4 (by decide)
    have h5 := h 5 (by decide)
    have h6 := h 6 (by decide)
    have h7 := h 7 (by decide)
    have h8 := h 8 (by decide)
    have h9 := h 9 (by decide)
    ext i
    fin_cases i <;> simp [-coordinates_apply, h4, h5, h6, h7, h8, h9]
  right_inv w := by ext i; fin_cases i <;> simp [-coordinates_apply]
  map_add' v w := by ext i; fin_cases i <;> simp [-coordinates_apply]
  map_smul' c v := by ext i; fin_cases i <;> simp [-coordinates_apply]

/-- Pointwise intertwining on the actual invariant subspace Γ₁ ∧ Γ. -/
theorem V₄Equiv_action (g : Group) (hg : g ∈ parabolic 1) (v : V₄) :
    V₄Equiv ⟨exteriorAction 2 g v.val,
      (parabolic_one_le_stabilizer_V₄ hg v.val).mpr v.property⟩ =
      (lowerFourBlock g).mulVec (V₄Equiv v) := by
  have hz := (mem_parabolic_iff_lowerLeft_zero 1 g).mp hg
  have h1 := hz 1 0 (by decide) (by decide)
  have h2 := hz 2 0 (by decide) (by decide)
  have h3 := hz 3 0 (by decide) (by decide)
  have h4 := hz 4 0 (by decide) (by decide)
  have hd := parabolic_one_first_diagonal g hg
  have hv := (mem_coordinateSpan _ _).mp v.property
  have v4 := hv 4 (by decide)
  have v5 := hv 5 (by decide)
  have v6 := hv 6 (by decide)
  have v7 := hv 7 (by decide)
  have v8 := hv 8 (by decide)
  have v9 := hv 9 (by decide)
  change ![coordinates (exteriorAction 2 g v.val) 0,
    coordinates (exteriorAction 2 g v.val) 1,
    coordinates (exteriorAction 2 g v.val) 2,
    coordinates (exteriorAction 2 g v.val) 3] = _
  rw [coordinates_action]
  ext i
  fin_cases i <;>
    simp [V₄Equiv, lowerFourBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      actionMatrix, pair, h1, h2, h3, h4, hd, v4, v5, v6, v7, v8, v9, -coordinates_apply]

/-- The exterior action induces the upper-block action on the four quotient coordinates. -/
theorem shearQuotient_action (g : Group) (hg : g ∈ parabolic 4) (v : V) :
    shearQuotient (exteriorAction 2 g v) =
      (upperFourBlock g).mulVec (shearQuotient v) := by
  have hz := (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg
  have h0 := hz 4 0 (by decide) (by decide)
  have h1 := hz 4 1 (by decide) (by decide)
  have h2 := hz 4 2 (by decide) (by decide)
  have h3 := hz 4 3 (by decide) (by decide)
  have hd := parabolic_four_last_diagonal g hg
  change ![coordinates (exteriorAction 2 g v) 3,
    coordinates (exteriorAction 2 g v) 6,
    coordinates (exteriorAction 2 g v) 8,
    coordinates (exteriorAction 2 g v) 9] = _
  rw [coordinates_action]
  ext i
  fin_cases i <;>
    simp [shearQuotient, upperFourBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      actionMatrix, pair, h0, h1, h2, h3, hd, -coordinates_apply]

/-- Conjugation acts on the literal last-column shear parameter by the upper block. -/
theorem conjugate_shear (g : Group) (hg : g ∈ parabolic 4) (u : ShearParameter) :
    g * shear u * g⁻¹ = shear ((upperFourBlock g).mulVec u) := by
  have hz := (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg
  have h0 := hz 4 0 (by decide) (by decide)
  have h1 := hz 4 1 (by decide) (by decide)
  have h2 := hz 4 2 (by decide) (by decide)
  have h3 := hz 4 3 (by decide) (by decide)
  have hd := parabolic_four_last_diagonal g hg
  have he : g * shear u = shear ((upperFourBlock g).mulVec u) * g := by
    apply Subtype.ext
    ext i j
    change ∑ k, g.val i k * (shear u).val k j =
      ∑ k, (shear ((upperFourBlock g).mulVec u)).val i k * g.val k j
    simp only [matrix_shear]
    fin_cases i <;> fin_cases j <;>
      simp [upperFourBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        h0, h1, h2, h3, hd] <;> ring
  rw [he, mul_assoc, mul_inv_cancel, mul_one]

/-- The action induced on the actual quotient by Λ²Γ₄. -/
noncomputable def quotientSixAction : Representation (ZMod 2) (parabolic 4) (V ⧸ V₆) where
  toFun g := V₆.mapQ V₆ (exteriorAction 2 g.val) (by
    intro v hv
    exact (parabolic_four_le_stabilizer_V₆ g.property v).mpr hv)
  map_one' := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      change V₆.mkQ (exteriorAction 2 1 v) = V₆.mkQ v
      simp
  map_mul' g h := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      change V₆.mkQ (exteriorAction 2 (g.val * h.val) v) =
        V₆.mkQ (exteriorAction 2 g.val (exteriorAction 2 h.val v))
      rw [map_mul]
      rfl

@[simp] theorem quotientSixAction_mk (g : parabolic 4) (v : V) :
    quotientSixAction g (V₆.mkQ v) = V₆.mkQ (exteriorAction 2 g.val v) := rfl

/-- The quotient coordinates intertwine the induced action with the actual upper block. -/
theorem shearQuotientEquiv_action (g : parabolic 4) (v : V ⧸ V₆) :
    shearQuotientEquiv (quotientSixAction g v) =
      (upperFourBlock g.val).mulVec (shearQuotientEquiv v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change shearQuotient (exteriorAction 2 g.val v) =
      (upperFourBlock g.val).mulVec (shearQuotient v)
    exact shearQuotient_action g.val g.property v

/-- The literal quotient-to-shear group isomorphism. -/
noncomputable def quotientSixShearEquiv : Multiplicative (V ⧸ V₆) ≃* shearSubgroup :=
  (AddEquiv.toMultiplicative shearQuotientEquiv.toAddEquiv).trans shearEquiv

@[simp] theorem quotientSixShearEquiv_apply (v : V ⧸ V₆) :
    (quotientSixShearEquiv (Multiplicative.ofAdd v) : Group) =
      shear (shearQuotientEquiv v) := rfl

/-- The quotient-to-shear isomorphism intertwines exterior action and conjugation. -/
theorem quotientSixShearEquiv_action (g : parabolic 4) (v : V ⧸ V₆) :
    (quotientSixShearEquiv (Multiplicative.ofAdd (quotientSixAction g v)) : Group) =
      g.val * (quotientSixShearEquiv (Multiplicative.ofAdd v) : Group) * g.val⁻¹ := by
  simp only [quotientSixShearEquiv_apply, shearQuotientEquiv_action,
    conjugate_shear g.val g.property]

/-- Naturality on Γ₁ ∧ Γ uses the lower-right SL₄ block. -/
theorem V₄Equiv_natural (g : parabolic 1) (v : V₄) :
    V₄Equiv ⟨exteriorAction 2 g.val v.val,
      (parabolic_one_le_stabilizer_V₄ g.property v.val).mpr v.property⟩ =
      specialLinearNatural 4 (lowerFourProjection g) (V₄Equiv v) :=
  V₄Equiv_action g.val g.property v

/-- Naturality on V/Λ²Γ₄ uses the upper-left SL₄ block. -/
theorem shearQuotientEquiv_natural (g : parabolic 4) (v : V ⧸ V₆) :
    shearQuotientEquiv (quotientSixAction g v) =
      specialLinearNatural 4 (upperFourProjection g) (shearQuotientEquiv v) :=
  shearQuotientEquiv_action g v

end Representation.SL5ExteriorSquare
