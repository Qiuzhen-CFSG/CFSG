module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Stabilizers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Complementary-wedge duality on the binary exterior three-space

The ordered coordinates `[v₂₃, v₁₃, v₁₂]` identify Λ²Γ₃ with F₂³. Its
parabolic action is the inverse transpose of the literal upper-left SL₃ block.
The determinant of that block is one: its inverse is the block of the inverse
parabolic element, and every nonzero scalar in F₂ is one. The three-by-three
adjugate formula identifies its cofactors with the exterior minors; the signs
vanish in characteristic two.

We construct the inverse-transpose actor automorphism and the resulting natural
intertwiner, both for the three-space parabolic and for the literal exterior
stabilizer of V₃. The actor twist is explicit. Transport to the source residual
quotient is a separate Levi-quotient application of these intertwiners.

Source: Aschbacher–Smith, Lemma 12.5.2(2), printed p.817/PDF p.834.
-/

@[expose] public section

open scoped BigOperators
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The literal upper-left three-by-three block of an SL₅ matrix. -/
def upperThreeBlock (g : Group) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => g.val i.castSucc.castSucc j.castSucc.castSucc

@[simp] theorem upperThreeBlock_one : upperThreeBlock 1 = 1 := by
  ext i j
  simp [upperThreeBlock, Matrix.one_apply]

/-- A right factor preserving Γ₃ makes extraction of the upper block multiplicative. -/
theorem upperThreeBlock_mul (g h : Group) (hh : h ∈ parabolic 3) :
    upperThreeBlock (g * h) = upperThreeBlock g * upperThreeBlock h := by
  ext i j
  change (∑ k : Fin 5, g.val i.castSucc.castSucc k * h.val k j.castSucc.castSucc) =
    ∑ k : Fin 3, g.val i.castSucc.castSucc k.castSucc.castSucc *
      h.val k.castSucc.castSucc j.castSucc.castSucc
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have h3 : h.val 3 j.castSucc.castSucc = 0 :=
    (mem_parabolic_iff_lowerLeft_zero 3 h).mp hh _ _ (by decide) j.isLt
  have h4 : h.val 4 j.castSucc.castSucc = 0 :=
    (mem_parabolic_iff_lowerLeft_zero 3 h).mp hh _ _ (by decide) j.isLt
  simp only [show (Fin.last 3).castSucc = (3 : Fin 5) from rfl,
    show Fin.last 4 = (4 : Fin 5) from rfl, h3, h4, mul_zero, add_zero]

/-- The upper block of the three-space parabolic has determinant one over F₂. -/
theorem upperThreeBlock_det (g : Group) (hg : g ∈ parabolic 3) :
    (upperThreeBlock g).det = 1 := by
  have he := congrArg Matrix.det
    (upperThreeBlock_mul g g⁻¹ ((parabolic 3).inv_mem hg))
  rw [mul_inv_cancel, upperThreeBlock_one, Matrix.det_one, Matrix.det_mul] at he
  exact (by decide : ∀ a b : ZMod 2, a * b = 1 → a = 1) _ _ he.symm

/-- The upper-left block as an actual SL₃-valued homomorphism. -/
def upperThreeProjection : parabolic 3 →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun g := ⟨upperThreeBlock g.val, upperThreeBlock_det g.val g.property⟩
  map_one' := Subtype.ext upperThreeBlock_one
  map_mul' g h := Subtype.ext (upperThreeBlock_mul g.val h.val h.property)

@[simp] theorem upperThreeProjection_val (g : parabolic 3) :
    (upperThreeProjection g).val = upperThreeBlock g.val := rfl

private theorem three_transpose_inv (x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Matrix.SpecialLinearGroup.transpose x⁻¹ =
      (Matrix.SpecialLinearGroup.transpose x)⁻¹ := by
  apply Subtype.ext
  exact Matrix.adjugate_transpose _

/-- The involutory contragredient automorphism of the SL₃ actor. -/
def threeInverseTranspose : MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) where
  toFun x := Matrix.SpecialLinearGroup.transpose x⁻¹
  invFun x := Matrix.SpecialLinearGroup.transpose x⁻¹
  left_inv x := by
    dsimp only
    rw [three_transpose_inv]
    change x⁻¹⁻¹ = x
    exact inv_inv x
  right_inv x := by
    dsimp only
    rw [three_transpose_inv]
    change x⁻¹⁻¹ = x
    exact inv_inv x
  map_mul' x y := by
    apply Subtype.ext
    change ((x * y)⁻¹).val.transpose = (x⁻¹).val.transpose * (y⁻¹).val.transpose
    rw [mul_inv_rev]
    exact Matrix.transpose_mul _ _

@[simp] theorem threeInverseTranspose_val
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    (threeInverseTranspose g).val = (g⁻¹).val.transpose := rfl

@[simp] theorem threeInverseTranspose_involutive
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    threeInverseTranspose (threeInverseTranspose g) = g :=
  threeInverseTranspose.left_inv g

/-- The block projection twisted by inverse transpose, used for naturality on V₃. -/
def threeNaturalProjection : parabolic 3 →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  threeInverseTranspose.toMonoidHom.comp upperThreeProjection

@[simp] theorem threeNaturalProjection_val (g : parabolic 3) :
    (threeNaturalProjection g).val = ((upperThreeProjection g)⁻¹).val.transpose := rfl

/-- Complementary-wedge coordinates, ordered as 23, 13, 12. -/
noncomputable def V₃Equiv : V₃ ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := ![coordinates v.val 4, coordinates v.val 1, coordinates v.val 0]
  invFun w := ⟨coordinates.symm ![w 2, w 1, 0, 0, w 0, 0, 0, 0, 0, 0], by
    apply (mem_coordinateSpan _ _).mpr
    intro i hi
    fin_cases i <;> simp_all [-coordinates_apply]⟩
  left_inv v := by
    apply Subtype.ext
    apply coordinates.injective
    have h := (mem_coordinateSpan _ _).mp v.property
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    have h5 := h 5 (by decide)
    have h6 := h 6 (by decide)
    have h7 := h 7 (by decide)
    have h8 := h 8 (by decide)
    have h9 := h 9 (by decide)
    ext i
    fin_cases i <;> simp [-coordinates_apply, h2, h3, h5, h6, h7, h8, h9]
  right_inv w := by ext i; fin_cases i <;> simp [-coordinates_apply]
  map_add' v w := by ext i; fin_cases i <;> simp [-coordinates_apply]
  map_smul' c v := by ext i; fin_cases i <;> simp [-coordinates_apply]

@[simp] theorem V₃Equiv_apply (v : V₃) :
    V₃Equiv v = ![coordinates v.val 4, coordinates v.val 1, coordinates v.val 0] := rfl

@[simp] theorem V₃Equiv_symm_apply (w : Fin 3 → ZMod 2) :
    (V₃Equiv.symm w).val =
      coordinates.symm ![w 2, w 1, 0, 0, w 0, 0, 0, 0, 0, 0] := rfl

/-- The exterior minors are the transposed adjugate in complementary-wedge coordinates. -/
theorem V₃Equiv_action (g : Group) (hg : g ∈ parabolic 3) (v : V₃) :
    V₃Equiv ⟨exteriorAction 2 g v.val,
      (parabolic_three_le_stabilizer_V₃ hg v.val).mpr v.property⟩ =
      (upperThreeBlock g).adjugate.transpose.mulVec (V₃Equiv v) := by
  have hv := (mem_coordinateSpan _ _).mp v.property
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  have v5 := hv 5 (by decide)
  have v6 := hv 6 (by decide)
  have v7 := hv 7 (by decide)
  have v8 := hv 8 (by decide)
  have v9 := hv 9 (by decide)
  change ![coordinates (exteriorAction 2 g v.val) 4,
    coordinates (exteriorAction 2 g v.val) 1,
    coordinates (exteriorAction 2 g v.val) 0] = _
  rw [coordinates_action, Matrix.adjugate_fin_three]
  ext i
  fin_cases i <;>
    simp [V₃Equiv, upperThreeBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      actionMatrix, pair, v2, v3, v5, v6, v7, v8, v9, sub_eq_add_neg, ZMod.neg_eq_self_mod_two,
      -coordinates_apply] <;> ring

/-- The action is contragredient to the literal upper-left block. -/
theorem V₃Equiv_inverseTranspose (g : parabolic 3) (v : V₃) :
    V₃Equiv ⟨exteriorAction 2 g.val v.val,
      (parabolic_three_le_stabilizer_V₃ g.property v.val).mpr v.property⟩ =
      ((upperThreeProjection g)⁻¹).val.transpose.mulVec (V₃Equiv v) :=
  V₃Equiv_action g.val g.property v

/-- Naturality on V₃ with the explicitly twisted actor homomorphism. -/
theorem V₃Equiv_natural (g : parabolic 3) (v : V₃) :
    V₃Equiv ⟨exteriorAction 2 g.val v.val,
      (parabolic_three_le_stabilizer_V₃ g.property v.val).mpr v.property⟩ =
      specialLinearNatural 3 (threeNaturalProjection g) (V₃Equiv v) :=
  V₃Equiv_inverseTranspose g v

/-- Restriction of the genuine exterior action to the invariant V₃. -/
noncomputable def V₃Action : Representation (ZMod 2) (parabolic 3) V₃ where
  toFun g := (exteriorAction 2 g.val).restrict
    (fun v hv => (parabolic_three_le_stabilizer_V₃ g.property v).mpr hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change exteriorAction 2 1 v.val = v.val
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change exteriorAction 2 (g.val * h.val) v.val =
      exteriorAction 2 g.val (exteriorAction 2 h.val v.val)
    rw [map_mul]
    rfl

@[simp] theorem V₃Action_apply (g : parabolic 3) (v : V₃) :
    (V₃Action g v).val = exteriorAction 2 g.val v.val := rfl

/-- The coordinate equivalence intertwines the literal restricted representation. -/
theorem V₃Equiv_intertwines (g : parabolic 3) (v : V₃) :
    V₃Equiv (V₃Action g v) =
      specialLinearNatural 3 (threeNaturalProjection g) (V₃Equiv v) :=
  V₃Equiv_natural g v

/-- Use the proved equality of the exterior stabilizer and the three-space parabolic. -/
noncomputable def threeStabilizerToParabolic : exteriorStabilizer V₃ →* parabolic 3 :=
  Subgroup.inclusion (le_of_eq exteriorStabilizer_V₃_eq_parabolic)

/-- The twisted block projection on the literal exterior stabilizer of V₃. -/
noncomputable def threeStabilizerNaturalProjection :
    exteriorStabilizer V₃ →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  threeNaturalProjection.comp threeStabilizerToParabolic

/-- The literal stabilizer acts on V₃ by restriction of the exterior action. -/
noncomputable def V₃StabilizerAction :
    Representation (ZMod 2) (exteriorStabilizer V₃) V₃ where
  toFun g := (exteriorAction 2 g.val).restrict (fun v hv => (g.property v).mpr hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change exteriorAction 2 1 v.val = v.val
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change exteriorAction 2 (g.val * h.val) v.val =
      exteriorAction 2 g.val (exteriorAction 2 h.val v.val)
    rw [map_mul]
    rfl

@[simp] theorem V₃StabilizerAction_apply (g : exteriorStabilizer V₃) (v : V₃) :
    (V₃StabilizerAction g v).val = exteriorAction 2 g.val v.val := rfl

/-- Application to the source's literal V₃ stabilizer. This supplies the module
comparison in 12.5.2(2) before the separate residual/quotient transport. -/
theorem V₃Equiv_stabilizer_natural (g : exteriorStabilizer V₃) (v : V₃) :
    V₃Equiv (V₃StabilizerAction g v) =
      specialLinearNatural 3 (threeStabilizerNaturalProjection g) (V₃Equiv v) :=
  V₃Equiv_natural (threeStabilizerToParabolic g) v

end Representation.SL5ExteriorSquare
