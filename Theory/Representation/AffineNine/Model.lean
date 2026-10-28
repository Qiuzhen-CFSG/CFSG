module

public import Theory.SpecificGroups.SL2.Affine
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The concrete affine-nine group model

The affine-nine argument uses the actual semidirect product of the ternary
translation plane by its linear complement. This module records the natural
column action, the dual inverse-transpose action on character weights, and the
injectivity of an elementary two-subgroup's projection to the complement.
-/

open Matrix
open scoped MatrixGroups

public section

namespace Representation.AffineNine
abbrev Plane := Fin 2 → ZMod 3
abbrev Translation := Multiplicative Plane
abbrev LinearGroup := GL (Fin 2) (ZMod 3)
abbrev SpecialLinear := SL(2, ZMod 3)

@[expose] def naturalAction : LinearGroup →* MulAut Translation where
  toFun g := (GeneralLinearGroup.toLin g).toLinearEquiv.toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    change (GeneralLinearGroup.toLin (1 : LinearGroup) : Module.End (ZMod 3) Plane) v.toAdd = v.toAdd
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v : 1
    change (GeneralLinearGroup.toLin (g * h) : Module.End (ZMod 3) Plane) v.toAdd =
      (GeneralLinearGroup.toLin g : Module.End (ZMod 3) Plane)
        ((GeneralLinearGroup.toLin h : Module.End (ZMod 3) Plane) v.toAdd)
    rw [map_mul]
    rfl

@[simp] theorem naturalAction_apply (g : LinearGroup) (v : Translation) :
    (naturalAction g v).toAdd = g.val *ᵥ v.toAdd := rfl

abbrev Affine {L : Type*} [Group L] (j : L →* LinearGroup) :=
  Translation ⋊[naturalAction.comp j] L
abbrev Full := Affine (MonoidHom.id LinearGroup)
abbrev Special := Affine (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)

def specialEquiv : Special ≃* Matrix.SL2.Affine (ZMod 3) :=
  SemidirectProduct.congr (MulEquiv.refl Translation) (MulEquiv.refl SpecialLinear) (by
    intro g
    ext v : 1
    rfl)

variable {L : Type*} [Group L] (j : L →* LinearGroup)

@[expose] def linearPart : Affine j →* LinearGroup := j.comp SemidirectProduct.rightHom

@[simp] theorem linearPart_apply (g : Affine j) : linearPart j g = j g.right := rfl

theorem conjugate_translation (g : Affine j) (v : Translation) :
    g * SemidirectProduct.inl v * g⁻¹ =
      SemidirectProduct.inl (naturalAction (linearPart j g) v) := by
  apply SemidirectProduct.ext
  · simp [mul_comm, mul_left_comm, linearPart]
  · simp

@[expose] def dualPerm (g : LinearGroup) : Equiv.Perm Plane where
  toFun w := g⁻¹.val.transpose *ᵥ w
  invFun w := g.val.transpose *ᵥ w
  left_inv w := by
    change g.val.transpose *ᵥ ((g⁻¹).val.transpose *ᵥ w) = w
    rw [Matrix.mulVec_mulVec w g.val.transpose (g⁻¹).val.transpose, ← Matrix.transpose_mul]
    simp
  right_inv w := by
    change (g⁻¹).val.transpose *ᵥ (g.val.transpose *ᵥ w) = w
    rw [Matrix.mulVec_mulVec w (g⁻¹).val.transpose g.val.transpose, ← Matrix.transpose_mul]
    simp

@[simp] theorem dualPerm_apply (g : LinearGroup) (w : Plane) :
    dualPerm g w = g⁻¹.val.transpose *ᵥ w := rfl

@[simp] theorem dualPerm_zero (g : LinearGroup) : dualPerm g 0 = 0 := by
  simp [dualPerm]

theorem translation_cube (v : Translation) : v ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  change 3 • v.toAdd = 0
  ext i
  change 3 • v.toAdd i = 0
  exact (show ∀ x : ZMod 3, (3 : ℕ) • x = 0 by decide) (v.toAdd i)

theorem linearPart_injective_on_elementary (hj : Function.Injective j)
    (A : Subgroup (Affine j)) [IsElementaryAbelian 2 A] :
    Function.Injective ((linearPart j).comp A.subtype) := by
  apply (((linearPart j).comp A.subtype).ker_eq_bot_iff).mp
  apply le_bot_iff.mp
  intro a ha
  have hr : a.val.right = 1 := hj (by simpa [linearPart] using ha)
  have he : (a : Affine j) = SemidirectProduct.inl a.val.left := by
    apply SemidirectProduct.ext
    · rfl
    · simpa using hr
  have h2 : (a : Affine j) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a.val a.property
  have h3 : (a : Affine j) ^ 3 = 1 := by
    rw [he, ← map_pow, translation_cube, map_one]
  rw [pow_succ, h2, one_mul] at h3
  exact Subtype.ext h3


instance affine_finite [Finite L] : Finite (Affine j) :=
  Finite.of_equiv (Translation × L) SemidirectProduct.equivProd.symm

theorem card_plane : Fintype.card Plane = 9 := by decide

theorem rank_linearPart (hj : Function.Injective j)
    (A : Subgroup (Affine j)) [IsElementaryAbelian 2 A] :
    BinaryOffender.rank (A.map (linearPart j)) = BinaryOffender.rank A := by
  let f := (linearPart j).comp A.subtype
  have hf := linearPart_injective_on_elementary j hj A
  have hr : f.range = A.map (linearPart j) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  unfold BinaryOffender.rank
  congr 1
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem elementary_linearPart (hj : Function.Injective j)
    {A : Subgroup (Affine j)} (hA : BinaryOffender.IsElementaryTwo A) :
    BinaryOffender.IsElementaryTwo (A.map (linearPart j)) := by
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map (linearPart j)⟩
  intro hbot
  apply hA.1
  apply le_bot_iff.mp
  intro a ha
  have hz : linearPart j a = 1 := by
    have hm := Subgroup.mem_map_of_mem (linearPart j) ha
    rwa [hbot, Subgroup.mem_bot] at hm
  have he : (⟨a, ha⟩ : A) = 1 :=
    linearPart_injective_on_elementary j hj A (by simpa using hz)
  exact congrArg Subtype.val he

end Representation.AffineNine
