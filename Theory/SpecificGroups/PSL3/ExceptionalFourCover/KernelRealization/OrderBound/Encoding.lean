module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.Model
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound.Checker
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Faithful finite coordinates for the literal exceptional extension

The two permutations act on their given 224 letters. The SL₃(F₄) coordinate
acts by ordinary multiplication on **column** vectors, including zero.
Coding the field as `re + 2*im` and vectors in base four gives 64 letters.
The resulting monoid homomorphism is injective, by faithfulness of the
natural matrix action. Thus a cover of the encoded positive-word monoid
bounds the literal subgroup `KernelModel.Group`; finiteness identifies
positive monoid generation with subgroup generation.

No GAP action convention is assumed in this comparison. In particular,
`encode` uses the actual Lean permutations and the actual matrix product.
Source application: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate

abbrev V := Fin 3 → F

def fieldCode : F ≃ Fin 4 where
  toFun a := ⟨a.re.val + 2 * a.im.val, by have := ZMod.val_lt a.re; have := ZMod.val_lt a.im; omega⟩
  invFun i := ⟨(i.val % 2 : Nat), (i.val / 2 : Nat)⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vectorCode : V ≃ Fin 64 where
  toFun v := ⟨16 * (fieldCode (v 0)).val + 4 * (fieldCode (v 1)).val +
    (fieldCode (v 2)).val, by
      have := (fieldCode (v 0)).isLt
      have := (fieldCode (v 1)).isLt
      have := (fieldCode (v 2)).isLt
      omega⟩
  invFun i := ![fieldCode.symm ⟨i.val / 16, by omega⟩,
    fieldCode.symm ⟨i.val / 4 % 4, Nat.mod_lt _ (by decide)⟩,
    fieldCode.symm ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def encode : Ambient →* M where
  toFun g := ((fun i => g.1.1 i, fun i => g.1.2 i), fun i => vectorCode (g.2.val.mulVec (vectorCode.symm i)))
  map_one' := by
    apply Prod.ext
    · rfl
    · funext i
      change vectorCode ((1 : Matrix (Fin 3) (Fin 3) F).mulVec (vectorCode.symm i)) = i
      simp
  map_mul' g h := by
    apply Prod.ext
    · rfl
    · funext i
      change vectorCode ((g.2.val * h.2.val).mulVec (vectorCode.symm i)) =
        vectorCode (g.2.val.mulVec (vectorCode.symm (vectorCode
          (h.2.val.mulVec (vectorCode.symm i)))))
      rw [vectorCode.symm_apply_apply, Matrix.mulVec_mulVec]

theorem encode_injective : Function.Injective encode := by
  intro g h he
  apply Prod.ext
  · apply Prod.ext
    · apply Equiv.ext
      exact congrFun (congrArg (fun a : M => a.1.1) he)
    · apply Equiv.ext
      exact congrFun (congrArg (fun a : M => a.1.2) he)
  · apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    change g.2.val.mulVec v = h.2.val.mulVec v
    have hv := congrFun (congrArg (fun a : M => a.2) he) (vectorCode v)
    exact vectorCode.injective (by simpa only [encode, MonoidHom.coe_mk,
      OneHom.coe_mk, vectorCode.symm_apply_apply] using hv)


/-- All three encoded coordinates agree with the literal generator `x`. -/
theorem encode_x : encode x = gen0 0 := by
  apply eq_of_check
  decide +kernel

/-- All three encoded coordinates agree with the literal generator `y`. -/
theorem encode_y : encode y = gen0 1 := by
  apply eq_of_check
  decide +kernel

theorem realization_card_le_of_encoded (H : Submonoid M)
    (hx : encode x ∈ H) (hy : encode y ∈ H) : Nat.card Group ≤ Nat.card H := by
  have hm (g : Ambient) (hg : g ∈ subgroup) : encode g ∈ H := by
    have hg' : g ∈ Submonoid.closure ({x, y} : Set Ambient) := by
      change g ∈ (Subgroup.closure ({x, y} : Set Ambient)).toSubmonoid at hg
      rwa [Subgroup.closure_toSubmonoid_of_finite] at hg
    clear hg
    induction hg' using Submonoid.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact hx
      · exact hy
    | one => simpa only [map_one] using H.one_mem
    | mul a b ha hb ia ib => simpa only [map_mul] using H.mul_mem ia ib
  let f : Group → H := fun g => ⟨encode g, hm g g.property⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  apply Subtype.ext
  exact encode_injective (congrArg Subtype.val hab)

end Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate
