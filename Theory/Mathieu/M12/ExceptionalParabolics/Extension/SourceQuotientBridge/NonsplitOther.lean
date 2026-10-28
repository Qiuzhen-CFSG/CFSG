module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SourceQuotientBridge

/-!
# The marked C₄ × E₄ in the nonsplit first core

The actual factor-swap has order four. Its powers commute with the two paired
quaternion diagonals. Their sixteen products form the literal preimage of the
other eight-group under the existing wreath map. The equivalence retains the
original embedding into the core and takes the original z to (2,0).

Small permutation certificates verify multiplication and injectivity on these
sixteen coordinates; cardinality then identifies the image with the preimage.
Source: the corrected local calculation in Aschbacher--Smith 14.2.21,
printed p.988, refs/quasithin.pdf. This is intrinsic model geometry only.
-/

@[expose] public section

open Sporadic.Mathieu.M12ExceptionalExtension FirstParabolic
namespace Sporadic.Mathieu.M12ExceptionalExtension.SourceQuotientBridge.NonsplitOther
set_option maxRecDepth 10000
abbrev Coordinates := Multiplicative (ZMod 4) × FourWreathTwo.E4

def diagonalI : outerCore := outerLeft (.a 1) * outerRight (.a 1)
def diagonalJ : outerCore := outerLeft (.xa 0) * outerRight (.xa 0)
def encode (v : Coordinates) : outerCore :=
  outerSwap ^ v.1.toAdd.val * diagonalI ^ v.2.toAdd.1.val * diagonalJ ^ v.2.toAdd.2.val

def encodePerm (v : Coordinates) : Equiv.Perm (Fin 24) :=
  nonsplitSwapPerm ^ v.1.toAdd.val * (leftIPerm * rightIPerm) ^ v.2.toAdd.1.val *
    (leftJPerm * rightJPerm) ^ v.2.toAdd.2.val

theorem encode_val (v : Coordinates) : (encode v).val.val = encodePerm v := by
  change nonsplitSwapPerm ^ _ * ((quaternionWord leftI leftJ (.a 1)).val *
    (quaternionWord rightI rightJ (.a 1)).val) ^ _ *
    ((quaternionWord leftI leftJ (.xa 0)).val *
    (quaternionWord rightI rightJ (.xa 0)).val) ^ _ = _
  simp only [quaternionWord_left_val, quaternionWord_right_val, quaternionPerm,
    ZMod.val_zero, pow_zero, mul_one]
  rfl

private theorem encodePerm_mul : ∀ v w : Coordinates,
    encodePerm (v * w) = encodePerm v * encodePerm w := by decide +kernel

private theorem encodePerm_injective : Function.Injective encodePerm := by decide +kernel

def embedding : Coordinates →* outerCore where
  toFun := encode
  map_one' := by apply Subtype.ext; apply Subtype.ext; rw [encode_val]; decide +kernel
  map_mul' v w := by
    apply Subtype.ext; apply Subtype.ext
    change (encode (v*w)).val.val = (encode v).val.val * (encode w).val.val
    simp only [encode_val]
    exact encodePerm_mul v w

theorem embedding_injective : Function.Injective embedding := by
  intro v w h
  apply encodePerm_injective
  exact (encode_val v).symm.trans ((congrArg (fun x : outerCore => x.val.val) h).trans
    (encode_val w))

theorem diagonalI_mem (m : InnerModel) : diagonalI ∈ otherPreimage m := by
  rw [otherPreimage_eq]
  change outerWreathMap m (outerLeft (.a 1) * outerRight (.a 1)) ∈ QuaternionSwapModel.other
  rw [map_mul, outerWreathMap_left, outerWreathMap_right]
  change (_ : QuaternionSwapModel.E4) = _
  decide +kernel

theorem diagonalJ_mem (m : InnerModel) : diagonalJ ∈ otherPreimage m := by
  rw [otherPreimage_eq]
  change outerWreathMap m (outerLeft (.xa 0) * outerRight (.xa 0)) ∈ QuaternionSwapModel.other
  rw [map_mul, outerWreathMap_left, outerWreathMap_right]
  change (_ : QuaternionSwapModel.E4) = _
  decide +kernel

theorem embedding_mem (m : InnerModel) (v : Coordinates) : embedding v ∈ otherPreimage m :=
  (otherPreimage m).mul_mem
    ((otherPreimage m).mul_mem ((otherPreimage m).pow_mem (outerSwap_mem_otherPreimage m) _)
      ((otherPreimage m).pow_mem (diagonalI_mem m) _))
    ((otherPreimage m).pow_mem (diagonalJ_mem m) _)

noncomputable def parametrization (m : InnerModel) : Coordinates ≃* otherPreimage m :=
  MulEquiv.ofBijective (embedding.codRestrict _ (embedding_mem m))
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨
      fun a b h => embedding_injective (congrArg Subtype.val h), by
        rw [otherPreimage_card, Nat.card_eq_fintype_card]
        decide⟩)

theorem parametrization_apply (m : InnerModel) (v : Coordinates) :
    (parametrization m v).val = embedding v := rfl

theorem embedding_swap : embedding (Multiplicative.ofAdd 1, 1) = outerSwap := by
  change outerSwap ^ 1 * diagonalI ^ 0 * diagonalJ ^ 0 = outerSwap
  simp only [pow_one, pow_zero, mul_one]

/-- Coordinates on the literal preimage, retaining its given subgroup inclusion. -/
noncomputable def markedEquiv (m : InnerModel) : otherPreimage m ≃* Coordinates :=
  (parametrization m).symm

def markedCoordinates : Coordinates := (Multiplicative.ofAdd 2, 1)

theorem embedding_marked : embedding markedCoordinates = outerMarked := by
  change outerSwap ^ 2 * diagonalI ^ 0 * diagonalJ ^ 0 = outerMarked
  simp only [pow_zero, mul_one, outerSwap_square]

theorem marked_mem (m : InnerModel) : outerMarked ∈ otherPreimage m := by
  rw [← embedding_marked]
  exact embedding_mem m _

theorem markedEquiv_marked (m : InnerModel) :
    markedEquiv m ⟨outerMarked, marked_mem m⟩ = markedCoordinates := by
  apply (parametrization m).injective
  rw [markedEquiv, MulEquiv.apply_symm_apply]
  exact Subtype.ext embedding_marked.symm

instance other_commutative (m : InnerModel) : IsMulCommutative (otherPreimage m) := by
  constructor
  constructor
  intro a b
  apply (markedEquiv m).injective
  simp only [map_mul, mul_comm]

/-- The swap used in the marked parametrization has order four. -/
theorem swap_order : orderOf outerSwap = 4 := by
  have hs : outerSwap ^ 2 ≠ 1 := by rw [outerSwap_square]; exact outerMarked_ne_one
  have ht : outerSwap ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, outerSwap_square]
    exact Subtype.ext z_square
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hs ht

end Sporadic.Mathieu.M12ExceptionalExtension.SourceQuotientBridge.NonsplitOther
