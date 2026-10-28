module
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged

/-!
# Binary labels for the enlarged split action

The six ordered binary coordinates are encoded by the integers zero through
63. The marked point has label two. Conjugating permutations through this
explicit equivalence gives a faithful permutation representation of the full
automorphism group, so the small permutation certificates use exactly the
same coordinates as the ambient product action.

Source: the elementary coordinate calculation for Aschbacher–Smith,
14.4.4, printed p.1007.
-/

@[expose] public section
namespace BinarySixSplitPair

def decode (i : Fin 64) : E :=
  (Multiplicative.ofAdd ![(i.val%2 : ℕ),((i.val/2)%2:ℕ),((i.val/4)%2:ℕ),((i.val/8)%2:ℕ)],
   Multiplicative.ofAdd ![((i.val/16)%2:ℕ),((i.val/32)%2:ℕ)])

def encode (x : E) : Fin 64 :=
  ⟨(x.1.toAdd 0).val + 2*(x.1.toAdd 1).val + 4*(x.1.toAdd 2).val +
    8*(x.1.toAdd 3).val + 16*(x.2.toAdd 0).val + 32*(x.2.toAdd 1).val,by
      have h0 := (x.1.toAdd 0).val_lt
      have h1 := (x.1.toAdd 1).val_lt
      have h2 := (x.1.toAdd 2).val_lt
      have h3 := (x.1.toAdd 3).val_lt
      have h4 := (x.2.toAdd 0).val_lt
      have h5 := (x.2.toAdd 1).val_lt
      omega⟩

def labels : E ≃ Fin 64 where
  toFun := encode
  invFun := decode
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permAction : MulAut E →* Equiv.Perm (Fin 64) :=
  labels.permCongrHom.toMonoidHom.comp (MulAut.toPerm E)

theorem permAction_injective : Function.Injective permAction := by
  intro f g h
  apply MulEquiv.ext
  intro x
  apply labels.injective
  have hh := Equiv.congr_fun h (labels x)
  change labels (f (labels.symm (labels x))) = labels (g (labels.symm (labels x))) at hh
  simpa only [labels.symm_apply_apply] using hh

theorem labels_point : labels point = 2 := by decide +kernel

theorem permAction_apply (f : MulAut E) (x : E) :
    permAction f (labels x) = labels (f x) := by
  change labels (f (labels.symm (labels x))) = _
  rw [labels.symm_apply_apply]

end BinarySixSplitPair
