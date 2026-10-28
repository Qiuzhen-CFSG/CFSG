module

public import Stellmacher.ElementaryAbelianMaxJWeakClosure

/-!
# The normalizer action on the maximum elementary family

The normalizer of the elementary Thompson subgroup permutes the original
subgroup's maximum elementary subgroups: their order is unchanged, and their
images remain in the Thompson subgroup. In the wreath configuration this is
the actual four-vertex intersection action of 13.9.2(2).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Subgroup

namespace Stellmacher

variable {G : Type*} [Group G]

theorem maxFamily_map_of_normalizes_maxJ (S E : Subgroup G)
    (hE : E ∈ elementaryAbelianMaxSubgroups S) (g : G)
    (hg : g ∈ normalizer (elementaryAbelianMaxJ S : Set G)) :
    E.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups S := by
  have hES : E ≤ elementaryAbelianMaxJ S := le_sSup hE
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le (fun _ h => h.1)
  have hgJ : (elementaryAbelianMaxJ S).map (MulAut.conj g).toMonoidHom =
      elementaryAbelianMaxJ S := mem_normalizer_iff_map_conj_eq.mp hg
  refine ⟨?_, hE.2.1.map _, ?_⟩
  · have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hES
    rw [hgJ] at hmap
    exact hmap.trans hJS
  · intro B hBS hB
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hE.2.2 B hBS hB

private theorem conjugate_map_mul (E : Subgroup G) (g h : G) :
    E.map (MulAut.conj (g * h)).toMonoidHom =
      (E.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

def maxJNormalizerPerm (S : Subgroup G) (g : normalizer (elementaryAbelianMaxJ S : Set G)) :
    Equiv.Perm {E : Subgroup G // E ∈ elementaryAbelianMaxSubgroups S} where
  toFun E := ⟨E.1.map (MulAut.conj (g : G)).toMonoidHom,
    maxFamily_map_of_normalizes_maxJ S E.1 E.2 g g.2⟩
  invFun E := ⟨E.1.map (MulAut.conj (g⁻¹ : G)).toMonoidHom,
    maxFamily_map_of_normalizes_maxJ S E.1 E.2 g⁻¹ ((normalizer _).inv_mem g.2)⟩
  left_inv E := by
    apply Subtype.ext
    change (E.1.map _).map _ = E.1
    rw [← conjugate_map_mul, inv_mul_cancel]
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by ext x; simp, map_id]
  right_inv E := by
    apply Subtype.ext
    change (E.1.map _).map _ = E.1
    rw [← conjugate_map_mul, mul_inv_cancel]
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by ext x; simp, map_id]

def maxJNormalizerAction (S : Subgroup G) :
    normalizer (elementaryAbelianMaxJ S : Set G) →*
      Equiv.Perm {E : Subgroup G // E ∈ elementaryAbelianMaxSubgroups S} where
  toFun := maxJNormalizerPerm S
  map_one' := by
    apply Equiv.ext
    intro E
    apply Subtype.ext
    change E.1.map (MulAut.conj (1 : G)).toMonoidHom = E.1
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by ext x; simp, map_id]
  map_mul' g h := by
    apply Equiv.ext
    intro E
    apply Subtype.ext
    exact conjugate_map_mul E.1 g h

theorem maxJNormalizerAction_apply (S : Subgroup G)
    (g : normalizer (elementaryAbelianMaxJ S : Set G))
    (E : {E : Subgroup G // E ∈ elementaryAbelianMaxSubgroups S}) :
    (maxJNormalizerAction S g E).1 = E.1.map (MulAut.conj (g : G)).toMonoidHom := rfl

end Stellmacher
