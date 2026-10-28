module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.WordTable
public import Theory.GroupTheory.Amalgam.RankTwo
public import Mathlib.Data.Fintype.Prod

/-!
# Injecting amalgam automorphisms into a finite word sieve

Two generating pairs share their first generator in the overlap. Three images
therefore determine any compatible automorphism. Relators and preservation of
both overlap embeddings put those images in the finite candidate sieve.
The argument is proved with abstract groups so that its elaboration does not
unfold octonion automorphisms or large multiplication tables.

Source application: the binary G₂ derived amalgam in Aschbacher--Smith F.1.12
and Definition F.4.3. No global extension property is used.
-/

@[expose] public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
open Theory.GroupTheory

variable {L B R : Type*} [Group L] [Group B] [Group R]

structure AmalgamRealization (TL TR : WordTable) (α : RankTwoAmalgam L B R) where
  left : TL.Realization L
  right : TR.Realization R
  middle : Fin 32 ≃ B
  left_overlap : ∀ i, left.equiv (TL.overlap i) = α.left (middle i)
  right_overlap : ∀ i, right.equiv (TR.overlap i) = α.right (middle i)
  labels : ∀ i j b, left.equiv i = α.left b → right.equiv j = α.right b →
    TL.label i = TR.label j

namespace AmalgamRealization
variable {TL TR : WordTable} {α : RankTwoAmalgam L B R}
variable (E : AmalgamRealization TL TR α)

def signature (a : RankTwoAmalgam.Iso α α) : Signature :=
  (E.middle.symm (a.middle (E.middle 1)),
    E.left.equiv.symm (a.left (E.left.equiv 2)),
    E.right.equiv.symm (a.right (E.right.equiv 2)))

theorem left_generator (hL : TL.Valid) (a : RankTwoAmalgam.Iso α α) :
    E.left.equiv (TL.overlap (E.signature a).1) = a.left (E.left.equiv 1) := by
  rw [E.left_overlap]
  change α.left (E.middle (E.middle.symm (a.middle (E.middle 1)))) = _
  rw [E.middle.apply_symm_apply, ← a.left_commutes (E.middle 1), ← E.left_overlap 1, hL.common]

theorem right_generator (hR : TR.Valid) (a : RankTwoAmalgam.Iso α α) :
    E.right.equiv (TR.overlap (E.signature a).1) = a.right (E.right.equiv 1) := by
  rw [E.right_overlap]
  change α.right (E.middle (E.middle.symm (a.middle (E.middle 1)))) = _
  rw [E.middle.apply_symm_apply, ← a.right_commutes (E.middle 1), ← E.right_overlap 1, hR.common]

theorem left_cubic (a : RankTwoAmalgam.Iso α α) :
    E.left.equiv (E.signature a).2.1 = a.left (E.left.equiv 2) :=
  E.left.equiv.apply_symm_apply _

theorem right_cubic (a : RankTwoAmalgam.Iso α α) :
    E.right.equiv (E.signature a).2.2 = a.right (E.right.equiv 2) :=
  E.right.equiv.apply_symm_apply _

theorem left_preserves_overlap (a : RankTwoAmalgam.Iso α α) (i : Fin 32) :
    ∃ j : Fin 32, a.left (E.left.equiv (TL.overlap i)) =
      E.left.equiv (TL.overlap j) := by
  refine ⟨E.middle.symm (a.middle (E.middle i)), ?_⟩
  rw [E.left_overlap i, E.left_overlap (E.middle.symm (a.middle (E.middle i))),
    E.middle.apply_symm_apply]
  exact a.left_commutes (E.middle i)

theorem right_preserves_overlap (a : RankTwoAmalgam.Iso α α) (i : Fin 32) :
    ∃ j : Fin 32, a.right (E.right.equiv (TR.overlap i)) =
      E.right.equiv (TR.overlap j) := by
  refine ⟨E.middle.symm (a.middle (E.middle i)), ?_⟩
  rw [E.right_overlap i, E.right_overlap (E.middle.symm (a.middle (E.middle i))),
    E.middle.apply_symm_apply]
  exact a.right_commutes (E.middle i)

theorem signature_compatible (hL : TL.Valid) (hR : TR.Valid)
    (a : RankTwoAmalgam.Iso α α) : TL.Compatible TR (E.signature a) := by
  refine ⟨E.left.localCandidate hL a.left _ _ (E.left_generator hL a)
      (E.left_cubic a) (E.left_preserves_overlap a),
    E.right.localCandidate hR a.right _ _ (E.right_generator hR a)
      (E.right_cubic a) (E.right_preserves_overlap a), ?_⟩
  intro i
  have hl := (E.left.aut_row hL a.left _ _ (E.left_generator hL a)
    (E.left_cubic a) (TL.overlap i)).trans
    ((congrArg a.left (E.left_overlap i)).trans (a.left_commutes (E.middle i)))
  have hr := (E.right.aut_row hR a.right _ _ (E.right_generator hR a)
    (E.right_cubic a) (TR.overlap i)).trans
    ((congrArg a.right (E.right_overlap i)).trans (a.right_commutes (E.middle i)))
  exact E.labels _ _ (a.middle (E.middle i)) hl hr

theorem signature_injective (hL : TL.Valid) (hR : TR.Valid)
    (hα : Function.Injective α.left) : Function.Injective E.signature := by
  intro a b h
  have h₀ := congrArg Prod.fst h
  have h₁ := congrArg (fun s : Signature => s.2.1) h
  have h₂ := congrArg (fun s : Signature => s.2.2) h
  have hl : a.left = b.left := by
    apply MulEquiv.toMonoidHom_injective
    apply E.left.hom_ext hL
    · change a.left (E.left.equiv 1) = b.left (E.left.equiv 1)
      exact (E.left_generator hL a).symm.trans
        ((congrArg (fun k => E.left.equiv (TL.overlap k)) h₀).trans
          (E.left_generator hL b))
    · change a.left (E.left.equiv 2) = b.left (E.left.equiv 2)
      exact (E.left_cubic a).symm.trans ((congrArg E.left.equiv h₁).trans (E.left_cubic b))
  have hr : a.right = b.right := by
    apply MulEquiv.toMonoidHom_injective
    apply E.right.hom_ext hR
    · change a.right (E.right.equiv 1) = b.right (E.right.equiv 1)
      exact (E.right_generator hR a).symm.trans
        ((congrArg (fun k => E.right.equiv (TR.overlap k)) h₀).trans
          (E.right_generator hR b))
    · change a.right (E.right.equiv 2) = b.right (E.right.equiv 2)
      exact (E.right_cubic a).symm.trans ((congrArg E.right.equiv h₂).trans (E.right_cubic b))
  have hm : a.middle = b.middle := by
    apply MulEquiv.ext
    intro x
    apply hα
    exact (a.left_commutes x).symm.trans
      ((congrArg (fun c : L ≃* L => c (α.left x)) hl).trans (b.left_commutes x))
  rcases a with ⟨⟨aL, aM, aR⟩, haL, haR⟩
  rcases b with ⟨⟨bL, bM, bR⟩, hbL, hbR⟩
  cases hl
  cases hm
  cases hr
  rfl

def encode (hL : TL.Valid) (hR : TR.Valid)
    (a : RankTwoAmalgam.Iso α α) : {s : Signature // TL.Compatible TR s} :=
  ⟨E.signature a, E.signature_compatible hL hR a⟩

theorem encode_injective (hL : TL.Valid) (hR : TR.Valid)
    (hα : Function.Injective α.left) : Function.Injective (E.encode hL hR) := by
  intro a b h
  exact E.signature_injective hL hR hα (congrArg Subtype.val h)

end AmalgamRealization

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
