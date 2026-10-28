module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.ModelFacts
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
import Mathlib.Tactic
/-!
# The actual normalizer image contains the natural S₆

The component equivalence induced by the marked product model transports
ambient conjugation on L to Aut(A₆). On LE this map is exactly the natural
permutation action, so its full normalizer image contains the natural S₆.
Since that subgroup has index two, the image is either the natural S₆ or
all of Aut(A₆).

This is the automorphism-image part of the ordinary/full alternative.
Identifying LT with LE in the ordinary case still requires the Sylow and
centralizer-kernel argument; no ambient subgroup equality is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
open Subgroup Equiv Equiv.Perm
namespace CFSG.Quasithin.Chapter16.Intersections.Six
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

/-- Transport the genuine normalizer conjugation through the model coordinates. -/
noncomputable def modelNormalizerAction (M : AlternatingProductModel L z r 6) :
    normalizer (L : Set G) →* AutA6 :=
  (MulAut.congr (modelComponentEquiv M)).toMonoidHom.comp L.normalizerMonoidHom

/-- On LE the transported action is its actual permutation action. -/
theorem modelNormalizerAction_on_overgroup (M : AlternatingProductModel L z r 6)
    (a : AlternatingOvergroup L z r) :
    modelNormalizerAction M ⟨a, overgroup_normalizes M a.property⟩ =
      permutationAction (M.equiv a).1 := by
  apply MulEquiv.ext
  intro l
  apply Subtype.ext
  obtain ⟨l, rfl⟩ := (modelComponentEquiv M).surjective l
  change (modelComponentEquiv M (L.normalizerMonoidHom
    ⟨a, overgroup_normalizes M a.property⟩
      ((modelComponentEquiv M).symm (modelComponentEquiv M l))) : Perm (Fin 6)) = _
  rw [(modelComponentEquiv M).symm_apply_apply]
  exact modelComponentEquiv_conjugation M a l

/-- All permutation-induced automorphisms occur in the actual normalizer image. -/
theorem natural_le_modelNormalizerAction_range (M : AlternatingProductModel L z r 6) :
    natural ≤ (modelNormalizerAction M).range := by
  rintro β ⟨p, rfl⟩
  let a := M.equiv.symm (p, 1)
  refine ⟨⟨a, overgroup_normalizes M a.property⟩, ?_⟩
  rw [modelNormalizerAction_on_overgroup]
  simp only [a, M.equiv.apply_symm_apply]
  rfl

/-- Index two gives the alternative for the actual image in Aut(A₆). -/
theorem modelNormalizerAction_range_alternative (M : AlternatingProductModel L z r 6) :
    (modelNormalizerAction M).range = natural ∨ Function.Surjective (modelNormalizerAction M) := by
  by_cases hf : (modelNormalizerAction M).range = ⊤
  · exact Or.inr (MonoidHom.range_eq_top.mp hf)
  · left
    by_contra hn
    have hs := Subgroup.index_strictAnti (lt_of_le_of_ne
      (natural_le_modelNormalizerAction_range M) (Ne.symm hn))
    rw [GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index] at hs
    have hp : (modelNormalizerAction M).range.index ≠ 0 := index_ne_zero_of_finite
    exact hf (index_eq_one.mp (by omega))

/-- Surjectivity of the actual action is independent of the chosen A₆ coordinates. -/
theorem modelNormalizerAction_surjective_iff (M : AlternatingProductModel L z r 6)
    (e : L ≃* alternatingGroup (Fin 6)) :
    Function.Surjective (modelNormalizerAction M) ↔
      Function.Surjective ((MulAut.congr e).toMonoidHom.comp L.normalizerMonoidHom) := by
  constructor
  · intro hf
    change Function.Surjective ((MulAut.congr e) ∘ L.normalizerMonoidHom)
    apply (MulAut.congr e).surjective.comp
    intro b
    obtain ⟨a, ha⟩ := hf ((MulAut.congr (modelComponentEquiv M)) b)
    exact ⟨a, (MulAut.congr (modelComponentEquiv M)).injective ha⟩
  · intro hf
    change Function.Surjective ((MulAut.congr (modelComponentEquiv M)) ∘
      L.normalizerMonoidHom)
    apply (MulAut.congr (modelComponentEquiv M)).surjective.comp
    intro b
    obtain ⟨a, ha⟩ := hf ((MulAut.congr e) b)
    exact ⟨a, (MulAut.congr e).injective ha⟩

end CFSG.Quasithin.Chapter16.Intersections.Six
