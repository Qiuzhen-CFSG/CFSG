module
public import Theory.GroupTheory.Amalgam.CompletionAction
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Inner actors in a marked completion

If the two endpoint images are self-normalizing and their intersection is the
whole marked middle image, an automorphism preserving both endpoints can be
inner only by an element of that middle image. An injective actor marking
therefore detects the original reduced overlap and forces the completion to
be centerless. No classification or finiteness assumption is used.

These are the intersection checks for extending local markings in
Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985), Chapter 15,
printed pp.226--231.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace Theory.GroupTheory.RankTwoAmalgam.CompletionAction
variable {L B R K X : Type*} [Group L] [Group B] [Group R] [Group K] [Group X]
  {α : RankTwoAmalgam L B R} (c : FaithfulCompletion α (G := X))
  (ρ : K →* MulAut X) (hρ : Function.Injective ρ) (j : B →* K)
  (hred : ∀ d, ρ (j d) = MulAut.conj (c.middle d))
  (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
  (hnl : normalizer (c.left.range : Set X) = c.left.range)
  (hnr : normalizer (c.right.range : Set X) = c.right.range)

include hρ hred hoverlap hnl hnr

/-- Self-normalizing endpoint images detect an inner actor in the marked
middle group. The whole overlap, rather than its Sylow subgroup, is needed. -/
theorem mem_inner_iff
    (hl : ∀ k, c.left.range.map (ρ k).toMonoidHom = c.left.range)
    (hr : ∀ k, c.right.range.map (ρ k).toMonoidHom = c.right.range) (k : K) :
    ρ k ∈ (MulAut.conj : X →* MulAut X).range ↔ k ∈ j.range := by
  constructor
  · rintro ⟨x,hx⟩
    have hxl : x ∈ c.left.range := by
      rw [← hnl, mem_normalizer_iff_map_conj_eq, hx]
      exact hl k
    have hxr : x ∈ c.right.range := by
      rw [← hnr, mem_normalizer_iff_map_conj_eq, hx]
      exact hr k
    obtain ⟨d,hd⟩ := (show x ∈ c.middle.range from hoverlap ▸ ⟨hxl,hxr⟩)
    refine ⟨d,hρ ?_⟩
    rw [hred,hd,hx]
  · rintro ⟨d,rfl⟩
    exact ⟨c.middle d,(hred d).symm⟩

/-- Faithfulness of the marked overlap forces this completion to be
centerless when its endpoints are self-normalizing. -/
theorem center_eq_bot (hj : Function.Injective j) : center X = ⊥ := by
  apply bot_unique
  intro x hx
  have hxl : x ∈ c.left.range := hnl ▸ center_le_normalizer _ hx
  have hxr : x ∈ c.right.range := hnr ▸ center_le_normalizer _ hx
  obtain ⟨d,hd⟩ := (show x ∈ c.middle.range from hoverlap ▸ ⟨hxl,hxr⟩)
  have he : MulAut.conj x = (1 : MulAut X) := by
    apply MulEquiv.ext
    intro y
    change x*y*x⁻¹=y
    rw [← (mem_center_iff.mp hx y), mul_inv_cancel_right]
  have hd1 : d = 1 := by
    apply hj
    apply hρ
    rw [hred,hd,he,map_one,map_one]
  exact mem_bot.mpr (hd.symm.trans (by rw [hd1,map_one]))

end Theory.GroupTheory.RankTwoAmalgam.CompletionAction
