module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Coordinates

/-!
# Normal generation in the standard middle parabolic

Conjugating the upper middle transvection by the middle-coordinate swap
gives the lower transvection; their length-three product is the swap.
These elements reduce every middle-parabolic element to the full flag
stabilizer. Thus any subgroup containing that stabilizer and normalized
by the middle parabolic contains the latter.

Reference: Aschbacher--Smith 13.8.25, printed p.962 (PDF p.979).
-/

public section

namespace BinaryLinear.MiddleParabolic

private theorem binary (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private theorem actor5_plane : actor 5 ∈ parabolic plane := by
  apply (mem_plane_parabolic (actor_mem 5)).mpr
  decide +kernel

private theorem actor7_conj : actor 6 * actor 5 * (actor 6)⁻¹ = actor 7 := by
  apply LinearEquiv.ext
  exact (by decide +kernel : ∀ v : V,
    actorFun 6 (actorFun 5 (actorFun 6 v)) = actorFun 7 v)

private theorem actor6_word : actor 5 * actor 7 * actor 5 = actor 6 := by
  apply LinearEquiv.ext
  exact (by decide +kernel : ∀ v : V,
    actorFun 5 (actorFun 7 (actorFun 5 v)) = actorFun 6 v)

/-- The standard full flag stabilizer normally generates its middle parabolic. -/
theorem standard_normally_generates (N : Subgroup (BinaryLinear.GL V))
    (hTN : (parabolic line ⊓ parabolic hyperplane) ⊓ parabolic plane ≤ N)
    (hHN : parabolic line ⊓ parabolic hyperplane ≤ Subgroup.normalizer N) :
    parabolic line ⊓ parabolic hyperplane ≤ N := by
  have h5 : actor 5 ∈ N := hTN ⟨actor_mem 5, actor5_plane⟩
  have h7 : actor 7 ∈ N := by
    rw [← actor7_conj]
    exact (hHN (actor_mem 6) (actor 5)).mp h5
  have h6 : actor 6 ∈ N := by
    rw [← actor6_word]
    exact N.mul_mem (N.mul_mem h5 h7) h5
  intro g hg
  by_cases h0 : coordinates g 3 = 0
  · have hm : actor 6 * g ∈ (parabolic line ⊓ parabolic hyperplane) ⊓ parabolic plane := by
      refine ⟨(parabolic line ⊓ parabolic hyperplane).mul_mem (actor_mem 6) hg, ?_⟩
      apply (mem_plane_parabolic ((parabolic line ⊓ parabolic hyperplane).mul_mem
        (actor_mem 6) hg)).mpr
      exact h0
    exact (N.mul_mem_cancel_left h6).mp (hTN hm)
  · have h1 : coordinates g 3 = 1 := (binary _).resolve_left h0
    by_cases hzero : coordinates g 6 = 0
    · exact hTN ⟨hg, (mem_plane_parabolic hg).mpr hzero⟩
    · have hone : coordinates g 6 = 1 := (binary _).resolve_left hzero
      have hc : actor 6 * actor 5 ∈ parabolic line ⊓ parabolic hyperplane :=
        (parabolic line ⊓ parabolic hyperplane).mul_mem (actor_mem 6) (actor_mem 5)
      have hm : actor 6 * actor 5 * g ∈
          (parabolic line ⊓ parabolic hyperplane) ⊓ parabolic plane := by
        refine ⟨(parabolic line ⊓ parabolic hyperplane).mul_mem hc hg, ?_⟩
        apply (mem_plane_parabolic ((parabolic line ⊓ parabolic hyperplane).mul_mem hc hg)).mpr
        change coordinates g 3 + coordinates g 6 = 0
        rw [h1, hone]
        decide
      exact (N.mul_mem_cancel_left (N.mul_mem h6 h5)).mp (hTN hm)

end BinaryLinear.MiddleParabolic

end
