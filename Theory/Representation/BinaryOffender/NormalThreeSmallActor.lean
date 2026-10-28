module

public import Theory.Representation.BinaryOffender.NormalThree
public import Theory.Representation.BinaryOffender.CubicFixedSpaceSaturation
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer

/-!
# Small binary actors centralize a fixed-point-free normal cubic subgroup

Suppose a faithful binary module has degree at least twelve. An elementary
actor of rank at most three and fixed codimension at most twice its rank
centralizes every fixed-point-free normal subgroup of order three.

An inverting involution moves half the module. The bounds force its fixed
space to equal the actor's fixed space, which makes the actor quadratic.
The normal-three quadratic calculation then forces rank one and degree at
most four, a contradiction. No cubic-action hypothesis is needed.

Source: the dimension and fixed-space method of Guralnick--Malle,
*Classification of 2F-modules I*, applied to the outer triple-A7 branch
of Aschbacher--Smith K.1, printed p.452.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The ratio-two bound excludes inversion of a normal fixed-point-free C₃. -/
theorem small_actor_centralizes_normal_three
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (c : G) (hc : orderOf c = 3) (hn : (zpowers c).Normal)
    (hfree : ∀ v, ρ c v = v → v = 0)
    (hd : 12 ≤ Module.finrank (ZMod 2) V)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hr : rank A ≤ 3)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    A ≤ centralizer (zpowers c : Set G) := by
  let : IsElementaryAbelian 2 A := hA.2
  by_contra hnot
  obtain ⟨t, ht, htn⟩ := SetLike.not_le_iff_exists.mp hnot
  have hinv : t * c = c ^ 2 * t := by
    rcases RankTwo.commute_or_invert_of_normal_three c t hc hn with h | h
    · exfalso
      apply htn
      intro z hz
      obtain ⟨n, rfl⟩ := hz
      exact (h.zpow_left n).eq
    · exact h
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hc3 : (ρ c) ^ 3 = 1 := by rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
  have hρt : ρ t * ρ t = 1 := by rw [← map_mul, ← pow_two, ht2, map_one]
  have hρtc : ρ t * ρ c = (ρ c) ^ 2 * ρ t := by
    rw [← map_pow, ← map_mul, ← map_mul, hinv]
  have hhalf := RankTwo.finrank_range_inverting_cubic (ρ c) (ρ t) hc3 hfree hρt hρtc
  have hcodim : fixedCodim ρ (zpowers t) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
    exact fixedCodim_zpowers_eq_displacement_rank ρ t
  have hlarge : 2 * 3 ≤ fixedCodim ρ (zpowers t) := by omega
  obtain ⟨_, heq⟩ := fixedSpace_eq_of_saturated_actor ρ ht hr hsmall hlarge
  have hq : IsQuadratic ρ A := by
    intro a ha b hb v
    apply (show ρ b v - v ∈ fixedSpace ρ A from ?_) ⟨a, ha⟩
    rw [heq, mem_fixedSpace_zpowers_iff]
    have hdt : ρ t v - v ∈ fixedSpace ρ (zpowers t) := by
      rw [mem_fixedSpace_zpowers_iff, map_sub]
      have htv : ρ t (ρ t v) = v := LinearMap.congr_fun hρt v
      rw [htv]
      have hn (w : V) : -w = w := by
        have hh := @two_smul (ZMod 2) V _ _ _ w
        rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at hh
        exact neg_eq_iff_add_eq_zero.mpr hh.symm
      simp only [sub_eq_add_neg, hn]
      exact add_comm _ _
    have hbfix := (show ρ t v - v ∈ fixedSpace ρ A from heq.symm ▸ hdt) ⟨b, hb⟩
    change ρ b (ρ t v - v) = ρ t v - v at hbfix
    have htb : t * b = b * t := congrArg Subtype.val (mul_comm (⟨t, ht⟩ : A) ⟨b, hb⟩)
    have hcomm : ρ t (ρ b v) = ρ b (ρ t v) := by
      rw [← Module.End.mul_apply, ← map_mul, htb, map_mul, Module.End.mul_apply]
    rw [map_sub, hcomm]
    rw [map_sub] at hbfix
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp hbfix)
  have hm : subspaceCommutator ρ ⊤ (zpowers c) = ⊤ := by
    have hi : Function.Injective (ρ c - 1 : V →ₗ[ZMod 2] V) := by
      apply LinearMap.ker_eq_bot.mp
      apply le_bot_iff.mp
      intro v hv
      exact hfree v (sub_eq_zero.mp hv)
    have hs := LinearMap.surjective_of_injective hi
    apply top_unique
    intro v _
    obtain ⟨w, rfl⟩ := hs v
    exact Submodule.subset_span ⟨c, mem_zpowers c, w, Submodule.mem_top, rfl⟩
  obtain ⟨hr1, hdim⟩ := normalThree_quadratic_rank_fixedCodim ρ hf (zpowers c) hn
    (by rw [Nat.card_zpowers, hc]) hm A hA hq hnot
  omega

end Representation.BinaryOffender
