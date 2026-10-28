module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Inner squares detected on a characteristic subgroup

Let N be characteristic in G, with C_G(N) contained in N and of exponent two.
An automorphism fixing N pointwise displaces each x by x⁻¹α(x) in C_G(N).
It fixes this displacement, so its square is the identity. Consequently, an
automorphism whose restriction to N is induced by an element of G has inner
square: first correct by that element, then apply the kernel calculation.

Every automorphism of G normalizes the image of G in Aut(N). If that image is
self-normalizing, all automorphisms of G therefore have inner square.

This elementary restriction argument supplies the group-theoretic step in the
J₄ involution-centralizer calculation motivated by GLS3, Table 5.3i,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. No local-structure assertion from that
table is used as an input to this general theorem.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic]

/-- Restriction of an inner automorphism is the normal-subgroup action. -/
theorem characteristic_conj_eq_conjNormal (g : G) :
    MulAut.characteristic N (MulAut.conj g) = MulAut.conjNormal g := by
  apply MulEquiv.ext
  intro x
  rfl

/-- Restriction intertwines conjugation with the automorphism of the actor. -/
theorem characteristic_conjNormal_equivariant (α : MulAut G) (g : G) :
    MulAut.characteristic N α * MulAut.conjNormal g * (MulAut.characteristic N α)⁻¹ =
      MulAut.conjNormal (α g) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change α (g * α.symm (x : G) * g⁻¹) = α g * (x : G) * (α g)⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- An automorphism restricts to a normalizer of the induced inner action. -/
theorem characteristic_mem_normalizer_conjNormal_range (α : MulAut G) :
    MulAut.characteristic N α ∈ normalizer
      ((MulAut.conjNormal : G →* MulAut N).range : Set (MulAut N)) := by
  rw [mem_normalizer_iff]
  intro β
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨α g, (characteristic_conjNormal_equivariant N α g).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨α.symm g, ?_⟩
    have h := characteristic_conjNormal_equivariant N α (α.symm g)
    rw [MulEquiv.apply_symm_apply, hg] at h
    exact mul_left_cancel (mul_right_cancel h)

/-- If the centralizer is contained in N and has exponent two, the kernel of
restriction to N has exponent two. -/
theorem square_eq_one_of_characteristic_eq_one
    (hself : centralizer (N : Set G) ≤ N)
    (hpow : ∀ z ∈ centralizer (N : Set G), z ^ 2 = 1)
    (β : MulAut G) (hβ : MulAut.characteristic N β = 1) : β ^ 2 = 1 := by
  have hfix (n : G) (hn : n ∈ N) : β n = n :=
    congrArg Subtype.val (DFunLike.congr_fun hβ (⟨n, hn⟩ : N))
  have hdisp (x : G) : x⁻¹ * β x ∈ centralizer (N : Set G) := by
    intro n hn
    have h := hfix (x * n * x⁻¹) ((inferInstance : N.Normal).conj_mem n hn x)
    simp only [map_mul, map_inv, hfix n hn] at h
    have hh := congrArg (fun t : G => x⁻¹ * t * β x) h
    group at hh
    simpa only [mul_assoc, zpow_neg_one] using hh.symm
  apply MulEquiv.ext
  intro x
  change β (β x) = x
  have hd := hfix (x⁻¹ * β x) (hself (hdisp x))
  calc
    β (β x) = β (x * (x⁻¹ * β x)) := by rw [mul_inv_cancel_left]
    _ = β x * (x⁻¹ * β x) := by rw [map_mul, hd]
    _ = x * ((x⁻¹ * β x) ^ 2) := by simp only [pow_two]; group
    _ = x := by rw [hpow _ (hdisp x), mul_one]

/-- Correct an automorphism whose restriction comes from G. The correction
has square one, yielding an actual conjugator for the original square. -/
theorem square_inner_of_characteristic_mem_conjNormal_range
    (hself : centralizer (N : Set G) ≤ N)
    (hpow : ∀ z ∈ centralizer (N : Set G), z ^ 2 = 1)
    (α : MulAut G)
    (hα : MulAut.characteristic N α ∈ (MulAut.conjNormal : G →* MulAut N).range) :
    ∃ c : G, α ^ 2 = MulAut.conj c := by
  obtain ⟨c, hc⟩ := hα
  let β : MulAut G := MulAut.conj c⁻¹ * α
  have hb : MulAut.characteristic N β = 1 := by
    dsimp only [β]
    rw [map_mul, characteristic_conj_eq_conjNormal, ← hc, map_inv, inv_mul_cancel]
  have hb2 := square_eq_one_of_characteristic_eq_one N hself hpow β hb
  have he : α = MulAut.conj c * β := by
    dsimp only [β]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨c * β c, ?_⟩
  rw [he]
  apply MulEquiv.ext
  intro x
  have hx := DFunLike.congr_fun hb2 x
  change β (β x) = x at hx
  change c * β (c * β x * c⁻¹) * c⁻¹ = (c * β c) * x * (c * β c)⁻¹
  simp only [map_mul, map_inv, hx, mul_inv_rev, mul_assoc]

/-- A self-normalizing conjugation image detects inner squares. -/
theorem square_inner_of_self_normalizing_conjNormal_range
    (hself : centralizer (N : Set G) ≤ N)
    (hpow : ∀ z ∈ centralizer (N : Set G), z ^ 2 = 1)
    (hnorm : normalizer ((MulAut.conjNormal : G →* MulAut N).range : Set (MulAut N)) ≤
      (MulAut.conjNormal : G →* MulAut N).range)
    (α : MulAut G) : ∃ c : G, α ^ 2 = MulAut.conj c :=
  square_inner_of_characteristic_mem_conjNormal_range N hself hpow α
    (hnorm (characteristic_mem_normalizer_conjNormal_range N α))

end Subgroup
