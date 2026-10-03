module

public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.Tactic.Group

/-!
# Extending a normalizer action modulo the centralizer

If `N_G(U)` is contained in the product of `C_G(U)` and the simultaneous
normalizer of `U` and `V`, every normalizer action on `U` is induced by an
element normalizing `V`. The simultaneous normalizer normalizes `C_G(U)`,
so the subgroup join is a product. Its centralizer factor fixes `U`
pointwise and can be discarded from right conjugation.

This is the elementary extension step used after a Frattini argument in
centric fusion reduction. The product-containment hypothesis remains
explicit; it does not assert that arbitrary centric subgroups are radical.

The second extension lemma supplies the Frattini correction for the preimage
of a normal `p`-subgroup under any homomorphism from a finite group. The Sylow
intersection maps onto that preimage's image, so its product with the kernel
is the full preimage. Frattini's argument then gives a normalizer representative
modulo the kernel.
-/

namespace Subgroup

/-- A centralizer-times-normalizer factorization extends the entire action
on `U` to an element normalizing `V`. -/
public theorem exists_normalizer_extension_of_le_sup
    {G : Type*} [Group G] (U V : Subgroup G)
    (hcover : normalizer (U : Set G) ≤
      centralizer (U : Set G) ⊔ (normalizer (U : Set G) ⊓ normalizer (V : Set G)))
    (g : G) (hg : g ∈ normalizer (U : Set G)) :
    ∃ n ∈ normalizer (U : Set G) ⊓ normalizer (V : Set G),
      ∀ x ∈ U, g⁻¹ * x * g = n⁻¹ * x * n := by
  have hnorm : normalizer (U : Set G) ⊓ normalizer (V : Set G) ≤
      normalizer (centralizer (U : Set G) : Set G) :=
    inf_le_left.trans (normalizer_le_normalizer_centralizer U)
  have hprod := coe_mul_of_right_le_normalizer_left
    (centralizer (U : Set G))
    (normalizer (U : Set G) ⊓ normalizer (V : Set G)) hnorm
  have hgprod := hcover hg
  rw [← SetLike.mem_coe, hprod] at hgprod
  obtain ⟨c, hc, n, hn, rfl⟩ := hgprod
  refine ⟨n, hn, ?_⟩
  intro x hx
  have hcfix : c⁻¹ * x * c = x := by
    have hcomm := mem_centralizer_iff.mp hc x hx
    rw [mul_assoc, hcomm]
    simp
  calc
    (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
    _ = n⁻¹ * x * n := by rw [hcfix]

end Subgroup

open scoped Pointwise

/-- For a homomorphism out of a finite group, each action is represented by an
 element normalizing the Sylow intersection with the preimage of a normal
 `p`-subgroup of the target. -/
public theorem Sylow.exists_normalizer_preimage_correction
    {H A : Type*} [Group H] [Finite H] [Group A]
    {p : ℕ} [Fact p.Prime] (P : Sylow p H) (f : H →* A)
    (K : Subgroup A) [K.Normal] (hK : IsPGroup p K) :
    ∀ g : H, ∃ n ∈ Subgroup.normalizer
      (((P : Subgroup H) ⊓ K.comap f : Subgroup H) : Set H), f n = f g := by
  let L := K.comap f
  let D := (P : Subgroup H) ⊓ L
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal L
  have hQD : (Q : Subgroup L).map L.subtype = D := by
    rw [hQ, Subgroup.subgroupOf_map_subtype]
  let φ := f.comp L.subtype
  have hφ : IsPGroup p φ.range := hK.to_le (by
    rintro _ ⟨x, rfl⟩
    exact x.property)
  let R := Q.mapSurjective φ.rangeRestrict_surjective
  have hR : (R : Subgroup φ.range) = ⊤ :=
    (R.is_maximal' (hφ.to_subgroup ⊤) le_top).symm
  have hL : L ≤ D ⊔ f.ker := by
    intro x hx
    have hxR : φ.rangeRestrict ⟨x, hx⟩ ∈ (R : Subgroup φ.range) := by
      rw [hR]
      trivial
    obtain ⟨y, hy, heq⟩ := hxR
    have hf : f (y : H) = f x := congrArg Subtype.val heq
    have hyD : (y : H) ∈ D := hQD ▸ Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hker : (y : H)⁻¹ * x ∈ f.ker := by
      simp [MonoidHom.mem_ker, hf]
    have hm := (D ⊔ f.ker).mul_mem
      (Subgroup.mem_sup_left hyD) (Subgroup.mem_sup_right hker)
    simpa using hm
  have htop : Subgroup.normalizer (D : Set H) ⊔ L = ⊤ := by
    simpa only [hQD] using Q.normalizer_sup_eq_top
  have hcover : Subgroup.normalizer (D : Set H) ⊔ f.ker = ⊤ := by
    apply top_le_iff.mp
    rw [← htop]
    exact sup_le le_sup_left (hL.trans (sup_le_sup Subgroup.le_normalizer le_rfl))
  intro g
  have hg : g ∈ (Subgroup.normalizer (D : Set H) : Set H) * (f.ker : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (show Subgroup.normalizer (D : Set H) ≤ Subgroup.normalizer (f.ker : Set H)
        from Subgroup.le_normalizer_of_normal), hcover]
    trivial
  obtain ⟨n, hn, c, hc, rfl⟩ := hg
  exact ⟨n, hn, by simp [show f c = 1 from hc]⟩
