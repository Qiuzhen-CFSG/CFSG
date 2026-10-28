module

public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.QuasisimpleCoreImageAction

/-!
# Detecting a block action through the original two-core

If an original normalizer element is trivial on J/O₂(J), its action on the
quasisimple core-central image of J is trivial pointwise. The image map is
the original inclusion J≤K followed by K→K/O₂(K)/Z, and equivariance follows
from the original conjugation actions. No kernel of this composite is
assumed to be a two-group.

Source: Aschbacher--Smith 6.1.4, the original ternary block on p.666.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Triviality modulo the full two-core of the original subgroup fixes its
entire quasisimple image in the original component carrier. -/
theorem coreCentral_block_fixed_of_trivial_twoCore_action
    (K J : Subgroup G) (hJK : J ≤ K)
    (B : Subgroup (coreCentralQuotient K)) [IsQuasisimple B]
    (hB : coreCentralIntersectionImage K J = B)
    (x : G) (hxK : x ∈ normalizer (K : Set G))
    (hxJ : x ∈ normalizer (J : Set G))
    (hx : quotientAut (pCore 2 J) (J.normalizerMonoidHom ⟨x,hxJ⟩) = 1) :
    ∀ b ∈ B, normalizerCoreCentralAction K ⟨x,hxK⟩ b = b := by
  let q : J →* coreCentralQuotient K := (coreCentralProjection K).comp (inclusion hJK)
  have hqB : q.range = B := by
    calc
      q.range = (J.subgroupOf K).map (coreCentralProjection K) := by
        rw [MonoidHom.range_comp]
        congr 1
        ext k
        constructor
        · rintro ⟨j,rfl⟩
          exact j.property
        · intro hk
          exact ⟨⟨k,hk⟩,rfl⟩
      _ = B := hB
  let f : J →* B := (MulEquiv.subgroupCongr hqB).toMonoidHom.comp q.rangeRestrict
  have hf : Function.Surjective f := (MulEquiv.subgroupCongr hqB).surjective.comp
    q.rangeRestrict_surjective
  let a := J.normalizerMonoidHom ⟨x,hxJ⟩
  let b := normalizerCoreCentralAction K ⟨x,hxK⟩
  have he (j : J) : q (a j) = b (q j) := by
    exact (normalizerCoreCentralAction_apply K ⟨x,hxK⟩ (inclusion hJK j)).symm
  have hBb : B.map b.toMonoidHom = B := by
    apply eq_of_le_of_card_ge
    · rintro y ⟨z,hz,rfl⟩
      obtain ⟨j,hj⟩ := hf ⟨z,hz⟩
      have hj' : q j = z := congrArg Subtype.val hj
      change b z ∈ B
      rw [←hj',←he]
      exact hqB ▸ (show q (a j) ∈ q.range from ⟨a j,rfl⟩)
    · exact (Nat.card_congr (b.subgroupMap B).toEquiv).le
  let bB : MulAut B := (b.subgroupMap B).trans (MulEquiv.subgroupCongr hBb)
  have hef : f.comp a.toMonoidHom = bB.toMonoidHom.comp f := by
    ext j
    exact he j
  have hbB : bB = 1 := quasisimple_image_action_eq_one_of_twoCore_action f hf a bB hef hx
  intro y hy
  exact congrArg Subtype.val (DFunLike.congr_fun hbB (⟨y,hy⟩ : B))

end Theory.GroupTheory
