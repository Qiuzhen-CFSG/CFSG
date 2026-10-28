module
public import Theory.SpecificGroups.Suzuki.BorelPointwiseRigidity
public import Theory.SpecificGroups.Suzuki.BorelResidual
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Rigidity of a lifted Suzuki Borel residual

An automorphism fixing a Suzuki Borel is inner by a member of its Sylow
subgroup. A nonidentity such member has its centralizer inside that Sylow,
whereas the Borel contains a nontrivial odd complement. The automorphism
therefore is the identity.

The Borel is its own two-residual. Surjective transport consequently shows
that the residual of a Sylow normalizer in a two-core extension covers the
entire quotient Borel. Fixing that residual pointwise forces the induced
quotient automorphism to be trivial. The kernel is retained throughout.

Source: Huppert--Blackburn III, XI.3.3 and XI.3.10; GLS3, 2.6.5(e).
Application: Aschbacher--Smith, 13.6.27, printed p.934.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups
variable {H : Type*} [Group H] [Finite H] {m : ℕ}

/-- Pointwise fixation of a full Suzuki Borel forces identity. -/
theorem suzuki_aut_eq_one_of_fixing_borel (hm : 0 < m)
    (e : H ≃* SuzukiMatrixGroup m) (P : Sylow 2 H) (α : MulAut H)
    (hfix : ∀ x ∈ normalizer (P : Set H), α x = x) : α = 1 := by
  obtain ⟨g, hg, rfl⟩ := suzuki_aut_fixing_sylow_inner hm e P α
    (fun x hx => hfix x ((P : Subgroup H).le_normalizer hx))
  by_cases hg1 : g = 1
  · rw [hg1, map_one]
  obtain ⟨_, hc, D, ⟨eD⟩, hD, hi⟩ := suzukiSylow_borel_structure hm e P
  have hDP : D ≤ P := by
    intro x hx
    apply hc g hg hg1
    apply mem_centralizer_singleton_iff.mpr
    exact (mul_inv_eq_iff_eq_mul.mp (hfix x (hD ▸ mem_sup_right hx))).symm
  have hbot : D = ⊥ := bot_unique (by
    intro x hx
    exact hi ▸ (show x ∈ (P : Subgroup H) ⊓ D from ⟨hDP hx,hx⟩))
  have hcard : Nat.card D = 2 ^ (2 * m + 1) - 1 := by
    rw [Nat.card_congr eD.toEquiv]
    exact Nat.card_zmod _
  rw [hbot] at hcard
  have hpow : 8 ≤ 2 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ 2 * m + 1 by omega)
  have : Nat.card (⊥ : Subgroup H) = 1 := by simp
  omega

/-- Every prescribed Suzuki Sylow normalizer is its own two-residual. -/
theorem suzuki_sylowNormalizer_pResidual_eq_top (hm : 0 < m)
    (e : H ≃* SuzukiMatrixGroup m) (P : Sylow 2 H) :
    pResidual 2 (normalizer (P : Set H)) = ⊤ := by
  obtain ⟨f, _, hB⟩ := suzukiSylow_aligned_equiv hm e P
  let b := ((SuzukiBorelSubgroup m).equivMapOfInjective f.toMonoidHom f.injective).trans
    (MulEquiv.subgroupCongr hB)
  have h := map_pResidual_of_surjective 2 b.toMonoidHom b.surjective
  rw [suzukiBorel_pResidual_eq_top m hm, map_top_of_surjective _ b.surjective] at h
  exact h.symm

/-- The actual lifted Borel residual covers the full quotient Borel. -/
theorem suzuki_borelResidual_quotient_image (hm : 0 < m)
    (e : (H ⧸ pCore 2 H) ≃* SuzukiMatrixGroup m) (P : Sylow 2 H) :
    ((pResidual 2 (normalizer (P : Set H))).map
      (normalizer (P : Set H)).subtype).map (QuotientGroup.mk' (pCore 2 H)) =
      normalizer ((P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) :
        Set (H ⧸ pCore 2 H)) := by
  rw [map_embedded_pResidual,
    P.normalizer_map_surjective (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective (pCore 2 H))]
  have hr := suzuki_sylowNormalizer_pResidual_eq_top hm e
    (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)))
  rw [← (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))).coe_coe,
    Sylow.coe_mapSurjective] at hr
  rw [hr, ← MonoidHom.range_eq_map, range_subtype,
    ← (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))).coe_coe,
    Sylow.coe_mapSurjective]

/-- Fixing the lifted Borel residual annihilates the literal two-core quotient action. -/
theorem suzuki_quotientAut_eq_one_of_fixing_borelResidual (hm : 0 < m)
    (e : (H ⧸ pCore 2 H) ≃* SuzukiMatrixGroup m) (P : Sylow 2 H)
    (α : MulAut H)
    (hfix : ∀ x ∈ (pResidual 2 (normalizer (P : Set H))).map
      (normalizer (P : Set H)).subtype, α x = x) :
    (pCore 2 H).quotientAut α = 1 := by
  apply suzuki_aut_eq_one_of_fixing_borel hm e
    (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)))
  intro x hx
  rw [← suzuki_borelResidual_quotient_image hm e P] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [quotientAut_apply_mk, hfix y hy]

end BenderSuzuki.MatrixGroups
