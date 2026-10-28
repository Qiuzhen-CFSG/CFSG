module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.SylowCenter
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap.Inner
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.Definitions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer.Centralizer
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.Quasithin.EvenCharacteristic

/-!
# Invariant Hall–Janko second-parabolic geometry

The checked order-64 radical is characteristic in the marked Sylow subgroup,
so every automorphism stabilizing that Sylow subgroup preserves its full
normalizer. The radical centralizer calculation gives characteristic two.
An inner involution fixing the Sylow subgroup comes from its center of order
two, so its fixed subgroup is the first parabolic. The checked pair generates
the unchanged ATLAS degree-100 carrier. Sylow conjugacy transports all these
markings together to any prescribed Sylow subgroup.

This supplies the intrinsic geometry for Aschbacher–Smith 2.3.9(7), printed
p.526. It reuses the parabolics of F.1.12(I)(10), p.263, including the full
second normalizer and its two-core of order 64. It makes no assertion about
short subnormal blocks; that additional calculation belongs to the consumer.
The ATLAS provenance is retained in the imported construction modules.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockGeometry
open Subgroup Theory.GroupTheory Seed PairNormalizer
noncomputable section

/-- The actual full second parabolic with its prescribed Sylow and action. -/
structure LocalSeed (R : Sylow 2 Carrier) (α : MulAut Carrier) where
  localSubgroup : Subgroup Carrier
  modelIso : localSubgroup ≃* p₂
  sylow_le : (R : Subgroup Carrier) ≤ localSubgroup
  invariant : ∀ β : MulAut Carrier,
    (R : Subgroup Carrier).map β.toMonoidHom = R →
      localSubgroup.map β.toMonoidHom = localSubgroup
  selfCentralizing : centralizer (pCore 2 localSubgroup : Set localSubgroup) ≤
    pCore 2 localSubgroup
  generated : α.fixedSubgroup ⊔ localSubgroup = ⊤

/-- Faithfulness of conjugation makes the concrete carrier centerless. -/
theorem center_eq_bot : center Carrier = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply NormalizerAction.inner_conj_injective
  apply MulEquiv.ext
  intro y
  change x * y * x⁻¹ = 1 * y * 1⁻¹
  rw [← mem_center_iff.mp hx y, mul_inv_cancel_right]
  simp

/-- The intrinsic two-core of the full second normalizer is self-centralizing. -/
theorem p₂_selfCentralizing : centralizer (pCore 2 p₂ : Set p₂) ≤ pCore 2 p₂ := by
  rw [p₂_core_eq_q₂ SecondParabolic.l₂_core_card]
  intro x hx
  apply RankOneFourNormalizer.centralizer_le_q₂
  intro y hy
  exact congrArg Subtype.val (hx ⟨y, q₂.le_normalizer hy⟩ hy)

/-- Retain the order of the full normalizer's actual two-core. -/
theorem p₂_core_card : Nat.card (pCore 2 p₂) = 64 :=
  (p₂_core_and_quotient SecondParabolic.l₂_core_card).1

/-- Relative characteristicity gives invariance under all Sylow stabilizers. -/
theorem q₂_invariant (β : MulAut Carrier) (hβ : s.map β.toMonoidHom = s) :
    q₂.map β.toMonoidHom = q₂ := by
  let f : MulAut s := (β.subgroupMap s).trans (MulEquiv.subgroupCongr hβ)
  have hq := characteristic_iff_map_eq.mp q₂_characteristic f
  have hh := congrArg (Subgroup.map s.subtype) hq
  have hf : s.subtype.comp f.toMonoidHom = β.toMonoidHom.comp s.subtype := rfl
  rw [map_map, hf, ← map_map, map_subgroupOf_eq_of_le q₂_le_s] at hh
  exact hh

/-- Its full normalizer inherits the same invariance. -/
theorem p₂_invariant (β : MulAut Carrier) (hβ : s.map β.toMonoidHom = s) :
    p₂.map β.toMonoidHom = p₂ := by
  change (normalizer (q₂ : Set Carrier)).map β.toMonoidHom = normalizer (q₂ : Set Carrier)
  rw [map_equiv_normalizer_eq, q₂_invariant β hβ]

/-- An inner involution fixing the Sylow subgroup has the marked centralizer. -/
theorem marked_generated (α : MulAut Carrier) (ho : orderOf α = 2)
    (hi : α ∈ (MulAut.conj (G := Carrier)).range)
    (hf : ∀ r ∈ s, α r = r) : α.fixedSubgroup ⊔ p₂ = ⊤ := by
  obtain ⟨t, rfl⟩ := hi
  have ht : orderOf t = 2 :=
    (orderOf_injective MulAut.conj NormalizerAction.inner_conj_injective t).symm.trans ho
  have hc : t ∈ centralizer (s : Set Carrier) := by
    intro r hr
    have he : t * r * t⁻¹ = r := hf r hr
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; rfl)
  have hs : t ∈ s := by
    have hn : t ∈ normalizer (s : Set Carrier) := centralizer_le_normalizer (s : Set Carrier) hc
    have he := hp.inf_normalizer_sylow (SecondParabolic.sylow FirstParabolic.card_l₁)
    exact (show t ∈ zpowers t ⊓ s from he ▸ ⟨mem_zpowers t, hn⟩).2
  have hz : t ∈ (center s).map s.subtype :=
    ⟨⟨t, hs⟩, mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)), rfl⟩
  rw [SecondParabolic.center_s] at hz
  have he : t = GeneratorPair.FirstFusion.t := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
    have hcases : GeneratorPair.FirstFusion.t ^ k = 1 ∨
        GeneratorPair.FirstFusion.t ^ k = GeneratorPair.FirstFusion.t := by
      rw [← zpow_mod_orderOf, SecondParabolic.central_involution_order]
      have hb := Int.emod_nonneg k (by decide : (2 : ℤ) ≠ 0)
      have hu := Int.emod_lt_of_pos k (by decide : (0 : ℤ) < 2)
      interval_cases (k % 2) <;> simp
    rcases hcases with h1 | h1
    · have ht1 : t = 1 := hk.symm.trans h1
      rw [ht1, orderOf_one] at ht
      norm_num at ht
    · exact hk.symm.trans h1
  have hfixed : (MulAut.conj t).fixedSubgroup = l₁ := by
    rw [he]
    ext x
    rw [MulAut.mem_fixedSubgroup]
    change Seed.z * x * Seed.z⁻¹ = x ↔ x ∈ centralizer ({Seed.z} : Set Carrier)
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.trans eq_comm
  rw [hfixed, SecondParabolic.Overlap.l₁_sup_p₂]

private theorem map_pullback (e β : MulAut Carrier) (U : Subgroup Carrier) :
    U.map (e.trans (β.trans e.symm)).toMonoidHom =
      ((U.map e.toMonoidHom).map β.toMonoidHom).map e.symm.toMonoidHom := by
  rw [map_map, map_map]
  rfl

/-- Transport the full parabolic and its action along a Sylow conjugator. -/
theorem seed (R : Sylow 2 Carrier) (α : MulAut Carrier) (ho : orderOf α = 2)
    (hi : α ∈ (MulAut.conj (G := Carrier)).range)
    (hf : ∀ r ∈ (R : Subgroup Carrier), α r = r) : Nonempty (LocalSeed R α) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier
    (SecondParabolic.sylow FirstParabolic.card_l₁) R
  let e := MulAut.conj g
  have hR : s.map e.toMonoidHom = (R : Subgroup Carrier) := by
    change ((g • SecondParabolic.sylow FirstParabolic.card_l₁ : Sylow 2 Carrier) :
      Subgroup Carrier) = R
    rw [hg]
  have hRinv : (R : Subgroup Carrier).map e.symm.toMonoidHom = s := by
    rw [← hR]
    simp [map_map]
  let a : MulAut Carrier := e.trans (α.trans e.symm)
  have ha : ∀ r ∈ s, a r = r := by
    intro r hr
    have hm : e r ∈ (R : Subgroup Carrier) := hR ▸ mem_map_of_mem e.toMonoidHom hr
    change e.symm (α (e r)) = r
    rw [hf _ hm, e.symm_apply_apply]
  have hao : orderOf a = 2 := by
    have he : a = (MulAut.congr e.symm) α := rfl
    rw [he, MulEquiv.orderOf_eq, ho]
  have hai : a ∈ (MulAut.conj (G := Carrier)).range := by
    obtain ⟨t, ht⟩ := hi
    refine ⟨e.symm t, ?_⟩
    apply MulEquiv.ext
    intro x
    change e.symm t * x * (e.symm t)⁻¹ = e.symm (α (e x))
    rw [← ht]
    simp only [MulAut.conj_apply, map_mul, map_inv, e.symm_apply_apply]
  refine ⟨{
    localSubgroup := p₂.map e.toMonoidHom
    modelIso := (e.subgroupMap p₂).symm
    sylow_le := ?_
    invariant := ?_
    selfCentralizing := ?_
    generated := ?_ }⟩
  · rw [← hR]
    exact map_mono s_le_p₂
  · intro β hβ
    let b : MulAut Carrier := e.trans (β.trans e.symm)
    have hb : s.map b.toMonoidHom = s := by rw [map_pullback, hR, hβ, hRinv]
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    calc
      ((p₂.map e.toMonoidHom).map β.toMonoidHom).map e.symm.toMonoidHom =
          p₂.map b.toMonoidHom := (map_pullback e β p₂).symm
      _ = p₂ := p₂_invariant b hb
      _ = (p₂.map e.toMonoidHom).map e.symm.toMonoidHom := by simp [map_map]
  · exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e p₂).mpr p₂_selfCentralizing
  · have hfixed : a.fixedSubgroup.map e.toMonoidHom = α.fixedSubgroup := by
      ext x
      rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
      change e.symm (α (e (e.symm x))) = e.symm x ↔ α x = x
      rw [e.apply_symm_apply]
      exact e.symm.injective.eq_iff
    rw [← hfixed, ← Subgroup.map_sup, marked_generated a hao hai ha,
      map_top_of_surjective _ e.surjective]

end
end Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockGeometry
