module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockGeometry
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockSubnormalOrders

/-!
# The invariant cubic Hall–Janko local

Use the normal closure of the prescribed Sylow subgroup inside its second
radical normalizer. Its quotient is S₃, while the full normalizer has quotient
S₃ × C₃. Stabilizing the Sylow subgroup preserves its characteristic radical,
its full normalizer, and this relative normal closure. The existing generated
pair proves that adjoining the central-involution centralizer gives all J₂.
The same order-64 radical makes this narrower local characteristic two.

This is the local seed used in Aschbacher–Smith E.6.8, printed p.248.
All models and Sylow markings are the original ATLAS degree-100 carrier.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.CubicBlockGeometry
open Subgroup Theory.GroupTheory Seed PairNormalizer
noncomputable section

structure CubicSeed (R : Sylow 2 Carrier) (α : MulAut Carrier) where
  localSubgroup : Subgroup Carrier
  modelIso : localSubgroup ≃* l₂
  sylow_le : (R : Subgroup Carrier) ≤ localSubgroup
  invariant : ∀ β : MulAut Carrier,
    (R : Subgroup Carrier).map β.toMonoidHom = R →
      localSubgroup.map β.toMonoidHom = localSubgroup
  selfCentralizing : centralizer (pCore 2 localSubgroup : Set localSubgroup) ≤
    pCore 2 localSubgroup
  generated : α.fixedSubgroup ⊔ localSubgroup = ⊤

theorem l₂_selfCentralizing : centralizer (pCore 2 l₂ : Set l₂) ≤ pCore 2 l₂ := by
  rw [SecondParabolic.l₂_core_eq]
  intro x hx
  apply RankOneFourNormalizer.centralizer_le_q₂
  intro y hy
  exact congrArg Subtype.val (hx ⟨y, q₂_le_l₂ hy⟩ hy)

theorem l₂_invariant (β : MulAut Carrier) (hβ : s.map β.toMonoidHom = s) :
    l₂.map β.toMonoidHom = l₂ := by
  have hp := BlockGeometry.p₂_invariant β hβ
  let f : MulAut p₂ := (β.subgroupMap p₂).trans (MulEquiv.subgroupCongr hp)
  have hf : p₂.subtype.comp f.toMonoidHom = β.toMonoidHom.comp p₂.subtype := rfl
  have hs : (s.subgroupOf p₂).map f.toMonoidHom = s.subgroupOf p₂ := by
    apply map_injective (f := p₂.subtype) p₂.subtype_injective
    rw [map_map, hf, ← map_map, map_subgroupOf_eq_of_le s_le_p₂, hβ]
  have hn := map_normalClosure (s.subgroupOf p₂ : Set p₂) f.toMonoidHom f.surjective
  rw [← coe_map, hs] at hn
  have hh := congrArg (map p₂.subtype) hn
  rw [map_map, hf, ← map_map] at hh
  exact hh

/-- An inner involution fixing the Sylow subgroup has the marked centralizer. -/
theorem marked_cubic_generated (α : MulAut Carrier) (ho : orderOf α = 2)
    (hi : α ∈ (MulAut.conj (G := Carrier)).range)
    (hf : ∀ r ∈ s, α r = r) : α.fixedSubgroup ⊔ l₂ = ⊤ := by
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
  rw [hfixed]
  have h := SecondParabolic.Overlap.L_generate FirstParabolic.card_l₁ card_p₂
  change (l₁ ⊔ l₂) ⊔ s = ⊤ at h
  rwa [sup_eq_left.mpr (SecondParabolic.s_le_l₁.trans le_sup_left)] at h

private theorem map_pullback (e β : MulAut Carrier) (U : Subgroup Carrier) :
    U.map (e.trans (β.trans e.symm)).toMonoidHom =
      ((U.map e.toMonoidHom).map β.toMonoidHom).map e.symm.toMonoidHom := by
  rw [map_map, map_map]
  rfl

/-- Transport the full parabolic and its action along a Sylow conjugator. -/
theorem seed (R : Sylow 2 Carrier) (α : MulAut Carrier) (ho : orderOf α = 2)
    (hi : α ∈ (MulAut.conj (G := Carrier)).range)
    (hf : ∀ r ∈ (R : Subgroup Carrier), α r = r) : Nonempty (CubicSeed R α) := by
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
    localSubgroup := l₂.map e.toMonoidHom
    modelIso := (e.subgroupMap l₂).symm
    sylow_le := ?_
    invariant := ?_
    selfCentralizing := ?_
    generated := ?_ }⟩
  · rw [← hR]
    exact map_mono s_le_l₂
  · intro β hβ
    let b : MulAut Carrier := e.trans (β.trans e.symm)
    have hb : s.map b.toMonoidHom = s := by rw [map_pullback, hR, hβ, hRinv]
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    calc
      ((l₂.map e.toMonoidHom).map β.toMonoidHom).map e.symm.toMonoidHom =
          l₂.map b.toMonoidHom := (map_pullback e β l₂).symm
      _ = l₂ := l₂_invariant b hb
      _ = (l₂.map e.toMonoidHom).map e.symm.toMonoidHom := by simp [map_map]
  · exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e l₂).mpr l₂_selfCentralizing
  · have hfixed : a.fixedSubgroup.map e.toMonoidHom = α.fixedSubgroup := by
      ext x
      rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
      change e.symm (α (e (e.symm x))) = e.symm x ↔ α x = x
      rw [e.apply_symm_apply]
      exact e.symm.injective.eq_iff
    rw [← hfixed, ← Subgroup.map_sup, marked_cubic_generated a hao hai ha,
      map_top_of_surjective _ e.surjective]

/-- The canonical local inherits the genuine full-normalizer block orders. -/
theorem subnormal_orders :
    ∀ E : Subgroup l₂, E.IsSubnormal → IsPPerfect 2 E →
      Nat.card E = 1 ∨
        (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
          Nat.card (E ⧸ pCore 2 E) = 9 := by
  intro E hE hp
  let f : l₂ →* l₂.subgroupOf p₂ := (subgroupOfEquivOfLe l₂_le_p₂).symm.toMonoidHom
  let F := (E.map f).map (l₂.subgroupOf p₂).subtype
  have hF : F.IsSubnormal := (hE.map (subgroupOfEquivOfLe l₂_le_p₂).symm.surjective).trans'
    l₂_normal_in_p₂.isSubnormal
  let e : E ≃* F := (E.equivMapOfInjective f (subgroupOfEquivOfLe l₂_le_p₂).symm.injective).trans
    ((E.map f).equivMapOfInjective _ (l₂.subgroupOf p₂).subtype_injective)
  have hperf : IsPPerfect 2 F := hp.of_surjective e.toMonoidHom e.surjective
  have hcard : Nat.card E = Nat.card F := Nat.card_congr e.toEquiv
  have hquot : Nat.card (E ⧸ pCore 2 E) = Nat.card (F ⧸ pCore 2 F) :=
    Nat.card_congr (LocalCoreTransport.quotientEquiv 2 e).toEquiv
  rw [hcard, hquot]
  exact BlockSubnormalOrders.subnormal_orders F hF hperf

end
end Sporadic.LeechRelated.J2.ExceptionalParabolics.CubicBlockGeometry
