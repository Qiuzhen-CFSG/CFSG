module

public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeResidual
public import Theory.GroupAction.MarkedCubicClassTwo

/-!
# The actual marked involutions of F.6.16

The local symmetric-three quotient makes each cross-core involution invert
its cubic residual. Coprime kernel injectivity lifts this identity to the
original subgroup. Together with the opposite centralization and generation
proved in ThreeResidual, this supplies the full marked action on O²(G).

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
Lemma F.6.16, printed p.308 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
variable {G : Type*} [Group G] [Finite G]

private theorem symmetric_three_inverts :
    ∀ t x : Equiv.Perm (Fin 3), t ^ 2 = 1 → t ≠ 1 → x ^ 3 = 1 →
      t * x * t⁻¹ = x⁻¹ := by decide

omit [Finite G] in
private theorem local_inverts
    (he : Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)))
    (hL : IsPGroup 3 (pResidual 2 G)) (t : G) (ht : t ^ 2 = 1)
    (htQ : t ∉ pCore 2 G) (x : G) (hx : x ∈ pResidual 2 G) :
    t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨e⟩ := he
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := e.toMonoidHom.comp q
  have hinj : Function.Injective (q.subgroupMap (pResidual 2 G)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro y hy
    apply Subtype.ext
    have hyQ : (y : G) ∈ pCore 2 G := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    exact disjoint_def.mp (hL.disjoint_of_coprime pCore_isPGroup (by decide))
      y.property hyQ
  have ht' : f t ≠ 1 := by
    intro hh
    apply htQ
    apply (QuotientGroup.eq_one_iff _).mp
    exact e.injective (hh.trans (map_one e).symm)
  have hx' : (f x) ^ 3 = 1 := by
    have hc : Nat.card (pResidual 2 (Equiv.Perm (Fin 3))) = 3 :=
      (residual_of_symmetricThree (MulEquiv.refl _)).2
    have hm : f x ∈ pResidual 2 (Equiv.Perm (Fin 3)) :=
      map_pResidual_le 2 f (mem_map_of_mem _ hx)
    exact congrArg Subtype.val (show (⟨f x, hm⟩ : pResidual 2 _) ^ 3 = 1 by
      simpa only [hc] using pow_card_eq_one' (x := (⟨f x, hm⟩ : pResidual 2 _)))
  have hh : q (t * x * t⁻¹) = q x⁻¹ := by
    apply e.injective
    change f (t * x * t⁻¹) = f x⁻¹
    simpa only [map_mul, map_inv] using
      symmetric_three_inverts (f t) (f x) (by rw [← map_pow, ht, map_one]) ht' hx'
  exact congrArg Subtype.val (hinj (Subtype.ext hh :
    q.subgroupMap (pResidual 2 G) ⟨t * x * t⁻¹, Subgroup.Normal.conj_mem inferInstance x hx t⟩ =
    q.subgroupMap (pResidual 2 G) ⟨x⁻¹, inv_mem hx⟩))

variable {G₁ G₂ : Subgroup G}

theorem local_residual_inverted (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G))
    (t : G) (ht : t ∈ G₁) (ht2 : t ^ 2 = 1)
    (htQ : t ∉ (pCore 2 G₁).map G₁.subtype)
    (x : G) (hx : x ∈ (pResidual 2 G₁).map G₁.subtype) :
    t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hi := map_pResidual_le 2 G₁.subtype
  have hp := hL.of_injective (inclusion hi) (inclusion_injective hi)
  have hp' : IsPGroup 3 (pResidual 2 G₁) :=
    hp.of_equiv (equivMapOfInjective _ G₁.subtype G₁.subtype_injective).symm
  exact congrArg Subtype.val (local_inverts h.quotient_left hp' ⟨t, ht⟩
    (Subtype.ext ht2) (fun hm => htQ ⟨⟨t, ht⟩, hm, rfl⟩) y hy)

theorem exists_residual_cubic_marking (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hL : IsPGroup 3 (pResidual 2 G))
    (hnot : ¬ Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2))) :
    ∃ t₁ t₂ : G, t₁ ∈ G₁ ⊓ G₂ ∧ t₂ ∈ G₁ ⊓ G₂ ∧
      orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧ Commute t₁ t₂ ∧
      MarkedCubicClassTwo.CubicMarking
        (((pResidual 2 G₁).map G₁.subtype).subgroupOf (pResidual 2 G))
        (((pResidual 2 G₂).map G₂.subtype).subgroupOf (pResidual 2 G))
        (MulAut.conjNormal t₁) (MulAut.conjNormal t₂) := by
  obtain ⟨t₁, t₂, ht₁Q, ht₁n, ht₂Q, ht₂n, ho₁, ho₂, hc, hfix₁, hfix₂⟩ :=
    exists_marked_commuting_involutions h hcore hL hnot
  have ht₁ : t₁ ∈ G₁ ⊓ G₂ := by
    simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection ht₁Q
  have ht₂ : t₂ ∈ G₁ ⊓ G₂ := h.local_twoCore_le_intersection ht₂Q
  have hs₁ : t₁ ^ 2 = 1 := ho₁ ▸ pow_orderOf_eq_one t₁
  have hs₂ : t₂ ^ 2 = 1 := ho₂ ▸ pow_orderOf_eq_one t₂
  refine ⟨t₁, t₂, ht₁, ht₂, ho₁, ho₂, hc, ?_⟩
  constructor
  · rw [Nat.card_congr (subgroupOfEquivOfLe (map_pResidual_le 2 G₁.subtype)).toEquiv]
    exact local_residual_card_three h hL
  · rw [Nat.card_congr (subgroupOfEquivOfLe (map_pResidual_le 2 G₂.subtype)).toEquiv]
    exact local_residual_card_three h.symm hL
  · apply map_injective (pResidual 2 G).subtype_injective
    rw [Subgroup.map_sup,
      map_subgroupOf_eq_of_le (map_pResidual_le 2 G₁.subtype),
      map_subgroupOf_eq_of_le (map_pResidual_le 2 G₂.subtype),
      ← MonoidHom.range_eq_map, range_subtype]
    exact h.twoResidual_eq_sup.symm
  · rw [← map_pow, hs₁, map_one]
  · rw [← map_pow, hs₂, map_one]
  · exact hc.map MulAut.conjNormal
  · intro x hx
    apply Subtype.ext
    exact local_residual_inverted h hL t₁ ht₁.1 hs₁ ht₁n x hx
  · intro x hx
    apply Subtype.ext
    change t₁ * x.val * t₁⁻¹ = x.val
    rw [← (mem_centralizer_iff.mp hfix₁ x hx), mul_inv_cancel_right]
  · intro x hx
    apply Subtype.ext
    change t₂ * x.val * t₂⁻¹ = x.val
    rw [← (mem_centralizer_iff.mp hfix₂ x hx), mul_inv_cancel_right]
  · intro x hx
    apply Subtype.ext
    exact local_residual_inverted h.symm hL t₂ ht₂.2 hs₂ ht₂n x hx

end CFSG.Quasithin.ChapterF.Noncyclic
