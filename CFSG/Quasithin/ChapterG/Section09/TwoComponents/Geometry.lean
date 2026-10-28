module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The distinct component pair in G.9.3

The strict inequality `L < H` selects two distinct components from the
source hypothesis. Distinct components commute, so their multiplication
defines an actual homomorphism onto their join. The elementary actor has
trivial intersection with the centralizer of that join by irreducibility.
None of these statements asserts that the components are centerless.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L H : Subgroup G} {m : ℕ}

omit [Finite G] in
/-- Multiplication of the commuting factors, before any centerlessness or
direct-product claim. -/
@[expose] def productMap {L₂ : Subgroup G} (hc : ⁅L, L₂⁆ = ⊥) : L × L₂ →* G :=
  L.subtype.noncommCoprod L₂.subtype fun l j =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc l.property) j j.property).symm

omit [Finite G] in
theorem productMap_range {L₂ : Subgroup G} (hc : ⁅L, L₂⁆ = ⊥) :
    (productMap hc).range = L ⊔ L₂ := by
  simpa only [productMap, Subgroup.range_subtype] using
    (MonoidHom.noncommCoprod_range L.subtype L₂.subtype _)

omit [Finite G] in
/-- Trivial intersection, when supplied by the component-model restrictions,
makes the multiplication map an isomorphism to the actual join. -/
noncomputable def productEquiv {L₂ : Subgroup G} (hc : ⁅L, L₂⁆ = ⊥)
    (hd : Disjoint L L₂) : L × L₂ ≃* (L ⊔ L₂ : Subgroup G) :=
  (MonoidHom.ofInjective
    ((MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨L.subtype_injective, L₂.subtype_injective,
        by simpa only [Subgroup.range_subtype] using hd⟩)).trans
    (MulEquiv.subgroupCongr (productMap_range hc))

/-- The strict source branch supplies a distinct, commuting, isomorphic pair,
with the original quasiequivalence (including the permitted dual) retained. -/
theorem exists_component_pair (h : ComponentHypothesis K ρ A L H m)
    (hLH : L < H) :
    ∃ L₂ : Subgroup G, Theory.GroupTheory.IsComponent G L₂ ∧
      H = L ⊔ L₂ ∧ L ≠ L₂ ∧ ⁅L, L₂⁆ = ⊥ ∧ Nonempty (L ≃* L₂) ∧
      (Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
       Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype))) := by
  rcases h.components with heq | ⟨L₂, hL₂, hH, hq⟩
  · exact (hLH.ne heq.symm).elim
  · have hne : L ≠ L₂ := by
      intro heq
      rw [← heq, sup_idem] at hH
      exact hLH.ne hH.symm
    refine ⟨L₂, hL₂, hH, hne, h.component.commutator_eq_bot_of_ne hL₂ hne, ?_, hq⟩
    rcases hq with ⟨e, _, _⟩ | ⟨e, _, _⟩ <;> exact ⟨e⟩

/-- Even if the actor interchanges the components, it acts faithfully by
conjugation on their normal irreducibly acting join. -/
theorem actor_centralizer_eq_bot (h : ComponentHypothesis K ρ A L H m) :
    A ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
  let : Representation.IsIrreducible (ρ.comp H.subtype) := h.irreducible
  let : IsElementaryAbelian 2 A := h.elementary
  apply le_bot_iff.mp
  intro x hx
  exact Subgroup.mem_bot.mpr
    (Representation.BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
      ρ H h.faithful (elemPow_eq_one_of_isElementaryAbelian x hx.1) hx.2)

/-- The original actor embeds into the automorphism group of the whole join;
normality of either individual component is unnecessary. -/
theorem actor_rank_le_join_automorphisms (h : ComponentHypothesis K ρ A L H m) :
    m ≤ primeRank 2 (MulAut H) := by
  let : Representation.IsIrreducible (ρ.comp H.subtype) := h.irreducible
  apply h.toSetup.rank_le_automorphisms
  rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
  exact le_top

end CFSG.Quasithin.ChapterG.Section09.TwoComponents
