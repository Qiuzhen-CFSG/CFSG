module

public import Theory.GroupTheory.BaerSuzukiSubgroup
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Baer–Suzuki inside a specified overgroup

The conjugating elements in the subgroup criterion can be restricted to an
overgroup `H`; the conclusion then concerns the embedded core `H.pCoreIn p`.
Transport through `H.subtype` retains the literal ambient conjugate subgroups.
Commuting pairs already generate a p-group, so only noncommuting pairs need
to be checked.

The application is the last paragraph of Aschbacher–Smith, Lemma 7.6.1,
combined manuscript of 1 March 2004, printed p.703. There the overgroup is
the centralizer of a line, rather than the ambient simple group.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Relative Baer–Suzuki, with all conjugate joins viewed in the original group. -/
theorem le_pCoreIn_of_conjugate_sup_isPGroup
    (H V : Subgroup G) (hVH : V ≤ H) (hV : IsPGroup p V)
    (hpair : ∀ g ∈ H,
      IsPGroup p (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    V ≤ H.pCoreIn p := by
  let W := V.subgroupOf H
  have hW : W.map H.subtype = V := map_subgroupOf_eq_of_le hVH
  have hconj (g : H) :
      (W.map (MulAut.conj g).toMonoidHom).map H.subtype =
        V.map (MulAut.conj (g : G)).toMonoidHom := by
    have hf : H.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := by ext x; rfl
    rw [map_map, hf, ← map_map, hW]
  have hcore : W ≤ pCore p H := by
    apply le_pCore_of_conjugate_sup_isPGroup W hV.comap_subtype
    intro g
    have himage : IsPGroup p ((W ⊔ W.map (MulAut.conj g).toMonoidHom).map H.subtype) := by
      rw [map_sup, hW, hconj]
      exact hpair g g.property
    have hp := himage.comap_of_injective H.subtype H.subtype_injective
    rwa [comap_map_eq_self_of_injective H.subtype_injective] at hp
  have hm := map_mono (f := H.subtype) hcore
  rwa [hW] at hm

/-- It suffices to check conjugates that do not centralize the original subgroup. -/
theorem le_pCoreIn_of_noncentralizing_conjugate_sup_isPGroup
    (H V : Subgroup G) (hVH : V ≤ H) (hV : IsPGroup p V)
    (hpair : ∀ g ∈ H,
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      IsPGroup p (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    V ≤ H.pCoreIn p := by
  classical
  apply le_pCoreIn_of_conjugate_sup_isPGroup H V hVH hV
  intro g hg
  by_cases hc : V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)
  · exact hV.to_sup_of_normal_left' (hV.map _) (hc.trans (centralizer_le_normalizer _))
  · exact hpair g hg hc

/-- Escape from the local core supplies a noncommuting pair that is not a p-group. -/
theorem exists_noncentralizing_conjugate_sup_not_isPGroup
    (H V : Subgroup G) (hVH : V ≤ H) (hV : IsPGroup p V)
    (hcore : ¬ V ≤ H.pCoreIn p) :
    ∃ g ∈ H, ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) ∧
      ¬ IsPGroup p (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  classical
  by_contra hn
  apply hcore (le_pCoreIn_of_noncentralizing_conjugate_sup_isPGroup H V hVH hV ?_)
  intro g hg hc
  by_contra hp
  exact hn ⟨g, hg, hc, hp⟩

end Subgroup
