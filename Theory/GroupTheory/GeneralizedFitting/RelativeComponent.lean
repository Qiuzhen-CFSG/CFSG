module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Components retained in an ambient group

A component of an overgroup is retained as a subgroup of the original group,
with its containment recorded. Restriction, subnormal ascent, and transport
under isomorphisms preserve that interpretation.

Source: the component calculus of GLS, vol. 2, Theorem 3.5 and Lemmas 3.9–3.10;
application: Aschbacher–Smith, §16.2, especially Lemma 16.2.7.
-/

@[expose] public section

namespace Theory.GroupTheory
open Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- An ordinary component of `M`, with its actual ambient containment. -/
def IsComponentIn (L M : Subgroup G) : Prop :=
  L ≤ M ∧ IsComponent M (L.subgroupOf M)

namespace IsComponentIn
variable {L M N : Subgroup G}

theorem quasisimple (h : IsComponentIn L M) : IsQuasisimple L := by
  let := h.2.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.1)

/-- A component is nontrivial, including when its center is nontrivial. -/
theorem ne_bot (h : IsComponentIn L M) : L ≠ ⊥ := by
  let := h.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact (nontrivial_iff_ne_bot L).mp this

/-- A quasisimple subgroup is an ordinary component of its own normalizer. -/
theorem normalizer (h : IsComponentIn L M) :
    IsComponentIn L (Subgroup.normalizer (L : Set G)) := by
  refine ⟨L.le_normalizer, (inferInstance :
    (L.subgroupOf (Subgroup.normalizer (L : Set G))).Normal).isSubnormal, ?_⟩
  let := h.quasisimple
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe L.le_normalizer).symm

theorem restrict (h : IsComponentIn L M) (hLN : L ≤ N) (hNM : N ≤ M) :
    IsComponentIn L N := by
  refine ⟨hLN, ?_, ?_⟩
  · have hs := h.2.1.comap (inclusion hNM)
    exact hs
  · let := h.quasisimple
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLN).symm

theorem of_subnormal (h : IsComponentIn L M) (hMN : M ≤ N)
    (hsub : (M.subgroupOf N).IsSubnormal) : IsComponentIn L N := by
  refine ⟨h.1.trans hMN, ?_, ?_⟩
  · have hs := h.2.1.comap (subgroupOfEquivOfLe hMN).toMonoidHom
    have he : (L.subgroupOf N).subgroupOf (M.subgroupOf N) =
        (L.subgroupOf M).comap (subgroupOfEquivOfLe hMN).toMonoidHom := by
      ext x
      rfl
    exact Subgroup.IsSubnormal.trans (by intro x hx; exact h.1 hx) (he.symm ▸ hs) hsub
  · let := h.quasisimple
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (h.1.trans hMN)).symm

theorem map (h : IsComponentIn L M) (e : G ≃* H) :
    IsComponentIn (L.map e.toMonoidHom) (M.map e.toMonoidHom) := by
  refine ⟨map_mono h.1, ?_, ?_⟩
  · have hs := h.2.1.map (f := (e.subgroupMap M).toMonoidHom) (e.subgroupMap M).surjective
    have he : (L.subgroupOf M).map (e.subgroupMap M).toMonoidHom =
        (L.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact mem_map_of_mem _ hy
      · rintro ⟨y, hy, he⟩
        exact ⟨⟨y, h.1 hy⟩, hy, Subtype.ext he⟩
    rwa [he] at hs
  · let := h.quasisimple
    let : IsQuasisimple (L.map e.toMonoidHom) :=
      IsQuasisimple.of_mulEquiv (e.subgroupMap L)
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (map_mono h.1)).symm

theorem commutator_eq_bot_of_ne (h : IsComponentIn L M) {J : Subgroup G}
    (hJ : IsComponentIn J M) (hne : L ≠ J) : ⁅L, J⁆ = ⊥ := by
  have hn : L.subgroupOf M ≠ J.subgroupOf M := by
    intro he
    apply hne
    simpa only [map_subgroupOf_eq_of_le h.1, map_subgroupOf_eq_of_le hJ.1]
      using congrArg (Subgroup.map M.subtype) he
  have hc := h.2.commutator_eq_bot_of_ne hJ.2 hn
  simpa only [map_commutator, map_subgroupOf_eq_of_le h.1,
    map_subgroupOf_eq_of_le hJ.1, Subgroup.map_bot] using congrArg (Subgroup.map M.subtype) hc

end IsComponentIn
end Theory.GroupTheory
end
