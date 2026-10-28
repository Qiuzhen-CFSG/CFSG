module

public import Theory.GroupTheory.StronglyClosedTIFour
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Saturated

/-!
# The four-group step in the saturated branch

The literal fixed subgroup `U = C_E(j)` inside `J = C_G(j)` is elementary
abelian, TI and strongly closed in its normalizer. If `|U| = 4` and `M ∩ J`
is a two-group, the general strongly closed TI four-group theorem gives
`N_J(U) = J`. The established equality `N_J(U) = M ∩ J` then rules out the
escaping centralizer in the saturated branch.

This discharges the general four-group premise of the existing conditional
assembly. The two local action facts remain explicit and belong to the
independent local action calculation.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemma 1.1 and Lemma 2.8(1), printed pp.32, 35–36.
-/

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

universe u
variable {G : Type u} [Group G] [Finite G] {z g : G}

/-- Apply the general theorem to the literal four-group in the involution
centralizer, retaining precisely the two local action premises. -/
public theorem centralizerIntersection_normalizer_eq_top_of_card_four
    (h : Hypotheses z) (d : IntersectionData z g) (hs : FusionSaturated z g)
    (j : G) (hcard : Nat.card (centralizerIntersection z g j) = 4)
    (htwo : IsPGroup 2
      ((normalizer (coreIntersection z g : Set G)).subgroupOf (Centralizer j))) :
    normalizer (centralizerIntersection z g j : Set (Centralizer j)) = ⊤ := by
  have hne : centralizerIntersection z g j ≠ ⊥ := by
    intro he
    simp [he] at hcard
  have hnorm := centralizerIntersection_normalizer h d hs j hne
  exact normalizer_eq_top_of_stronglyClosed_ti_four (centralizerIntersection z g j)
    (centralizerIntersection_elementary d j) hcard
    (fun _ _ hx hx1 hax =>
      (centralizerIntersection_isTI h d hs j hne).mem_normalizer_of_conj_mem hx hx1 hax)
    (centralizerIntersection_stronglyClosed h d hs j hne) (hnorm.symm ▸ htwo)

/-- The saturated assembly now requires only the local action calculation;
the strongly closed TI four-group premise is fully discharged. -/
public theorem normalizer_eq_top_of_local_action
    (h : Hypotheses z) (d : IntersectionData z g) (hs : FusionSaturated z g)
    (local_action : ∀ j : G, j ∈ normalizer (coreIntersection z g : Set G) →
      orderOf j = 2 → j ∉ coreIntersection z g →
      Nat.card (centralizerIntersection z g j) = 4 ∧
        IsPGroup 2 ((normalizer (coreIntersection z g : Set G)).subgroupOf (Centralizer j))) :
    normalizer (coreIntersection z g : Set G) = ⊤ := by
  exact normalizer_eq_top_of_local_action_and_four_group h d hs local_action
    (fun _ _ _ U => normalizer_eq_top_of_stronglyClosed_ti_four U)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
