module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Saturated.Centralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Saturated.LocalAction
public import Theory.GroupTheory.StronglyClosedTIFour

/-!
# Global normality in the saturated elementary-eight branch

Strong closure and trivial intersections reduce global normality of E to
the escaping involution centralizer J. The local action calculation gives
|C_E(j)| = 4 with C_M(j) a two-group. The strongly closed TI four-group
theorem then forces J ≤ M, contradicting the chosen escape.

`FusionSaturated.normalizer_eq_top` discharges both inputs of the retained
conditional assembly. It assumes only the original local hypotheses,
`IntersectionData`, and saturation; no ambient normality or simplicity is
assumed. The local intersection data remain the earlier source step.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), the global normalizer assertion of Lemma 2.8(1), printed pp.35–36.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {z g : G}

/-- Conditional assembly of the saturated branch. The two remaining inputs are
local involution action and the strongly closed TI four-group theorem. -/
theorem normalizer_eq_top_of_local_action_and_four_group
    (h : Hypotheses z) (d : IntersectionData z g) (hs : FusionSaturated z g)
    (local_action : ∀ j : G, j ∈ normalizer (coreIntersection z g : Set G) →
      orderOf j = 2 → j ∉ coreIntersection z g →
      Nat.card (centralizerIntersection z g j) = 4 ∧
        IsPGroup 2 ((normalizer (coreIntersection z g : Set G)).subgroupOf (Centralizer j)))
    (four_group : ∀ (K : Type u) [Group K] [Finite K] (U : Subgroup K),
      IsElementaryAbelian 2 U → Nat.card U = 4 →
      (∀ a x : K, x ∈ U → x ≠ 1 → a * x * a⁻¹ ∈ U → a ∈ normalizer (U : Set K)) →
      IsStronglyClosedSet (U : Set K) (normalizer (U : Set K)) ⊤ →
      IsPGroup 2 (normalizer (U : Set K)) → normalizer (U : Set K) = ⊤) :
    normalizer (coreIntersection z g : Set G) = ⊤ := by
  classical
  by_contra hproper
  obtain ⟨j, hjM, hj2, hjE, hjC⟩ := exists_escaping_involution_centralizer h d hs hproper
  obtain ⟨hcard, htwo⟩ := local_action j hjM hj2 hjE
  have hne : centralizerIntersection z g j ≠ ⊥ := by
    intro he
    simp [he] at hcard
  have hnorm := centralizerIntersection_normalizer h d hs j hne
  have htop := four_group (Centralizer j) (centralizerIntersection z g j)
    (centralizerIntersection_elementary d j) hcard
    (fun _ _ hx hx1 hax => (centralizerIntersection_isTI h d hs j hne).mem_normalizer_of_conj_mem
      hx hx1 hax)
    (centralizerIntersection_stronglyClosed h d hs j hne) (hnorm.symm ▸ htwo)
  exact hjC (subgroupOf_eq_top.mp (hnorm.symm.trans htop))

/-- The global normalizer assertion of Aschbacher's Lemma 2.8(1).
The local action and strongly closed TI four-group premises are both proved;
the earlier local intersection facts are supplied by `d`. -/
theorem FusionSaturated.normalizer_eq_top
    (h : Hypotheses z) (d : IntersectionData z g) (hs : FusionSaturated z g) :
    normalizer (coreIntersection z g : Set G) = ⊤ := by
  exact normalizer_eq_top_of_local_action_and_four_group h d hs
    (fun _ hj hj2 hjE => centralizerIntersection_local_action d hj hj2 hjE)
    (fun _ _ _ U => normalizer_eq_top_of_stronglyClosed_ti_four U)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition

end
