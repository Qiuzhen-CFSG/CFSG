module
public import CFSG.Quasithin.Chapter4.Section03.A5.SourceMaximality
public import Theory.GroupTheory.TwoGroupSquareChoice

/-!
# The outside Sylow choice supplies the source crossing element

The normalizer condition in T supplies t outside S=T∩H which normalizes S
and has square in S. Maximal-intersection uniqueness therefore applies to
the actual subgroup L S⟨t⟩. Every nontrivial two-subgroup normalized by
this subgroup has its whole normalizer in N(L).

These are the crossing choice and normalizer-control consequence of
Aschbacher–Smith 4.3.5, printed p.614. The separate maximal-core choice
in 4.3.4 is not asserted here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Chapter4
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The chosen source crossing element and its literal uniqueness subgroup. -/
theorem exists_source_crossing_counterexample
    (hblock : ChapterC.IsAlternatingBlock L 5)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ (H : Subgroup G) (t : G), IsMaximalTwoLocal H ∧ L ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧
      (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H) ∧
      t ∈ (T : Subgroup G) ∧ t ∉ (T : Subgroup G) ⊓ H ∧
      t ∈ normalizer ((T : Subgroup G) ⊓ H : Set G) ∧
      t ^ 2 ∈ (T : Subgroup G) ⊓ H ∧
      UniqueMaximalOvergroup (L ⊔ ((T : Subgroup G) ⊓ H ⊔ zpowers t))
        (normalizer (L : Set G)) ∧
      (∀ W : Subgroup G, IsPGroup 2 W → W ≠ ⊥ →
        L ⊔ ((T : Subgroup G) ⊓ H ⊔ zpowers t) ≤ normalizer (W : Set G) →
        normalizer (W : Set G) ≤ normalizer (L : Set G)) := by
  obtain ⟨H,hH,hLH,hout,hST,_hn,hP,hu⟩ :=
    d.exists_source_sylow_counterexample hblock hnot
  obtain ⟨t,ht,houtS,hn,hsq⟩ := exists_outside_normalizer_square_mem _ _ T.isPGroup' hST
  have hstrict : (T : Subgroup G) ⊓ H < (T : Subgroup G) ⊓ H ⊔ zpowers t := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hmem : t ∈ (T : Subgroup G) ⊓ H ⊔ zpowers t :=
      (le_sup_right : zpowers t ≤ (T : Subgroup G) ⊓ H ⊔ zpowers t) (mem_zpowers t)
    exact houtS (he.ge hmem)
  have huniq := hu _ hstrict (sup_le inf_le_left (zpowers_le.mpr ht))
  refine ⟨H,t,hH,hLH,hout,hP,ht,houtS,hn,hsq,huniq,?_⟩
  intro W hW hne hnormal
  exact normalizer_le_of_unique_maximalTwoLocal huniq.2.2 hW hne hnormal

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
