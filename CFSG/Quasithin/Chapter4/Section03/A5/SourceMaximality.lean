module
public import CFSG.Quasithin.Chapter4.Section01.OutsideSylowSelection
public import CFSG.Quasithin.Chapter4.Section03.A5.Normalizer
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel

/-!
# The original A₅ outside choice has a full Sylow intersection

Failure of uniqueness over L supplies a maximal two-local H outside N(L).
Maximizing |T ∩ H| gives local Sylow control and uniqueness over every
strict extension of T ∩ H inside T. The proved A₅ specialization of 4.3.1
then controls its full normalizer and promotes T ∩ H to Sylow in H.
Neither the strict-extension uniqueness nor the full Sylow conclusion
is retained as an extra hypothesis.

Source: Aschbacher–Smith 4.3.3(a) and the first assertion of (b),
printed pp.613–614. This does not assert the later component identification.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Chapter4
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The source choice in 4.3.3 has a literal ambient Sylow subgroup. -/
theorem exists_source_sylow_counterexample
    (hblock : ChapterC.IsAlternatingBlock L 5)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ H : Subgroup G, IsMaximalTwoLocal H ∧ L ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ⊓ H < (T : Subgroup G) ∧
      normalizer ((T : Subgroup G) ⊓ H : Set G) ≤ normalizer (L : Set G) ∧
      (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H) ∧
      ∀ X : Subgroup G, (T : Subgroup G) ⊓ H < X → X ≤ (T : Subgroup G) →
        UniqueMaximalOvergroup (L ⊔ X) (normalizer (L : Set G)) := by
  obtain ⟨H,hH,hLH,hne,hST,⟨P,hP⟩,hunique⟩ :=
    exists_maximal_sylow_intersection T d.source_unique_sylow_join le_rfl hnot
  have hindex : ¬ 2 ∣ ((T : Subgroup G) ⊓ H).relIndex
      (H ⊓ normalizer (L : Set G)) := by
    have he := relIndex_map_map_of_injective (P : Subgroup _) ⊤
      (H ⊓ normalizer (L : Set G)).subtype_injective
    simp only [← MonoidHom.range_eq_map,range_subtype,relIndex_top_right,hP] at he
    rw [he]
    exact P.not_dvd_index
  obtain ⟨Q,hQ⟩ := d.local_sylow
  have hQS : (Q : Subgroup L).map L.subtype ≤ (T : Subgroup G) ⊓ H := by
    rw [hQ]
    exact inf_le_inf_left _ hLH
  obtain ⟨hn,hfull⟩ := d.source_sylow_promotion hblock H _ hST Q hQS inf_le_right hindex hunique
  exact ⟨H,hH,hLH,(fun h => hne (hH.eq_of_le d.normalizer_maximal_twoLocal.1 h)),
    hST,hn,hfull,hunique⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
