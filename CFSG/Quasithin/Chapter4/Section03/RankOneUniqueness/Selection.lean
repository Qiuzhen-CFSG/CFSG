module
public import CFSG.Quasithin.Chapter4.Section01.OutsideSylowSelection
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Normalizer
public import Theory.GroupTheory.TwoGroupSquareChoice

/-!
# The original rank-one outside choice has a full Sylow intersection

Failure of uniqueness over L supplies a maximal two-local H outside N(L).
Maximizing |T ∩ H| gives local Sylow control and uniqueness over every
strict extension of T ∩ H inside T. The proved binary rank-one specialization of 4.3.1
then controls its full normalizer and promotes T ∩ H to Sylow in H.
Neither the strict-extension uniqueness nor the full Sylow conclusion
is retained as an extra hypothesis.

Source: Aschbacher–Smith 4.3.3(a) and the first assertion of (b),
printed pp.613–614. This does not assert the later component identification.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
include D h hpsl

/-- The source choice in 4.3.3 has a literal ambient Sylow subgroup. -/
theorem exists_source_sylow_counterexample
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ H : Subgroup G, IsMaximalTwoLocal H ∧ L ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ⊓ H < (T : Subgroup G) ∧
      normalizer ((T : Subgroup G) ⊓ H : Set G) ≤ normalizer (L : Set G) ∧
      (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H) ∧
      ∀ X : Subgroup G, (T : Subgroup G) ⊓ H < X → X ≤ (T : Subgroup G) →
        UniqueMaximalOvergroup (L ⊔ X) (normalizer (L : Set G)) := by
  obtain ⟨H,hH,hLH,hne,hST,⟨P,hP⟩,hunique⟩ :=
    exists_maximal_sylow_intersection T (unique_sylow_join D h) le_rfl hnot
  have hindex : ¬ 2 ∣ ((T : Subgroup G) ⊓ H).relIndex
      (H ⊓ normalizer (L : Set G)) := by
    have he := relIndex_map_map_of_injective (P : Subgroup _) ⊤
      (H ⊓ normalizer (L : Set G)).subtype_injective
    simp only [← MonoidHom.range_eq_map,range_subtype,relIndex_top_right,hP] at he
    rw [he]
    exact P.not_dvd_index
  obtain ⟨Q,hQ⟩ := exists_sylow_component D
  have hQS : (Q : Subgroup L).map L.subtype ≤ (T : Subgroup G) ⊓ H := by
    rw [hQ]
    exact inf_le_inf_left _ hLH
  obtain ⟨hn,hfull⟩ := source_sylow_promotion D h hpsl H _ hST Q hQS inf_le_right hindex hunique
  exact ⟨H,hH,hLH,(fun hHM => hne (hH.eq_of_le (unique_sylow_join D h).1.1 hHM)),
    hST,hn,hfull,hunique⟩

/-- The chosen source crossing element and its literal uniqueness subgroup. -/
theorem exists_source_crossing_counterexample
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
    exists_source_sylow_counterexample D h hpsl hnot
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

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
