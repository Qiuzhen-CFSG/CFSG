module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Radical
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Mathieu

/-!
# The remaining J₄ projection in the source normalizer argument

The source component construction and the completed equal, radical, linear
and Mathieu rows leave only an actual J₄ point component if either of the
two normalizer containments fails. The remaining actor is the literal
projection of Gᵢ ∩ G₁ along the component centralizer, with the full point-core
kernel retained. Its failure to normalize the original L₁ image is explicit.

This is a reduction of 12.5.4, not its completed J₄ argument. The remaining
projection exclusion and local assembly belong to qt-d-1251-local; earlier
structural discharge and final exterior assembly retain qt-d-1222-source
and qt-d-1251-source respectively. No generation-one exclusion is used.
Source: Aschbacher--Smith, 12.5.3--4, printed pp.818--819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- Every normalizer escape lies in the actual J₄ point-component row. -/
theorem point_component_janko_of_local_normalizer_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (he : ¬ s.marking.Gi i ≤ s.marking.M) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  have no (hh : s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M) : False := by
    rcases hi with rfl | rfl
    · exact he hh.1
    · exact he hh.2
  cases s.point_component_alternative_from_source h hK hLK hN with
  | equal hk =>
    apply False.elim
    apply he
    apply (s.local_intersection_normalizes_point_iff h i hi).mpr
    have hNG : s.marking.Gi 1 ≤ normalizer (s.marking.Li 1 : Set G) := by
      rw [hk]
      exact (normal_subgroupOf_iff_le_normalizer hK.1).mp hN
    exact inf_le_right.trans hNG
  | large _ hm _ =>
    rcases hm with hl | hm | hj
    · exact (no (s.local_normalizers_le_M_of_linear_point_component h hK hLK hN hl)).elim
    · exact (no (s.local_normalizers_le_M_of_mathieu_point_component h hK hLK hN hm)).elim
    · exact hj
  | radical _ _ hm =>
    exact (no (s.local_normalizers_le_M_of_radical_point_component h hK hLK hN
      (s.point_radical_alternative_not_quasisimple h hK hm))).elim

/-- The original source parameters construct the exact remaining J₄
projection obstruction, including relative normality and Y-containment. -/
theorem exists_janko_point_projection_of_local_normalizer_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (he : ¬ s.marking.Gi i ≤ s.marking.M) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      s.marking.Li 1 ≤ K ∧ (K.subgroupOf (s.marking.Gi 1)).Normal ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) ∧ s.Y ≤ K ∧
      ¬ s.localPointProjection K i ≤ normalizer (s.pointCoreImage (s.marking.Li 1) : Set _) := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 1 (.inl rfl)
  have hm := s.point_component_janko_of_local_normalizer_escape h hK hLK hN i hi he
  refine ⟨K,hK,hLK,hN,hm,s.Y_le_point_component_of_large_model h hK hN (.inr (.inr hm)),?_⟩
  intro hp
  exact he ((s.local_normalizer_iff_large_point_projection h hK hLK hN (.inr (.inr hm)) i hi).mpr hp)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
