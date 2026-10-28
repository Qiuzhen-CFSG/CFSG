module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointTernaryExclusion
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Alignment
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.RadicalEscape
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.PointControl

/-!
# Source component construction in the normalizer and enlargement arguments

The full point catalogue now constructs all four local components. The
three-space residual is consequently a normal C-component in its original
normalizer, and both pending normalizer containments reduce to control of
the original point residual without assuming LocalComponents. The genuine
generation-one exclusion removes the radical point row, leaving precisely
the three large quasisimple models for the strict-enlargement argument.

The general normalizer control and the large-model escaping parabolics
remain with qt-d-1251-local. The earlier structural and generation inputs
retain their existing owners; qt-d-1251-source owns final exterior assembly.
Source: Aschbacher--Smith, 12.5.3--4 and 12.5.11(2), pp.817--821.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The source three-space component and its relative normality, with the
point refinement constructed from the original hypotheses. -/
theorem local_three_component_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    s.marking.Li 3 ∈ Chapter1.cComponentsIn (s.marking.Gi 3) ∧
      ((s.marking.Li 3).subgroupOf (s.marking.Gi 3)).Normal := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 1 (.inl rfl)
  exact s.local_three_component_source_of_point_alternative h hK hLK hN
    (s.point_component_alternative_from_source h hK hLK hN)

/-- The actual two normalizer consumers no longer require LocalComponents. -/
theorem local_normalizer_le_M_iff_point_control_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.marking.Gi i ≤ s.marking.M ↔
      centralizer (s.marking.Vi i : Set G) ≤ normalizer (s.marking.Li 1 : Set G) := by
  obtain ⟨c⟩ := s.local_components_from_source h
  exact s.local_normalizer_le_M_iff_centralizer_normalizes_point h c i hi

/-- Under the genuine generation-one exclusion, strict point enlargement
has one of exactly the three large source models and contains the original Y. -/
theorem strict_point_component_large_of_generation_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K)
    (hex : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      ChapterE.generationParameter H ≠ 1) :
    (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) ∧ s.Y ≤ K := by
  cases s.point_component_alternative_from_source h hK hLK hN with
  | equal he => exact (hne he).elim
  | large _ hm hY => exact ⟨hm,hY⟩
  | radical _ _ hm =>
    exact (hne (s.point_component_eq_of_nonquasisimple_of_generation_exclusion h hK hLK hN
      (s.point_radical_alternative_not_quasisimple h hK hm) hex)).elim

end SylowExteriorMarking

/-- Source 12.5.3 with the Sylow coordinates constructed on the original V.
Only the earlier universal 12.2.2 structural theorem remains explicit. -/
theorem exists_sylow_marking_with_local_components
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (a : ExteriorMarking D) :
    ∃ s : SylowExteriorMarking D, Nonempty (LocalComponents s) := by
  obtain ⟨s⟩ := sylowExteriorMarking_source h structural a
  exact ⟨s,s.local_components_from_source h⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
