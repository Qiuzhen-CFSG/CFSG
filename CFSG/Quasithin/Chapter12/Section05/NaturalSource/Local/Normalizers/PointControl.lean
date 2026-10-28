module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Generation
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Six
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Movement

/-!
# Point-residual control of the local normalizers

The literal generation identity L = L₁ ∨ Lᵢ reduces the two ambient normalizer
containments to the action of C_G(Vᵢ) on L₁. This gives both containments when
the point component equals L₁, and the six-space containment whenever L₁ is
normal in G₁. The equal-component branch also supplies the original module's
point-core containment. These are conditional source implications; the other
point-component alternatives still require their source arguments.

Source: Aschbacher--Smith, 12.5.4 and 12.5.8(1), printed pp.819--820.
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

omit [Finite G] in
private theorem residual_normal_of_components (c : LocalComponents s)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    ((s.marking.Li i).subgroupOf (s.marking.Gi i)).Normal := by
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have he : s.marking.Li i = c.K i := by
    cases c.alternative i hidx with
    | equal he => exact he
    | large he _ _ => rcases hi with hi | hi <;> omega
    | radical he _ _ => rcases hi with hi | hi <;> omega
  exact he.symm ▸ c.normal i hidx

/-- Controlling L₁ suffices to control L for either of the two local centralizers. -/
theorem local_centralizer_le_M_of_normalizes_point
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hni : ((s.marking.Li i).subgroupOf (s.marking.Gi i)).Normal)
    (hn1 : centralizer (s.marking.Vi i : Set G) ≤ normalizer (s.marking.Li 1 : Set G)) :
    centralizer (s.marking.Vi i : Set G) ≤ s.marking.M := by
  have hni' : s.marking.Gi i ≤ normalizer (s.marking.Li i : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (s.marking.Li_le_Gi i)).mp hni
  have hn : centralizer (s.marking.Vi i : Set G) ≤
      normalizer ((s.marking.Li 1 ⊔ s.marking.Li i : Subgroup G) : Set G) :=
    (le_inf hn1 ((Subgroup.centralizer_le_normalizer _).trans hni')).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rwa [s.point_residual_sup_local_eq h i hi] at hn

/-- Point-residual normality alone settles the six-space containment. -/
theorem G₆_le_M_of_point_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).Normal) :
    s.marking.Gi 6 ≤ s.marking.M := by
  apply (s.G₆_le_M_iff h).mpr
  apply s.local_centralizer_le_M_of_normalizes_point h 6 (Or.inr rfl)
    (s.local_six_component_source h).2
  exact (centralizer_le (s.marking.V₁_le_Vi 6 (Or.inr (Or.inr (Or.inr rfl))))).trans
    ((Subgroup.centralizer_le_normalizer _).trans
      ((normal_subgroupOf_iff_le_normalizer (s.marking.Li_le_Gi 1)).mp hn))

/-- The exact reduction of 12.5.4 to the action on the original point residual. -/
theorem local_normalizer_le_M_iff_centralizer_normalizes_point
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.marking.Gi i ≤ s.marking.M ↔
      centralizer (s.marking.Vi i : Set G) ≤ normalizer (s.marking.Li 1 : Set G) := by
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hc1 : centralizer (s.marking.Vi i : Set G) ≤ s.marking.Gi 1 :=
    (centralizer_le (s.marking.V₁_le_Vi i hidx)).trans (Subgroup.centralizer_le_normalizer _)
  constructor
  · intro hm
    have hn : centralizer (s.marking.Vi i : Set G) ≤ normalizer (L ⊓ s.marking.Gi 1 : Set G) :=
      (le_inf ((Subgroup.centralizer_le_normalizer _).trans hm)
        (hc1.trans (s.marking.Gi 1).le_normalizer)).trans inf_normalizer_le_normalizer_inf
    exact hn.trans (normalizer_le_normalizer_characteristic_image
      (L ⊓ s.marking.Gi 1) (solvableResidual (L ⊓ s.marking.Gi 1 : Subgroup G)))
  · intro hn
    have hc := s.local_centralizer_le_M_of_normalizes_point h i hi
      (s.residual_normal_of_components c i hi) hn
    rcases hi with rfl | rfl
    · exact s.marking.G₃_le_M_iff.mpr hc
    · exact (s.G₆_le_M_iff h).mpr hc

/-- The equal-point-component branch of both ambient normalizer containments. -/
theorem local_normalizers_le_M_of_point_component_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (he : c.K 1 = s.marking.Li 1) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M := by
  have hn1 : s.marking.Gi 1 ≤ normalizer (s.marking.Li 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (s.marking.Li_le_Gi 1)).mp
      (he ▸ c.normal 1 (Or.inl rfl))
  have step (i : ℕ) (hi : i = 3 ∨ i = 6) : s.marking.Gi i ≤ s.marking.M := by
    have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
    apply (s.local_normalizer_le_M_iff_centralizer_normalizes_point h c i hi).mpr
    exact (centralizer_le (s.marking.V₁_le_Vi i hidx)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hn1)
  exact ⟨step 3 (Or.inl rfl), step 6 (Or.inr rfl)⟩

/-- All local containment conclusions in the equal-point-component source branch. -/
theorem local_containments_of_point_component_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (he : c.K 1 = s.marking.Li 1) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M ∧
      V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  obtain ⟨h3, h6⟩ := s.local_normalizers_le_M_of_point_component_eq h c he
  exact ⟨h3, h6, s.seed_le_point_core_of_normal (he ▸ c.normal 1 (Or.inl rfl))⟩

/-- Failure of either normalizer containment forces a strict point component. -/
theorem point_component_ne_of_local_normalizer_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (he : ¬ s.marking.Gi 3 ≤ s.marking.M ∨ ¬ s.marking.Gi 6 ≤ s.marking.M) :
    c.K 1 ≠ s.marking.Li 1 := by
  intro hK
  obtain ⟨h3, h6⟩ := s.local_normalizers_le_M_of_point_component_eq h c hK
  exact he.elim (fun hn => hn h3) (fun hn => hn h6)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
