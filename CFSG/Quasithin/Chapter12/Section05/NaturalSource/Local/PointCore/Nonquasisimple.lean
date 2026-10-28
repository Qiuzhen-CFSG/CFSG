module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Seven
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Radical

/-!
# The nonquasisimple point component and the original seed

The actual source component classification now constructs its E₄₉-by-SL₂(7)
quotient, so the checked elementary-movement argument puts the original V
in O₂(G₁). This conclusion needs no LocalComponents record or assumed model.
Consequently failure of the point-core conclusion gives a relatively normal
containing component whose literal two-core quotient is quasisimple.

The remaining quasisimple point refinements, three-space radical exclusion,
normalizer containments and strict-enlargement escape remain with
qt-d-1251-local. Final exterior assembly belongs to qt-d-1251-source.
Source: Aschbacher--Smith, 12.5.3 and12.5.8(1), printed pp.817--820.
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

/-- The nonquasisimple point-core branch from the original source hypotheses. -/
theorem seed_le_point_core_of_nonquasisimple_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  s.seed_le_point_core_of_radical_model hLK hK.1 hN
    (s.local_component_nonquasisimple_model h 1 (.inl rfl) hK hLK hn)

/-- Failure of seed containment forces the actual point component to have
quasisimple two-core quotient, before constructing LocalComponents. -/
theorem point_component_quasisimple_of_seed_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  by_contra hn
  exact hfail (s.seed_le_point_core_of_nonquasisimple_component h hK hLK hN hn)

/-- Construct the literal normal containing component under point-core failure.
The still-needed quasisimple model sieve applies to this actual witness. -/
theorem exists_normal_quasisimple_point_component_of_seed_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      s.marking.Li 1 ≤ K ∧ (K.subgroupOf (s.marking.Gi 1)).Normal ∧
      IsQuasisimple (K ⧸ pCore 2 K) := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 1 (.inl rfl)
  exact ⟨K,hK,hLK,hN,s.point_component_quasisimple_of_seed_escape h hK hLK hN hfail⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
