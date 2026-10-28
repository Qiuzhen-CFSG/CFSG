module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointRankOne
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointAlternative

/-!
# Original local conclusions for the non-enlarging point models

The actual Bender quotients, odd-field PSL₂ quotients of degree one or two,
binary L₃(2), and even SU₃ covers all force K₁ = L₁. The point refinement
then constructs all four components and gives both ambient normalizer
containments together with V ≤ O₂(G₁). Thus the original point-control
and generation-one consumers need no additional local premises in these rows.

Structural1222At retains its earlier-source producer qt-d-1222-source.
The remaining point models, general normalizers and quasisimple escape
remain with qt-d-1251-local; final exterior assembly is qt-d-1251-source.
Source: Aschbacher--Smith 12.5.3--4, 12.5.8(1), and 12.5.11, pp.817--821.
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
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∨
      (∃ p e : ℕ, p.Prime ∧ Odd p ∧ (e = 1 ∨ e = 2) ∧
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ e)) ∨
      (∃ n : ℕ, 0 < n ∧ Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ n)))

include h hK hLK hN hm

/-- All four original components are constructed in these point-model branches. -/
@[expose] def localComponentsOfNonEnlargingPointModel : LocalComponents s :=
  s.localComponentsOfPointAlternative h K hK hLK hN
    (.equal (s.point_component_eq_of_non_enlarging_model hK hLK hm))

/-- Both ambient normalizer containments and the original point-core conclusion. -/
theorem local_containments_of_non_enlarging_point_model :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M ∧
      V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  have he := s.point_component_eq_of_non_enlarging_model hK hLK hm
  exact s.local_containments_of_point_residual_component h (he.symm ▸ hK) (he.symm ▸ hN)

/-- The literal point-control consumer has all local containment premises discharged. -/
theorem pointControl_of_non_enlarging_point_model
    (structural : Structural1222At KnownSimple.IsKnownSimple T) : PointControl s.marking := by
  obtain ⟨h3,h6,_⟩ := s.local_containments_of_non_enlarging_point_model h hK hLK hN hm
  exact s.pointControl_of_point_alternative h structural hK hLK hN
    (.equal (s.point_component_eq_of_non_enlarging_model hK hLK hm)) h3 h6

/-- The original generation-one exclusion, without separate normalizer or point-core inputs. -/
theorem generation_ne_one_of_non_enlarging_point_model
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 := by
  obtain ⟨h3,h6,_⟩ := s.local_containments_of_non_enlarging_point_model h hK hLK hN hm
  exact s.generation_ne_one_of_point_alternative h structural hK hLK hN
    (.equal (s.point_component_eq_of_non_enlarging_model hK hLK hm)) h3 h6 hH

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
