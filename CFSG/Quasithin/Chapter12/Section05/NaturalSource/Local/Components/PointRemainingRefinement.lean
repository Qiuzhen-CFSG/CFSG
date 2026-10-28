module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointCatalogue
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointOddTernary
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointSevenCover

/-!
# The marked remainder of the source point-component sieve

The original full catalogue now leaves only the signed ternary groups over
seven and the central A₇ cover. In each ternary row the image of the literal
L₁ in K₁/O₂(K₁) is SL₂(7). In the triple-cover row the literal Y lies in K₁,
and the original parabolic intersection has order 504 and index 15.
Every other row constructs LocalComponents with the original relative
normality. No model or additional ambient premise is introduced.

The remaining Sylow-action exclusions, general normalizer containments and
quasisimple strict-enlargement escape are still owned by qt-d-1251-local;
qt-d-1251-source retains final exterior assembly. This reduction does not
claim unconditional LocalComponents.
Source: Aschbacher--Smith 12.5.3, printed pp.817--818.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The remaining actual point quotients, with their proved marked local data. -/
@[expose] def RefinedRemainingPointAlternative (K : Subgroup G) : Prop :=
  (∃ unitary : Bool,
    (IsPSLSign (K ⧸ pCore 2 K) unitary 3 7 ∨ IsSLSign (K ⧸ pCore 2 K) unitary 3 7) ∧
      Nonempty ((((s.marking.Li 1).subgroupOf K).map
        (QuotientGroup.mk' (pCore 2 K))) ≃* SL(2,ZMod 7))) ∨
  (IsAlternatingCover (K ⧸ pCore 2 K) 7 ∧ s.Y ≤ K ∧
    Nat.card (s.pointComponentParabolic K) = 504 ∧ (s.pointComponentParabolic K).index = 15)

/-- Refine both remaining model families on the same original normal component. -/
theorem point_component_alternative_or_refined_remaining
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    LocalComponentAlternative s 1 K ∨ s.RefinedRemainingPointAlternative K := by
  rcases s.point_component_alternative_or_remaining h hK hLK hN with ha | hm
  · exact .inl ha
  rcases hm with ⟨p,hp,ho,unitary,hm⟩ | hm
  · obtain ⟨rfl,he⟩ := s.point_component_odd_ternary_residual_model hK hLK hp ho unitary hm
    exact .inr (.inl ⟨unitary,hm,he⟩)
  · exact .inr (.inr ⟨hm,s.Y_le_point_component_of_seven_cover h hK hN hm,
      s.pointComponentParabolic_card_index_of_seven_cover h hK hLK hN hm⟩)

/-- The source hypotheses construct all local components or one of the two
explicitly marked remaining point cases; no LocalComponents premise is used. -/
theorem local_components_or_refined_remaining_point
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    Nonempty (LocalComponents s) ∨ ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧ s.marking.Li 1 ≤ K ∧
      (K.subgroupOf (s.marking.Gi 1)).Normal ∧ s.RefinedRemainingPointAlternative K := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 1 (.inl rfl)
  rcases s.point_component_alternative_or_refined_remaining h hK hLK hN with ha | hm
  · exact .inl ⟨s.localComponentsOfPointAlternative h K hK hLK hN ha⟩
  · exact .inr ⟨K,hK,hLK,hN,hm⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
