module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointSmallModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointAlternative

/-!
# The original local consumers from the actual point quotient

Each large point quotient now supplies Y ≤ K₁, and hence the complete
point alternative. The three-space exclusion then constructs all four
local components, with their original embeddings and relative normality.
This gives V ≤ O₂(G₁) directly from the large model, without a residual
containment or LocalComponents premise. The same construction feeds the
original point-control and generation-one conclusions. The radical row
also constructs all components from nonquasisimplicity alone. The complete
binary higher-linear branch supplies the same point-core conclusion after
the degree-four quotient is excluded using the actual parabolic intersection.

The quasisimple point-model sieve, remaining ambient normalizer containments
and quasisimple strict-enlargement escape remain with qt-d-1251-local.
Structural1222At comes from qt-d-1222-source; qt-d-1251-source retains
final assembly and discharge of all explicit source premises.
Source: Aschbacher--Smith, 12.5.3--4, 12.5.8 and12.5.11, pp.817--821.
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

/-- Construct all original local components from any of the three large point models. -/
@[expose] def localComponentsOfLargePointModel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (K : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) : LocalComponents s :=
  s.localComponentsOfPointAlternative h K hK hLK hN
    (s.local_point_component_large_alternative h hK hN hm)

/-- Construct all original local components from the nonquasisimple point branch. -/
@[expose] def localComponentsOfNonquasisimplePoint
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (K : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) : LocalComponents s :=
  s.localComponentsOfPointAlternative h K hK hLK hN
    (s.local_point_component_radical_alternative h hK hLK hn)

/-- The original point-core conclusion in all three large rows, including the source residual construction. -/
theorem seed_le_point_core_of_large_point_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  s.seed_le_point_core h (s.localComponentsOfLargePointModel h K hK hLK hN hm)

/-- The point-fusion consumer retains only the earlier structural input and the two normalizer containments. -/
theorem pointControl_of_large_point_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model))
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    PointControl s.marking :=
  s.pointControl_of_local_components h structural
    (s.localComponentsOfLargePointModel h K hK hLK hN hm) hG₃ hG₆

/-- The actual generation-one exclusion, with all local components and point-core containment constructed from the large model. -/
theorem generation_ne_one_of_large_point_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model))
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 :=
  s.generation_ne_one_of_local_components h structural
    (s.localComponentsOfLargePointModel h K hK hLK hN hm) hG₃ hG₆ hH

/-- The entire binary higher-linear point branch supplies the original point-core containment. -/
theorem seed_le_point_core_of_binary_linear_point_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  s.seed_le_point_core_of_point_alternative h hK hLK hN
    (s.local_point_component_alternative_of_binary_linear h hK hLK hN hn hm)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
