module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.SourceConclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.BOneProfileSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.MixedGraphApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitarySolvability

/-!
# Chapter 7 from nonsolvable source parabolics

The retained PSU₃(2) enlargement is needed only when a degree-one projective
unitary source quotient is still possible.  For selected perfect-factor applications the two
F.1.1 parabolics are nonsolvable.  The literal fixed-field-two projective and
special-unitary quotients are solvable, so this premise excludes both rows.
`MixedGraphApplication` then supplies the actual 6.5 obstruction and
`SmallUnitarySolvability` supplies the actor models.  This is a specialized
assembly route; it does not infer nonsolvability from bare `HypothesisF11`.

Source: DGS, *Groups and Graphs* (1985), 6.1, 6.5--6.6 and 7.1--7.5,
pp.118--131; the fixed-field-two solvability calculation is in
`LocalStructure.SmallUnitarySolvability`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G]

namespace Reduction
open DGS85.Reduction NoncommutingProfile
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L₀ S₀ i) (G₀ L₀ S₀))

/-- The complete Chapter 7 conclusion under the exact source nonsolvability
premise.  The literal original small-unitary rows are excluded by their solvability,
supplying both actor models and the reversed adjacent-core obstruction. -/
theorem reduced_noncommuting_source_conclusion_of_nonsolvable_parabolics
    (h : HypothesisF11 L₀ S₀)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L₀ S₀ i))
    {v w : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    EqualFieldNaturalCenters (graphLocalGroup F v) (Z F v) (Q F v)
      (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) := by
  have hsmall : ∀ i : Fin 2,
      ¬ ClassicalGroup.IsPSU (L₀ i ⧸ pCore 2 (L₀ i)) 3 2 ∧
      ¬ IsSU (L₀ i ⧸ pCore 2 (L₀ i)) 3 2 :=
    no_small_unitary_of_nonsolvable_parabolics h hns
  exact reduced_noncommuting_source_conclusion h
    (reduced_actor_models_of_nonsolvable_parabolics h hns)
    (fun x y hxy => reduced_graph_core_obstruction_of_no_small_unitary h hsmall
      y x hxy.symm) hc hne

/-- The original b=1 Chapter 10 natural-core consumer has the same exact
source premise and therefore no residual order-144 hypothesis. -/
theorem original_bOne_natural_cores_of_nonsolvable_parabolics
    (h : HypothesisF11 L₀ S₀)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L₀ S₀ i))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 1) :
    IsElementaryAbelian 2 ((parabolic L₀ S₀ 0).pCoreIn 2) ∧
    IsElementaryAbelian 2 ((parabolic L₀ S₀ 1).pCoreIn 2) ∧
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BOneActionData F (base F false) (base F true) k₀ (Fin 2 → k₀))
        (c₁ : BOneActionData F (base F true) (base F false) k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F (base F false) ∧
        c₁.actor = graphLocalGroup F (base F true) ∧ Nat.card k₀ = Nat.card k₁ ∧
        OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ := by
  exact original_bOne_natural_cores_of_actor_models h
    (reduced_actor_models_of_nonsolvable_parabolics h hns) hc hne hb

/-- Both orientations of the b=2 Chapter 10 action have equal defining fields.
Nonsolvability supplies the actual actor models used in their construction. -/
theorem reduced_bTwo_equal_field_profile_actions_of_nonsolvable_parabolics
    (h : HypothesisF11 L₀ S₀)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L₀ S₀ i))
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BTwoCenterActionData F v m w k₀ (Fin 2 → k₀))
        (c₁ : BTwoCenterActionData F w m v k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F v ∧ c₁.actor = graphLocalGroup F w ∧
        Nat.card k₀ = Nat.card k₁ ∧
        (∀ t, (graph F).Adj v t → t ≠ m →
          ∃ g : c₀.actor, (g : G₀ L₀ S₀) • m = t ∧
            c₀.quotient g ∉ normalizer (c₀.imageSylow : Set SL(2,k₀)) ∧
            Nonempty (BTwoActionData F w m v t k₀)) ∧
        (∀ t, (graph F).Adj w t → t ≠ m →
          ∃ g : c₁.actor, (g : G₀ L₀ S₀) • m = t ∧
            c₁.quotient g ∉ normalizer (c₁.imageSylow : Set SL(2,k₁)) ∧
            Nonempty (BTwoActionData F v m w t k₁)) :=
  reduced_bTwo_equal_field_profile_actions h
    (reduced_actor_models_of_nonsolvable_parabolics h hns) hc hne hb hvm hmw

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
