module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.NonsolvableSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation

/-!
# Noncommuting critical centers in the selected perfect-factor source pair

The actual Chapter 6 preparation constructs F.1.1 for the original pair
`![L,R]` and `S = O₂(N_G(L) ∩ H)`. Local-family membership makes L
nonsolvable, and the selected perfect R is nontrivial by its escape from
`N_G(L)`. Thus both original parabolics are nonsolvable. This discharges
the small-unitary exclusions before applying Chapter 7 to its reduced graph.

The result retains both distance branches, the two literal natural sections
with equal defining fields, and the Sylow products. The two Chapter 10 action
applications use those same original factors and quotient maps. No actor
recognition or order-144 exclusion is an additional premise on this branch.
The unrestricted F.1.1 theorem still requires the separate setup argument.

Source: Aschbacher--Smith 5.2.4--6, pp.649--651; DGS, *Groups and Graphs*
(1985), (7.1)--(7.5), pp.126--131 and the Chapter 10 action setup.
-/

public noncomputable section
open Subgroup
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Prepared
open Chapter6.Source.RankOneGeneric DGS85.Reduction NoncommutingProfile
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
local notation "F" => reducedFamily ![L,R] (Global.sourceS L H)
include d h hTH hp

/-- Chapter 7 with nonsolvability discharged by the actual selected factors. -/
theorem noncommuting_source_conclusion
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    EqualFieldNaturalCenters (graphLocalGroup F v) (Z F v) (Q F v)
      (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) :=
  Reduction.reduced_noncommuting_source_conclusion_of_nonsolvable_parabolics
    (d.hypothesisF11 h hTH) (d.parabolics_not_solvable h hp) hc hne

/-- Both b=1 natural-core actions on the original source parabolics. -/
theorem bOne_natural_cores
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 1) :
    IsElementaryAbelian 2 ((parabolic ![L,R] (Global.sourceS L H) 0).pCoreIn 2) ∧
    IsElementaryAbelian 2 ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) ∧
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BOneActionData F (base F false) (base F true) k₀ (Fin 2 → k₀))
        (c₁ : BOneActionData F (base F true) (base F false) k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F (base F false) ∧
        c₁.actor = graphLocalGroup F (base F true) ∧ Nat.card k₀ = Nat.card k₁ ∧
        OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ :=
  Reduction.original_bOne_natural_cores_of_nonsolvable_parabolics
    (d.hypothesisF11 h hTH) (d.parabolics_not_solvable h hp) hc hne hb

/-- Both b=2 actions and the opposite-neighbor consumers, with source
nonsolvability discharged and equal actual defining fields retained. -/
theorem bTwo_equal_field_profile_actions
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BTwoCenterActionData F v m w k₀ (Fin 2 → k₀))
        (c₁ : BTwoCenterActionData F w m v k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F v ∧ c₁.actor = graphLocalGroup F w ∧
        Nat.card k₀ = Nat.card k₁ ∧
        (∀ t, (graph F).Adj v t → t ≠ m →
          ∃ g : c₀.actor, (g : G₀ ![L,R] (Global.sourceS L H)) • m = t ∧
            c₀.quotient g ∉ normalizer (c₀.imageSylow : Set SL(2,k₀)) ∧
            Nonempty (BTwoActionData F w m v t k₀)) ∧
        (∀ t, (graph F).Adj w t → t ≠ m →
          ∃ g : c₁.actor, (g : G₀ ![L,R] (Global.sourceS L H)) • m = t ∧
            c₁.quotient g ∉ normalizer (c₁.imageSylow : Set SL(2,k₁)) ∧
            Nonempty (BTwoActionData F v m w t k₁)) :=
  Reduction.reduced_bTwo_equal_field_profile_actions_of_nonsolvable_parabolics
    (d.hypothesisF11 h hTH) (d.parabolics_not_solvable h hp) hc hne hb hvm hmw

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Prepared
