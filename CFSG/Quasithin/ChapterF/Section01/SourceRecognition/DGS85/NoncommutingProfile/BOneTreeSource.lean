module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneRegularSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneCoverPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Action
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover

/-!
# The original b=1 markings on the universal completion tree

The literal inclusions of both reduced endpoints into G₀ define a faithful
completion of the original reduced amalgam. Their intersection is the whole
reduced Borel, so the universal map gives a coset covering. Applying the
short-path covering calculation transfers the four- or five-path conclusions
of (10.5) to the exact universal tree used in the Chapter 14 construction.

The endpoint and Borel equations retain the reduced-to-original inclusions.
The full original actor centers and the source graph's exact r,s parameters
are retained as well. Earlier marked action inputs remain with source
assembly; no ambient completion isomorphism is asserted.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.156--157, and the tree
reduction p.227; AS F.1.9 and F.3.3, pp.261--262 and 270.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem reduced_endpoint_le (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (reducedSylow L S) i ≤ G₀ L S := by
  rw [←P₀_eq_source h i]
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private def completionOfSubgroups (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H) :
    FaithfulCompletion (RankTwoAmalgam.ofSubgroups A D C hDA hDC) (G := H) where
  left := inclusion hA
  right := inclusion hC
  compatible := rfl
  left_injective := inclusion_injective _
  right_injective := inclusion_injective _
  middle_injective := fun _ _ hxy => Subtype.ext (congrArg (fun x : H => (x : G)) hxy)
  generated := by
    rw [inclusion_range,inclusion_range,←subgroupOf_sup hA hC,hgen]
    exact subgroupOf_self _

private theorem completionOfSubgroups_overlap (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H)
    (hinter : A ⊓ C = D) :
    (completionOfSubgroups A D C H hDA hDC hA hC hgen).left.range ⊓
      (completionOfSubgroups A D C H hDA hDC hA hC hgen).right.range =
      (completionOfSubgroups A D C H hDA hDC hA hC hgen).middle.range := by
  change (inclusion hA).range ⊓ (inclusion hC).range = (inclusion (hDA.trans hA)).range
  rw [inclusion_range,inclusion_range,inclusion_range]
  change (A ⊓ C).subgroupOf H = D.subgroupOf H
  rw [hinter]

private theorem completion_lift_left (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H)
    (x : A) :
    (Universal.lift (RankTwoAmalgam.ofSubgroups A D C hDA hDC)
      (completionOfSubgroups A D C H hDA hDC hA hC hgen)
      (Universal.left (RankTwoAmalgam.ofSubgroups A D C hDA hDC) x) : G) = (x : G) := by
  rw [Universal.lift_left]
  rfl

private theorem completion_lift_right (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H)
    (x : C) :
    (Universal.lift (RankTwoAmalgam.ofSubgroups A D C hDA hDC)
      (completionOfSubgroups A D C H hDA hDC hA hC hgen)
      (Universal.right (RankTwoAmalgam.ofSubgroups A D C hDA hDC) x) : G) = (x : G) := by
  rw [Universal.lift_right]
  rfl

private theorem completion_lift_middle (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H)
    (x : D) :
    (Universal.lift (RankTwoAmalgam.ofSubgroups A D C hDA hDC)
      (completionOfSubgroups A D C H hDA hDC hA hC hgen)
      (Universal.left (RankTwoAmalgam.ofSubgroups A D C hDA hDC)
        ((RankTwoAmalgam.ofSubgroups A D C hDA hDC).left x)) : G) = (x : G) :=
  completion_lift_left A D C H hDA hDC hA hC hgen
    ((RankTwoAmalgam.ofSubgroups A D C hDA hDC).left x)

private def reducedCompletion (h : HypothesisF11 L S) :
    FaithfulCompletion (reducedAmalgam L S) (G := G₀ L S) :=
  completionOfSubgroups _ _ _ _ (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (reduced_endpoint_le h 0) (reduced_endpoint_le h 1)
    (by rw [←P₀_eq_source h 0,←P₀_eq_source h 1]; rfl)

private theorem reducedCompletion_family (h : HypothesisF11 L S) :
    (reducedCompletion h).cosetFamily = reducedFamily L S := by
  funext i
  cases i with
  | false =>
    change (inclusion (reduced_endpoint_le h 0)).range =
      (P₀ L S 0).subgroupOf (G₀ L S)
    rw [inclusion_range,P₀_eq_source h 0]
  | true =>
    change (inclusion (reduced_endpoint_le h 1)).range =
      (P₀ L S 1).subgroupOf (G₀ L S)
    rw [inclusion_range,P₀_eq_source h 1]

private theorem reducedCompletion_overlap (h : HypothesisF11 L S) :
    (reducedCompletion h).left.range ⊓ (reducedCompletion h).right.range =
      (reducedCompletion h).middle.range := by
  exact completionOfSubgroups_overlap _ _ _ _
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (reduced_endpoint_le h 0) (reduced_endpoint_le h 1)
    (by rw [←P₀_eq_source h 0,←P₀_eq_source h 1]; rfl)
    (lemma_F_1_3_6 (reduced_hypothesis h))

/-- The actual quotient from the universal completion to the original reduced subgroup. -/
def bOne_tree_map (h : HypothesisF11 L S) : (reducedAmalgam L S).Universal →* G₀ L S :=
  Universal.lift (reducedAmalgam L S) (reducedCompletion h)

/-- The left endpoint map is the original reduced-to-original inclusion. -/
theorem bOne_tree_map_left (h : HypothesisF11 L S)
    (x : parabolic L (reducedSylow L S) 0) :
    (bOne_tree_map h (Universal.left (reducedAmalgam L S) x) : G) = (x : G) :=
  completion_lift_left _ _ _ _
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (reduced_endpoint_le h 0) (reduced_endpoint_le h 1)
    (by rw [←P₀_eq_source h 0,←P₀_eq_source h 1]; rfl) x

/-- The right endpoint map is the original reduced-to-original inclusion. -/
theorem bOne_tree_map_right (h : HypothesisF11 L S)
    (x : parabolic L (reducedSylow L S) 1) :
    (bOne_tree_map h (Universal.right (reducedAmalgam L S) x) : G) = (x : G) :=
  completion_lift_right _ _ _ _
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (reduced_endpoint_le h 0) (reduced_endpoint_le h 1)
    (by rw [←P₀_eq_source h 0,←P₀_eq_source h 1]; rfl) x

/-- The whole reduced Borel, including its odd part, retains its original inclusion. -/
theorem bOne_tree_map_middle (h : HypothesisF11 L S)
    (x : commonBorel L (reducedSylow L S)) :
    (bOne_tree_map h (Universal.left (reducedAmalgam L S) ((reducedAmalgam L S).left x)) : G) =
      (x : G) :=
  completion_lift_middle _ _ _ _
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (reduced_endpoint_le h 0) (reduced_endpoint_le h 1)
    (by rw [←P₀_eq_source h 0,←P₀_eq_source h 1]; rfl) x

/-- The endpoint and whole-Borel markings induce the literal coset covering. -/
theorem bOne_tree_cover (h : HypothesisF11 L S) :
    CoverData (Universal.cosetFamily (reducedAmalgam L S)) (reducedFamily L S) (bOne_tree_map h) := by
  rw [←reducedCompletion_family h]
  exact Universal.coverData_of_overlap (reducedAmalgam L S) (reducedCompletion h)
    (reducedCompletion_overlap h)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance bOneTreeAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The b=1 source alternatives on the exact universal tree used by Chapter 14.
The field and center markings remain those of the original F.1.11 pair. -/
theorem original_bOne_tree_path_alternatives
    (h : HypothesisF11 L S)
    (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)
    (hactor₀ : c₀.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    (centerIn (c₀.actor.map (G₀ L S).subtype) = ⊥ ∧
      centerIn (c₁.actor.map (G₀ L S).subtype) = ⊥ ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4 ∧
      BasedPathTransitive (X := (reducedAmalgam L S).Universal)
        (graph (Universal.cosetFamily (reducedAmalgam L S))) 4 ∧
      ∀ {a b} (p : (graph (Universal.cosetFamily (reducedAmalgam L S))).Walk a b),
        p.IsPath → p.length = 4 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) ∨
    (Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype)) = Nat.card k₀ ∧
      Nat.card (centerIn (c₁.actor.map (G₀ L S).subtype)) = Nat.card k₁ ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 ∧
      BasedPathTransitive (X := (reducedAmalgam L S).Universal)
        (graph (Universal.cosetFamily (reducedAmalgam L S))) 5 ∧
      ∀ {a b} (p : (graph (Universal.cosetFamily (reducedAmalgam L S))).Walk a b),
        p.IsPath → p.length = 5 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) := by
  have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set (G₀ L S)) := by
    rw [hactor₀]
    exact reduced_borel_normalizes_source_actor h 0
  have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set (G₀ L S)) := by
    rw [hactor₁]
    exact reduced_borel_normalizes_source_actor h 1
  rw [←reduced_actor_center_map,←reduced_actor_center_map,
    map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective,
    map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective,
    card_map_of_injective (G₀ L S).subtype_injective,
    card_map_of_injective (G₀ L S).subtype_injective]
  exact bOne_cover_path_alternatives (reduced_triple h) c₀ c₁ hn₀ hn₁ E₀ E₁ (bOne_tree_cover h)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
