module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourAlphaCoreSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameterOrderBound

/-!
# The field-four upper bound for the first nonregular source path

The original field-four endpoint calculations give reduced endpoint orders
1152 and 1920, with Borel order 384. Their indices are three and five, so
the six-path orbit–stabilizer obstruction proves s ≤ 5 in the literal
reduced source graph. All original endpoint and two-core hypotheses are
retained. The remaining path extrema are separate source obligations.

Source: Delgado–Goldschmidt–Stellmacher, Groups and Graphs (1985),
(10.9), pp.162–163.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open scoped MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourPathAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The literal reduced field-four source has first nonregular length at most five. -/
theorem original_bTwo_field_four_sourceS_le_five
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    DGS85.sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) ≤ 5 := by
  obtain ⟨hthree,hα,_⟩ := original_bTwo_field_four_reduced_alpha_orders
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨_,_,hβ,hB⟩ := original_bTwo_field_four_reduced_beta_equals_enlargement
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hfive : (B₀ L S).relIndex (P₀ L S 1) = 5 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (B₀ L S) (P₀ L S 1)
      bot_le le_sup_right
    rw [relIndex_bot_left,relIndex_bot_left,hβ,hB] at hh
    omega
  have hi (i : Bool) : ((F₀ (!i)).subgroupOf (F₀ i)).index = (if i then 5 else 3) := by
    have he : ((F₀ (!i)).subgroupOf (F₀ i)).index =
        (B₀ L S).relIndex (P₀ L S (if i then 1 else 0)) := by
      change (F₀ (!i)).relIndex (F₀ i) = _
      rw [←inf_relIndex_left]
      have hI : F₀ (!i) ⊓ F₀ i = (B₀ L S).subgroupOf (G₀ L S) := by
        cases i
        · exact (inf_comm _ _).trans (reduced_triple h).intersection
        · exact (reduced_triple h).intersection
      have hI' : F₀ i ⊓ F₀ (!i) = (B₀ L S).subgroupOf (G₀ L S) := by
        rw [inf_comm]
        exact hI
      rw [hI']
      cases i
      · exact relIndex_subgroupOf (show P₀ L S 0 ≤ G₀ L S from le_sup_left)
      · exact relIndex_subgroupOf (show P₀ L S 1 ≤ G₀ L S from le_sup_right)
    rw [he]
    cases i
    · exact hthree
    · exact hfive
  apply sourceS_le_five_of_three_five_orders (reduced_triple h) (reduced_vertex_sylow h)
    (hi false) (hi true)
  exact (Nat.card_congr (subgroupOfEquivOfLe (show P₀ L S 0 ≤ G₀ L S from le_sup_left)).toEquiv).trans hα

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
