module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourAmalgamGlue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourOriginalConsumer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.BorelExtensions

/-!
# Compatible marked source recognition in the field-four Hall--Janko branch

The native Borel automorphism calculation realizes every automorphism of the
384-order overlap by the explicit 768-order outer normalizer. Its simultaneous
action on the second parabolic removes the discrepancy between the independent
source endpoint maps. The resulting reduced amalgam isomorphism feeds the
original J₂/Aut(J₂) restoration in the reversed source orientation.

The path parameters and residual conclusions of DGS (10.9) remain separate
source obligations.

Source: DGS, *Groups and Graphs* (1985), (10.9), printed pp.162--163, and
(15.3), printed pp.229--231.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
open SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance markedFieldFourAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

local notation "JB" => Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B

/-- The independent field-four endpoint maps become one compatible reduced
J₂ amalgam isomorphism after the certified native Borel coverage calculation. -/
theorem original_bTwo_field_four_reduced_iso
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
    Nonempty (RankTwoAmalgam.Iso
      (OriginalExtension.reducedAmalgam L S).reverse
      GreenBook.HallJanko.j2Model.toMarking.amalgam) := by
  apply original_bTwo_field_four_reduced_iso_of_borel_extensions
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  intro d
  exact Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.borel_extends_of_outerB_coverage
    Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.card_p₂
    Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms.automorphism_coverage d

/-- The compatible reduced comparison restores the original J₂/Aut(J₂)
alternative, preserving the beta-first reversed source orientation. -/
theorem original_bTwo_field_four_original_j2_or_autJ2_iso
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
    Nonempty (RankTwoAmalgam.Iso
      (OriginalExtension.originalAmalgam L S).reverse
      GreenBook.HallJanko.j2Model.toMarking.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (OriginalExtension.originalAmalgam L S).reverse
        GreenBook.HallJanko.autJ2Model.toMarking.amalgam) := by
  exact original_bTwo_field_four_reversed_j2_or_autJ2_iso h
    (original_bTwo_field_four_reduced_iso h hb c hactor hcentral ht hne hcomm hnot e hD E hK)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
