module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourMarkedSource

/-!
# Marked original field-four center-family consumer

The certified native Borel coverage aligns the independent field-four
endpoint maps, producing the reduced J₂ amalgam isomorphism required by the
original-extension restoration.  This adapter removes that compatibility
premise from the center-family classification while retaining the literal
core orders, extension indices, and quotient order supplied by the Chapter 10
consumer.

The path and residual conclusions remain separate source obligations.

Source: DGS, *Groups and Graphs* (1985), (10.9), pp.162--163, and
(15.3), pp.229--231.
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
variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourMarkedConsumerAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- The native Borel-compatible field-four source yields original reversed
J₂/Aut(J₂) recognition and all literal Chapter 10 order conclusions. -/
theorem original_bTwo_field_four_marked_classification_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer
        ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 4) :
    (GreenBook.ExceptionalModels.IsModel .j2
        (OriginalExtension.originalAmalgam L S).reverse ∨
      GreenBook.ExceptionalModels.IsModel .autJ2
        (OriginalExtension.originalAmalgam L S).reverse) ∧
    Nat.card (pCore 2 (parabolic L S 0)) = 64 ∧
    Nat.card (pCore 2 (parabolic L S 1)) = 32 ∧
    ∃ n : ℕ, (n = 1 ∨ n = 2) ∧
      (B₀ L S).relIndex (commonBorel L S) = n ∧
      (∀ i : Fin 2, (P₀ L S i).relIndex (parabolic L S i) = n) ∧
      Nat.card (parabolic L S 0) = 1152 * n ∧
      Nat.card (parabolic L S 1) = 1920 * n ∧
      Nat.card (commonBorel L S) = 384 * n ∧ Nat.card S = 128 * n ∧
      Nat.card (parabolic L S 0 ⧸ pCore 2 (parabolic L S 0)) = 18 * n := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have eJ := original_bTwo_field_four_reduced_iso h hb c hactor hcentral
    ht htne hcomm (hnot β c.middle.symm) e hD E hK
  exact original_bTwo_field_four_classification_of_center_family h hb c hactor E E₁
    hc hne hnot hcenters ht htne hcomm hD e hK eJ

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
