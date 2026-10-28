module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoChapter10Consumer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoMarkedAlternatives

/-!
# Original field-four Hall--Janko consumer

The Chapter 10 field-four source identifies the reduced endpoints and the
whole reduced Borel independently.  The missing compatibility is therefore
represented here by a genuine `RankTwoAmalgam.Iso`, rather than by a second
`ParabolicEquiv`.  The source orientation has beta first, so the comparison is
the reverse of `OriginalExtension.reducedAmalgam`.

The first pair of theorems consumes an untwisted compatible reduced comparison
and applies the proved original-extension restoration.  The second pair also
accepts the standard twist output of Sylow alignment, provided the twist
factors through the concrete J₂ endpoint.  This leaves the native Borel
restriction calculation to its owner while exposing the exact premise needed
by the outer-restoration theorem.

Source: DGS, *Groups and Graphs* (1985), (10.9), pp.162--163, and
(15.3), pp.229--231.
-/

public noncomputable section
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open GreenBook SuzukiContainment
open Subgroup Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Noncommuting DGS85.Reduction
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

local notation "J₂" => HallJanko.j2Model.toMarking.amalgam

/-- The completed outer-restoration step in the field-four source orientation.
The input is the actual compatible reduced amalgam isomorphism; independent
endpoint equivalences do not satisfy this premise. -/
theorem original_bTwo_field_four_reversed_j2_or_autJ2_iso
    (h : HypothesisF11 L S)
    (e : Nonempty (RankTwoAmalgam.Iso (OriginalExtension.reducedAmalgam L S).reverse J₂)) :
    Nonempty (RankTwoAmalgam.Iso (OriginalExtension.originalAmalgam L S).reverse J₂) ∨
      Nonempty (RankTwoAmalgam.Iso (OriginalExtension.originalAmalgam L S).reverse
        HallJanko.autJ2Model.toMarking.amalgam) := by
  obtain ⟨e⟩ := e
  exact OriginalExtension.JankoTwo.SplitComparison.original_reversed_j2_or_autJ2_iso h e

/-- A compatible reduced J₂ comparison gives the original J₂/Aut(J₂)
parabolic alternative, with the source's reversed orientation retained. -/
theorem original_bTwo_field_four_reversed_j2_or_autJ2_models
    (h : HypothesisF11 L S)
    (e : Nonempty (RankTwoAmalgam.Iso (OriginalExtension.reducedAmalgam L S).reverse J₂)) :
    ExceptionalModels.IsModel .j2 (OriginalExtension.originalAmalgam L S).reverse ∨
      ExceptionalModels.IsModel .autJ2 (OriginalExtension.originalAmalgam L S).reverse := by
  obtain hJ | hA := original_bTwo_field_four_reversed_j2_or_autJ2_iso h e
  · obtain ⟨e⟩ := hJ
    exact Or.inl ⟨e.toParabolicEquiv⟩
  · obtain ⟨e⟩ := hA
    exact Or.inr ⟨e.toParabolicEquiv⟩

/-- A twisted reduced comparison can be untwisted when its overlap
automorphism factors through the concrete J₂ amalgam. -/
theorem original_bTwo_field_four_reversed_j2_or_autJ2_iso_of_twist
    (h : HypothesisF11 L S) (d : MulAut HallJanko.j2Model.toMarking.B)
    (e : Nonempty (RankTwoAmalgam.Iso (OriginalExtension.reducedAmalgam L S).reverse (RankTwoAmalgam.twistRight J₂ d)))
    (hfactor : RankTwoAmalgam.FactorsThrough J₂ d) :
    Nonempty (RankTwoAmalgam.Iso (OriginalExtension.originalAmalgam L S).reverse J₂) ∨
      Nonempty (RankTwoAmalgam.Iso (OriginalExtension.originalAmalgam L S).reverse
        HallJanko.autJ2Model.toMarking.amalgam) := by
  obtain ⟨e⟩ := e
  exact original_bTwo_field_four_reversed_j2_or_autJ2_iso h
    ⟨e.trans hfactor.iso⟩

/-- The same twisted interface directly supplies the original model
alternative. -/
theorem original_bTwo_field_four_reversed_j2_or_autJ2_models_of_twist
    (h : HypothesisF11 L S) (d : MulAut HallJanko.j2Model.toMarking.B)
    (e : Nonempty (RankTwoAmalgam.Iso (OriginalExtension.reducedAmalgam L S).reverse (RankTwoAmalgam.twistRight J₂ d)))
    (hfactor : RankTwoAmalgam.FactorsThrough J₂ d) :
    ExceptionalModels.IsModel .j2 (OriginalExtension.originalAmalgam L S).reverse ∨
      ExceptionalModels.IsModel .autJ2 (OriginalExtension.originalAmalgam L S).reverse := by
  obtain hJ | hA := original_bTwo_field_four_reversed_j2_or_autJ2_iso_of_twist
    h d e hfactor
  · obtain ⟨e⟩ := hJ
    exact Or.inl ⟨e.toParabolicEquiv⟩
  · obtain ⟨e⟩ := hA
    exact Or.inr ⟨e.toParabolicEquiv⟩

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourOriginalConsumerAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- The literal Chapter 10 center-family consumer: compatibility of the
reduced comparison discharges original J₂/Aut(J₂) recognition while retaining
the original endpoint orders, common extension index, full Borel and Sylow.
The independent source calculation of that compatibility remains explicit. -/
theorem original_bTwo_field_four_classification_of_center_family
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
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 4)
    (eJ : Nonempty (RankTwoAmalgam.Iso (OriginalExtension.reducedAmalgam L S).reverse J₂)) :
    (ExceptionalModels.IsModel .j2 (OriginalExtension.originalAmalgam L S).reverse ∨
      ExceptionalModels.IsModel .autJ2 (OriginalExtension.originalAmalgam L S).reverse) ∧
    Nat.card (pCore 2 (parabolic L S 0)) = 64 ∧
    Nat.card (pCore 2 (parabolic L S 1)) = 32 ∧
    ∃ n : ℕ, (n = 1 ∨ n = 2) ∧
      (B₀ L S).relIndex (commonBorel L S) = n ∧
      (∀ i : Fin 2, (P₀ L S i).relIndex (parabolic L S i) = n) ∧
      Nat.card (parabolic L S 0) = 1152 * n ∧
      Nat.card (parabolic L S 1) = 1920 * n ∧
      Nat.card (commonBorel L S) = 384 * n ∧ Nat.card S = 128 * n ∧
      Nat.card (parabolic L S 0 ⧸ pCore 2 (parabolic L S 0)) = 18 * n := by
  have hmodels := original_bTwo_field_four_reversed_j2_or_autJ2_models h eJ
  obtain ⟨eJ⟩ := eJ
  refine ⟨hmodels,
    OriginalExtension.JankoTwo.original_second_core_card h 0 eJ.right,
    OriginalExtension.JankoTwo.original_core_card h 1 eJ.left, ?_⟩
  exact original_bTwo_field_four_orders_of_center_family h hb c hactor E E₁
    hc hne hnot hcenters ht htne hcomm hD e hK

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
