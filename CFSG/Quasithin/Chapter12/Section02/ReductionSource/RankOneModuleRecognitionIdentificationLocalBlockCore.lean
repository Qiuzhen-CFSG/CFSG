module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalBlockCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalBlockAction

/-!
# Chapter 12 consumers of the original block layer

The contrary order-four branch gives commutator generation of L by the
original closure U, identifies [O₂(LT),L] with the chosen-module layer,
and makes O₂(LT) elementary abelian. These are the block algebra steps in
source 6.2.11, printed p.686; the ambient A₇ contradiction remains open.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The source block calculation on the original whole reduced layer. -/
theorem source_local_four_intersection_block_core
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    L = ⁅L, sourceClosure (T : Subgroup G) L (wholeReduced T L) z⁆ ∧
      ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, L⁆ = commutatorLayer T L ∧
      IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  have hp := (source_local_layer_normalizers D h h611 hnatural).1
  exact ⟨LocalQuotientAction.four_component_commutator_closure h611 hnatural hz ho hT hp hcard,
    LocalQuotientAction.four_local_core_commutator_component h611 hnatural hz ho hT hp hcard,
    LocalQuotientAction.four_local_core_elementary h611 hnatural hz ho hT hp hcard⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
