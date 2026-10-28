module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceRootTransitivityLowerBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourPathBoundSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Reduced

/-!
# Field-four source minimum from transported rooted transitivity

The native J₂ path calculation and the compatible marked amalgam transport
are independent prerequisites.  This module supplies their direct consumer:
once rooted five-path transitivity has reached the reduced source graph, the
source minimum is at least five; the field-four order calculation gives the
opposite inequality.

The transport theorem is intentionally a premise here.  This keeps the
source-order consumer independent of the concrete native certificate and
allows either the direct J₂ path action or a later equivalent certificate to
feed it.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

local instance fieldFourPathParametersAlgebra {k₀ : Type*} [Field k₀]
    [CharP k₀ 2] : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-! A reduced rooted-transitivity premise is the exact interface between the
native path owner and the source-order consumer. -/

theorem sourceS_ge_five_of_reduced_path_transitive
    (h : HypothesisF11 L S)
    (ht : ∀ i, RootPathTransitive (graph F₀) (G₀ L S)
      (base F₀ i) 5) :
    5 ≤ DGS85.sourceS
      (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) := by
  exact DGS85.sourceS_ge_of_root_transitive
    (DGS85.Reduction.reduced_triple h)
    (DGS85.Reduction.reduced_vertex_sylow h) ht

/-! The field-four order bound and transported rooted transitivity force the
literal source minimum to be exactly five.  All endpoint/model hypotheses
needed to establish the order bound remain explicit. -/

theorem original_bTwo_field_four_sourceS_eq_five_of_reduced_path_transitive
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (htadj : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4)
    (ht : ∀ i, RootPathTransitive (graph F₀) (G₀ L S)
      (base F₀ i) 5) :
    DGS85.sourceS
      (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5 := by
  apply Nat.le_antisymm
  · exact original_bTwo_field_four_sourceS_le_five
      h hb c hactor hcentral htadj hne hcomm hnot e hD E hK
  · exact sourceS_ge_five_of_reduced_path_transitive h ht

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
