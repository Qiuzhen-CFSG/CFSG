module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.FlagRoot
public import Theory.Combinatorics.TranslationPlane.NativeFlagRoots

/-!
# Six compatible roots from the original source geometry

Each native elementary root is an elation at its coordinate flag. The
proved equality between source and full geometric flag groups places it
in the faithful action image of the same source quotient. Taking its unique
preimage constructs all six roots at once over the one original field.
Faithfulness pulls back all three elementary relations, including every
orientation of the mixed commutators. No relation or model-isomorphism
premise is assumed, and fields of orders two and four are retained.

The chosen projective frame has not yet been aligned with the original
base point. Full generation, positive subgroup identification, endpoint
placements and independent amalgam transport remain with this source family.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, printed pp.156,224;
Steinberg, Lectures on Chevalley Groups, Section 6.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace ProjectiveCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (d : SourceQuotient L S)
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  (hm : RootCoordinates.rotationOrder d = 3) (hcenter : centerIn c₁.actor = ⊥)

variable (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})

open Theory.SpecificGroups.LinearHigher
open scoped commutatorElement

/-- Every native root is realized in the same source quotient. -/
theorem exists_root_preimage (r : Root 3) (a : k₁) :
    ∃ g : (generated L S) ⧸ d.D,
      action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o g =
        specialLinearCollineation (matrixRoot r a) :=
  flagElations_le_action_range h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o _ _
    (TranslationPlane.FieldChart.coordinate_incident k₁ r.property)
    (TranslationPlane.FieldChart.matrixRoot_mem_flagElations k₁ r a)

/-- All six roots use the one field chart and its actual faithful projective action. -/
def compatibleRoot (r : Root 3) (a : k₁) : (generated L S) ⧸ d.D :=
  (exists_root_preimage h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o r a).choose

/-- The native action equation fixes the scaling of each root parameter. -/
theorem action_compatibleRoot (r : Root 3) (a : k₁) :
    action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (compatibleRoot h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o r a) =
        specialLinearCollineation (matrixRoot r a) :=
  (exists_root_preimage h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o r a).choose_spec

/-- All elementary relations hold for the constructed original-quotient roots.
The chain field includes all ordered triples, hence both signs and orientations. -/
theorem compatibleRoot_relations :
    Relations (compatibleRoot h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o) := by
  have native : Relations (fun (r : Root 3) (a : k₁) =>
      specialLinearCollineation (matrixRoot r a)) :=
    matrixRoot_relations.map specialLinearCollineation
  constructor
  · intro r a b
    apply action_injective h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
    rw [map_mul,action_compatibleRoot,action_compatibleRoot,action_compatibleRoot]
    exact native.add r a b
  · intro r s a b hrs hsr
    apply action_injective h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
    rw [map_commutatorElement,action_compatibleRoot,action_compatibleRoot,map_one]
    exact native.distant r s a b hrs hsr
  · intro i j k hij hjk hik a b
    apply action_injective h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
    rw [map_commutatorElement,action_compatibleRoot,action_compatibleRoot,action_compatibleRoot]
    exact native.chain i j k hij hjk hik a b

end ProjectiveCoordinates
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
