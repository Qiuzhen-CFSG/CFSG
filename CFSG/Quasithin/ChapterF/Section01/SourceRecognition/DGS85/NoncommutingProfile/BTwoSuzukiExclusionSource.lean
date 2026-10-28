module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSuzukiExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntersectionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSuzukiEnlargement

/-!
# Excluding the original Suzuki beta quotient

The original F1.11 beta quotient is transported by the literal starred
endpoint inclusion to the reduced graph quotient. The seed Frattini
obstruction then excludes this actual quotient. The second application
discharges beta centrality using the earlier center-action family; (6.5),
(7.1), and (7.4) remain explicit earlier-source inputs.

The endpoint is the original L_1, with its original 2-core denominator.
The all-parameter applications also exclude Sz(2), using its actual
enlargement map. These results do not assert that
the other rank-one rows have been classified.
Source: DGS, Groups and Graphs (1985), (10.7), pp.158--159, and the
original/reduced endpoint markings, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The original beta quotient cannot be a nonbinary Suzuki group. -/
theorem original_bTwo_not_suzuki_beta
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    {n : ℕ} (hn : 0 < n) (e : (L 1 ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup n) :
    False :=
  c.not_suzuki_beta (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot hn
    (reduced_graphSuzukiQuotient h true hn e)

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance exclusionAlgebra {F : Type*} [Field F] [CharP F 2] : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

/-- The earlier center family supplies the centrality needed to exclude
the nonbinary Suzuki quotient on the original beta endpoint. -/
theorem original_bTwo_not_suzuki_beta_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    {n : ℕ} (hn : 0 < n) (e : (L 1 ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup n) :
    False := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  exact original_bTwo_not_suzuki_beta h hb c hactor hcentral ht htne hcomm
    (hnot β c.middle.symm) hn e

/-- The original beta quotient cannot be any Suzuki group. -/
theorem original_bTwo_not_suzuki_beta_all
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    {n : ℕ} (e : (L 1 ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup n) :
    False :=
  c.not_suzuki_beta_all (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot
    (reduced_graphSuzukiQuotient_all h true n e)

/-- The earlier center family supplies the centrality needed to exclude
every Suzuki quotient on the original beta endpoint. -/
theorem original_bTwo_not_suzuki_beta_all_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    {n : ℕ} (e : (L 1 ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup n) :
    False := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  exact original_bTwo_not_suzuki_beta_all h hb c hactor hcentral ht htne hcomm
    (hnot β c.middle.symm) e

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
