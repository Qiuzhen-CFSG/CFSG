module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoUnitaryExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntersectionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnitaryApplication

/-!
# Excluding the original nonbinary unitary beta quotients

The genuine endpoint enlargement maps transport each original projective
or full special-unitary quotient to the reduced graph actor. The Sylow
Frattini obstruction excludes either model for fixed-field degree at least
two. The second application derives beta centrality from the earlier center
family. The special case keeps the full scalar cover and original core.

Degree-one original unitary rows need a separate enlargement argument;
the graph exclusion itself covers them whenever the actual graph quotient
has a unitary marking. No nonsolvability assumption is added here.
Source: DGS, Groups and Graphs (1985), (10.7), pp.158--159, with the
original/reduced endpoint markings and genuine Chapter 6 enlargement.
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

/-- Neither genuine unitary row of degree at least two can occur at the original beta endpoint. -/
theorem original_bTwo_not_unitary_beta
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 (2^n) ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 (2^n)) :
    False := by
  rcases hm with hm | hm
  · obtain ⟨K,hK,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    exact c.not_projective_unitary_beta (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot J (by omega) hcard hconj
      (reduced_graphProjectiveUnitaryQuotient h true J hn hcard hconj e)
  · obtain ⟨K,hK,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    exact c.not_special_unitary_beta (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot J (by omega) hcard hconj
      (reduced_graphSpecialUnitaryQuotient h true J hn hcard hconj e)

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance unitaryExclusionAlgebra {F : Type*} [Field F] [CharP F 2] : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

/-- The earlier center family supplies the centrality needed to exclude
either nonbinary unitary quotient on the original beta endpoint. -/
theorem original_bTwo_not_unitary_beta_of_center_family
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
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 (2^n) ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 (2^n)) :
    False := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  exact original_bTwo_not_unitary_beta h hb c hactor hcentral ht htne hcomm
    (hnot β c.middle.symm) hn hm

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
