module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedSaturation

/-!
# The saturated seed and its field parameter

The square-order calculation for the central seed is useful only after the
source saturation step has identified that seed with `Q alpha`.  This module
performs that consumer application on the actual reduced F1.11 configuration.
The remaining numerical premise is stated as the literal p.159 index identity;
it is not folded into the definition of the seed and is not replaced by a
classification assumption.

Source: DGS, *Groups and Graphs* (1985), (10.7)--(10.8), pp.158--161.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
open DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/- The saturated equality transports the already proved normality and square
order of the actual seed to the source subgroup `Q alpha`. -/
theorem original_bTwo_saturated_seed_card_square
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hsat : Q F₀ α ≤
      (⨆ x : Vertex F₀, ⨆ (_ : (graph F₀).Adj α x),
        V F₀ x 1 ⊓ Q F₀ α) ⊔ D F₀ β t) :
    ∃ hN : ((D F₀ β t).subgroupOf (Q F₀ α)).Normal,
      letI := hN
      Nat.card (Q F₀ α ⧸ (D F₀ β t).subgroupOf (Q F₀ α)) =
        (D F₀ β t).relIndex (V F₀ β 1 ⊓ Q F₀ α) ^ 2 := by
  have hseed := centralSeed_eq_Q_of_span (reduced_triple h)
    (reduced_kernel_sylow h) hb c ht htne hsat
  obtain ⟨hN,hcard⟩ := c.central_seed_card_square
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hb hactor hcentral ht htne hcomm
  rw [hseed] at hN hcard
  exact ⟨hN,hcard⟩

/- The exact second-field-parameter clause of the source is an index identity.
Once that clause is supplied by the local 10.8 calculation, the parameter is
identified without taking a square root in the ambient group. -/
theorem original_bTwo_saturated_seed_field_parameter
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hsat : Q F₀ α ≤
      (⨆ x : Vertex F₀, ⨆ (_ : (graph F₀).Adj α x),
        V F₀ x 1 ⊓ Q F₀ α) ⊔ D F₀ β t)
    (hindex : (D F₀ β t).relIndex (V F₀ β 1 ⊓ Q F₀ α) = Nat.card k) :
    ∃ hN : ((D F₀ β t).subgroupOf (Q F₀ α)).Normal,
      letI := hN
      Nat.card (Q F₀ α ⧸ (D F₀ β t).subgroupOf (Q F₀ α)) = Nat.card k ^ 2 := by
  obtain ⟨hN,hcard⟩ := original_bTwo_saturated_seed_card_square h hb c
    hactor hcentral ht htne hcomm hsat
  refine ⟨hN,?_⟩
  rw [hcard,hindex]

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
