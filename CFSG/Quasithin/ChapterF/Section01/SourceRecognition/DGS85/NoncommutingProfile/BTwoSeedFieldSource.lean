module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedField
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedSource

/-!
# The central seed field bound with original F1.11 markings

Transport the p.159 numerical estimate through the actual inclusion of
the reduced completion into the original group. The denominator is the
intersection of the original neighboring core and the transported opposite
core; the numerator is the transported radius-one group intersected with
the original starting core.

The center-family application discharges centrality using the proved
characteristic-two exclusion of 10.6, and retains normalization of both
seed layers by the full reduced endpoint and Borel. Only the earlier
6.5/7.1/7.4 inputs remain explicit. The estimate does not identify the
seed with Q_alpha or its factor order with the second field parameter.

Source: DGS, Groups and Graphs (1985), proof of 10.7, pp.158--159,
with the source-to-reduced markings of pp.95--96.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The field bound on the literal original radius/core section. Both
cores are transported through the original reduced-completion inclusion. -/
theorem original_bTwo_seed_field_bound
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    Nat.card k ≤
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype).relIndex
        ((V F₀ β 1).map (G₀ L S).subtype ⊓ (parabolic L S 0).pCoreIn 2) := by
  have hh := c.central_seed_field_bound (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm hnot
  have he := relIndex_map_map_of_injective (f := (G₀ L S).subtype)
    (D F₀ β t) (V F₀ β 1 ⊓ Q F₀ α) (G₀ L S).subtype_injective
  change ((Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype).relIndex
    ((V F₀ β 1 ⊓ Q F₀ α).map (G₀ L S).subtype) = _ at he
  rw [map_inf _ _ _ (G₀ L S).subtype_injective,map_inf _ _ _ (G₀ L S).subtype_injective,
    reduced_base_Q_map h true,reduced_base_Q_map h false] at he
  exact he.symm ▸ hh

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The actual earlier center-action family supplies centrality by the
characteristic-two 10.6 exclusion. The resulting field bound retains the
original endpoints, full reduced Borel and literal denominator of 10.7.
No seed saturation or parameter refinement is assumed. -/
theorem original_bTwo_seed_field_bound_of_center_family
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
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β) :
    let J₀ := (centralSeed F₀ α β t).map (G₀ L S).subtype
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    let A₀ := (V F₀ β 1).map (G₀ L S).subtype ⊓ (parabolic L S 0).pCoreIn 2
    Nat.card k ≤ D₀.relIndex A₀ ∧
      P₀ L S 0 ≤ normalizer (J₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (J₀ : Set G) ⊓ normalizer (D₀ : Set G) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  exact ⟨original_bTwo_seed_field_bound h hb c hactor hcentral ht htne hcomm (hnot β c.middle.symm),
    original_bTwo_seed_layers_normalized h hb c ht htne⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
