module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedAction
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Original marked applications of the central residual and seed module

The residual centralizer is transported through the reduced-to-original
inclusion, retaining the literal neighboring cores and both conjugated
center groups. Its direct factors give the original D order and the exact
residual test separating the two later Chapter 10 branches.

For the original F1.11 seed, the proved characteristic-two exclusion
discharges centrality. The actual quotient has conjugation coordinates,
a quadratic V_beta action, two direct factors and a square-order formula.
Its image is normalized by the original enlarged endpoint. Earlier 6.5
and Chapter 7 inputs remain explicit for their existing source producers;
seed saturation, 10.8 and the 10.9--10.10 alternatives are not asserted.
Source: DGS, Groups and Graphs (1985), 10.4 and opening of 10.7, pp.153--159.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The source residual after inclusion in the original completion. Its
centralizer is taken inside the literal intersection of the two original
cores; its two generating centers use the same chosen conjugator. -/
theorem original_bTwo_residual_structure (h : HypothesisF11 L S)
    (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β) :
    ∃ g : c.actor, (g : G₀ L S) • β = t ∧
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
      let Z₀ := (Z F₀ α).map (G₀ L S).subtype
      let W₀ := (Z F₀ u).map (G₀ L S).subtype ⊔
        (Z F₀ ((g : G₀ L S) • u)).map (G₀ L S).subtype
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      R₀ = (centralResidual F₀ β t u ((g : G₀ L S) • u)).map (G₀ L S).subtype ∧
      D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧ IsElementaryAbelian 2 R₀ ∧
      Nat.card D₀ = Nat.card k ^ 2 * Nat.card R₀ ∧ (D₀ = Z₀ ↔ R₀ = ⊥) := by
  obtain ⟨g,hg,hr,hdec,hdis,hR,⟨e,_⟩,hcrit⟩ := c.central_residual_structure
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hb hactor hcentral ht hne
  let ι := (G₀ L S).subtype
  let R := bTwoResidual F₀ β t u ((g : G₀ L S) • u)
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map ι
  let Z₀ := (Z F₀ α).map ι
  let W₀ := (Z F₀ u).map ι ⊔ (Z F₀ ((g : G₀ L S) • u)).map ι
  let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
  change R = centralResidual F₀ β t u ((g : G₀ L S) • u) at hr
  change D F₀ β t = Z F₀ α ⊔ R at hdec
  change IsElementaryAbelian 2 R at hR
  have hDm : (D F₀ β t).map ι = D₀ := by
    change ((Q F₀ β ⊓ Q F₀ t).map ι) = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hRm : R.map ι = R₀ := by
    change ((D F₀ β t ⊓ centralizer ((Z F₀ u ⊔ Z F₀ ((g : G₀ L S) • u) :
      Subgroup (G₀ L S)) : Set (G₀ L S))).map ι) = _
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,
      hDm,Subgroup.map_sup]
  have hDmcard : Nat.card D₀ = Nat.card (D F₀ β t) := by
    rw [←hDm,card_map_of_injective (G₀ L S).subtype_injective]
  have hRmcard : Nat.card R₀ = Nat.card R := by
    rw [←hRm,card_map_of_injective (G₀ L S).subtype_injective]
  have hz := c.central_center_card E (c.omega_eq_bot_of_central_neighbor
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hactor hcentral)
  change Z F₀ α × R ≃* D F₀ β t at e
  change Nat.card (Z F₀ α) = Nat.card k ^ 2 at hz
  have hcard : Nat.card (D F₀ β t) = Nat.card k ^ 2 * Nat.card R := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hz]
  refine ⟨g,hg,?_,?_,?_,?_,?_,?_⟩
  · change R₀ = _
    rw [←hRm]
    exact congrArg (map ι) hr
  · have hh := congrArg (map ι) hdec
    rwa [hDm,Subgroup.map_sup,hRm] at hh
  · change Disjoint Z₀ R₀
    rw [←hRm]
    exact Subgroup.disjoint_map (G₀ L S).subtype_injective hdis
  · change IsElementaryAbelian 2 R₀
    rw [←hRm]
    let := hR
    exact IsElementaryAbelian.map _
  · exact hDmcard.trans (hcard.trans (congrArg (Nat.card k ^ 2 * ·) hRmcard.symm))
  · change D₀ = Z₀ ↔ R₀ = ⊥
    rw [←hDm,←hRm]
    rw [(Subgroup.map_injective (G₀ L S).subtype_injective).eq_iff,
      map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective]
    exact hcrit

/-- Original marked source application of the seed representation and its
two direct factors. Centrality is discharged by the proved 10.6 exclusion.
The earlier 6.5 obstruction and Chapter 7 action family remain explicit. -/
theorem original_bTwo_seed_module_of_center_family
    {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
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
    ∃ hN : ((D F₀ β t).subgroupOf (centralSeed F₀ α β t)).Normal,
      letI := hN
      ∃ hE : IsElementaryAbelian 2 (centralSeed F₀ α β t ⧸
        (D F₀ β t).subgroupOf (centralSeed F₀ α β t)),
      letI := hE
      let J := centralSeed F₀ α β t
      let q := QuotientGroup.mk' ((D F₀ β t).subgroupOf J)
      let A := ((V F₀ β 1 ⊓ Q F₀ α).subgroupOf J).map q
      let C := ((V F₀ t 1 ⊓ Q F₀ α).subgroupOf J).map q
      (∃ ρ : Representation (ZMod 2) c.actor (Additive (J ⧸ (D F₀ β t).subgroupOf J)),
        Nonempty (Representation.BinaryConjugationSection c.actor J (D F₀ β t) ρ) ∧
        Representation.BinaryOffender.IsQuadratic ρ ((V F₀ β 1).subgroupOf c.actor)) ∧
      Disjoint A C ∧
      (∃ e : A × C ≃* (J ⧸ (D F₀ β t).subgroupOf J),
        ∀ a c, e (a,c) = (a : J ⧸ (D F₀ β t).subgroupOf J) * c) ∧
      Nat.card (J ⧸ (D F₀ β t).subgroupOf J) =
        (D F₀ β t).relIndex (V F₀ β 1 ⊓ Q F₀ α) ^ 2 ∧
      enlargedEndpoint L S 0 ≤ normalizer (J.map (G₀ L S).subtype : Set G) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  obtain ⟨hN,hE,ρ,⟨s⟩,hq⟩ := c.central_seed_representation (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm
  refine ⟨hN,hE,⟨ρ,⟨s⟩,hq⟩,?_⟩
  let := hN
  let := hE
  obtain ⟨hd,he⟩ := bTwo_seed_quotient_factors (reduced_triple h) (reduced_kernel_sylow h) hb α β t
  obtain ⟨_,hcard⟩ := c.central_seed_card_square (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm
  refine ⟨hd,he,hcard,?_⟩
  have hAm : c.actor.map (G₀ L S).subtype = enlargedEndpoint L S 0 := by
    rw [hactor,reduced_graphLocalGroup_image h false]
    rfl
  rw [←hAm]
  exact (map_mono s.normalized).trans (le_normalizer_map (G₀ L S).subtype)

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
