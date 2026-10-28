module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCenterAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoShiftedSource

/-!
# The characteristic-two noncentral exclusion from earlier center actions

The two earlier marked natural center actions construct both opposite
D geometries. The paired Frattini calculation proves D_alpha=Z_alpha
and D_beta=Z_beta. Opposite lifts give the literal Q/Z actors, and the
natural center dimensions compute the required line indices. The
previously proved quotient-action and involution-lifting argument now
excludes characteristic two.

For the original F1.11 application, 10.3 constructs the shifted critical
pair. Its Chapter 7 center action is an explicit earlier-source input,
along with the setup's 6.5 obstruction. Every Chapter 10 D identity,
fixed-preimage, core-quadraticity, core index and field comparison used
by the contradiction is proved. The final theorem supplies the central
branch needed by 10.7--10.10.

These statements are conditional on genuine earlier source center
actions; final source assembly must discharge them with the Chapter 7
and setup producers. They do not yet prove 10.9 or 10.10.
Source: DGS, *Groups and Graphs* (1985), 10.3--10.6, pp.154--158.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]

local instance {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- Both D identities follow from the earlier marked natural center
actions. All covers, intersections, opposite lifts and Frattini steps
are discharged here; no D geometry is assumed. -/
theorem bTwo_D_eq_centers_of_center_actions (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {t v m w : Vertex (family P)}
    (c₀ : BTwoCenterActionData (family P) v m w k₀ W₀)
    (c₁ : BTwoCenterActionData (family P) m v t k₁ W₁)
    (hnt : t ≠ m) (hnw : w ≠ v) :
    D (family P) m t = Z (family P) v ∧
      D (family P) v w = Z (family P) m := by
  obtain ⟨g₀,hm₀,ho₀⟩ := c₀.exists_opposite_lift h c₁.terminal hnt
  obtain ⟨g₁,hm₁,ho₁⟩ := c₁.exists_opposite_lift h c₀.terminal hnw
  obtain ⟨d₀⟩ := c₀.exists_dGeometry h hS hb g₀ hm₀ ho₀
    (c₁.own_critical_product h) c₁.critical_product
  obtain ⟨d₁⟩ := c₁.exists_dGeometry h hS hb g₁ hm₁ ho₁
    (c₀.own_critical_product h) c₀.critical_product
  exact bTwo_paired_D_eq_centers h hS hb d₀ d₁

/-- Characteristic-two exclusion in 10.6, using only the two earlier
marked center actions and their natural dimensions. The actual Q/Z
actions and all Chapter 10 subgroup calculations are constructed. -/
theorem bTwo_paired_center_actions_impossible (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {t v m w : Vertex (family P)}
    (c₀ : BTwoCenterActionData (family P) v m w k₀ W₀)
    (c₁ : BTwoCenterActionData (family P) m v t k₁ W₁)
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc₀ : IsCriticalPair (family P) v w) (hc₁ : IsCriticalPair (family P) m t)
    (hne₀ : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hne₁ : ⁅Z (family P) m,Z (family P) t⁆ ≠ ⊥) : False := by
  have hnt : t ≠ m := by
    intro he
    have hd := hc₁.1
    rw [he,SimpleGraph.dist_self,hb] at hd
    omega
  have hnw : w ≠ v := by
    intro he
    have hd := hc₀.1
    rw [he,SimpleGraph.dist_self,hb] at hd
    omega
  obtain ⟨hD₀,hD₁⟩ := bTwo_D_eq_centers_of_center_actions h hS hb c₀ c₁ hnt hnw
  obtain ⟨g₀,hm₀,_⟩ := c₀.exists_opposite_lift h c₁.terminal hnt
  obtain ⟨g₁,hm₁,_⟩ := c₁.exists_opposite_lift h c₀.terminal hnw
  let a₀ := c₀.coreActionData g₀ hm₀
  let a₁ := c₁.coreActionData g₁ hm₁
  let d₀ := a₀.localGeometry h hS hb c₀.terminal.symm c₁.middle c₁.terminal.symm
    hc₁ hD₀ (c₁.own_critical_product h) c₁.critical_product
  let d₁ := a₁.localGeometry h hS hb c₁.terminal.symm c₀.middle c₀.terminal.symm
    hc₀ hD₁ (c₀.own_critical_product h) c₀.critical_product
  exact bTwo_paired_local_geometry_impossible_of_line_indices h hS hb
    c₁.terminal.symm c₀.middle c₀.terminal.symm hc₁ hc₀ hne₁ hne₀ d₀ d₁
    (c₀.line_index E₀) (c₁.line_index E₁)

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- The literal two D intersections after inclusion in the original
completion. The source center actions, not D equalities, are inputs. -/
theorem original_bTwo_D_eq_centers_of_center_actions (h : HypothesisF11 L S)
    (hb : b F = 2) {t u : Vertex F}
    (c₀ : BTwoCenterActionData F α β u k₀ W₀)
    (c₁ : BTwoCenterActionData F β α t k₁ W₁)
    (hnt : t ≠ β) (hnu : u ≠ α) :
    (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype =
        (Z F α).map (G₀ L S).subtype ∧
      (parabolic L S 0).pCoreIn 2 ⊓ (Q F u).map (G₀ L S).subtype =
        (Z F β).map (G₀ L S).subtype := by
  obtain ⟨h₀,h₁⟩ := bTwo_D_eq_centers_of_center_actions (reduced_triple h)
    (reduced_kernel_sylow h) hb c₀ c₁ hnt hnu
  have hm₀ := congrArg (map (G₀ L S).subtype) h₀
  have hm₁ := congrArg (map (G₀ L S).subtype) h₁
  change ((Q F β ⊓ Q F t).map (G₀ L S).subtype) = _ at hm₀
  change ((Q F α ⊓ Q F u).map (G₀ L S).subtype) = _ at hm₁
  rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true] at hm₀
  rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h false] at hm₁
  exact ⟨hm₀,hm₁⟩

/-- The complete p=2 noncentral branch of 10.6 from earlier source
center actions. The shifted pair comes from 10.3; its marked Chapter 7
center action is the sole second-orbit action input. Every D, fixed-space,
quadratic core, equal-field and involution-lifting premise is discharged. -/
theorem original_bTwo_noncentral_exclusion_of_center_family
    (h : HypothesisF11 L S) (hb : b F = 2) {u : Vertex F}
    (c₀ : BTwoCenterActionData F α β u k₀ W₀)
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hnc : ¬ Z F β ≤ centerIn (graphLocalGroup F β))
    (hnot : ∀ t, (graph F).Adj t α →
      ¬ stabilizer F α ≤ normalizer ((Q F t ⊓ Q F α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ t, (graph F).Adj t α → IsCriticalPair F β t →
      ⁅Z F β,Z F t⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F β α t k₁ W₁)) : False := by
  obtain ⟨t,ht,_,_,_,_,hc₁,hne₁,_⟩ := original_bTwo_shifted_pair_of_noncentral h hb
    c₀.terminal.symm hc hne hnc c₀.critical_product hnot
  obtain ⟨c₁⟩ := hcenters t ht hc₁ hne₁
  exact bTwo_paired_center_actions_impossible (reduced_triple h)
    (reduced_kernel_sylow h) hb c₀ c₁ E₀ E₁ hc hc₁ hne hne₁

/-- The central branch required by 10.7--10.10, on the actual reduced
F1.11 graph. The earlier center actions and 6.5 obstruction are retained;
no conclusion of Chapter 10 appears among the hypotheses. -/
theorem original_bTwo_center_central_of_center_family
    (h : HypothesisF11 L S) (hb : b F = 2) {u : Vertex F}
    (c₀ : BTwoCenterActionData F α β u k₀ W₀)
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hnot : ∀ t, (graph F).Adj t α →
      ¬ stabilizer F α ≤ normalizer ((Q F t ⊓ Q F α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ t, (graph F).Adj t α → IsCriticalPair F β t →
      ⁅Z F β,Z F t⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F β α t k₁ W₁)) :
    Z F β ≤ centerIn (graphLocalGroup F β) := by
  by_contra hnc
  exact original_bTwo_noncentral_exclusion_of_center_family h hb c₀ E₀ E₁ hc hne hnc hnot hcenters

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
