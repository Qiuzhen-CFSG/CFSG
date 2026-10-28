module
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant

/-!
# Cubic ratios under faithful equivariant actor embeddings

An injective actor map preserves elementary cubic subgroups and their exact
ratios. Taking the infimum gives an inequality between the two cubic ratios,
so strict and nonintegral bounds also transfer. The actual Chapter15 consumer
uses this to exclude outside-core locals in the ratio-two branch of 15.1.11.
Source: Aschbacher--Smith, printed p.1089.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)

theorem cubicRatio_le_of_injective_equivariant (f : G →* D)
    (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) :
    cubicRatio σ ≤ cubicRatio ρ := by
  refine le_iInf fun A => le_iInf fun hA => ?_
  let : IsElementaryAbelian 2 A := hA.1.2
  have ha : IsElementaryTwo (A.map f) := by
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hb
    exact hA.1.1 (Subgroup.map_injective hf (by simpa only [Subgroup.map_bot] using hb))
  have h : cubicRatio σ ≤ actionRatio σ (A.map f) := iInf_le_of_le (A.map f) (iInf_le_of_le
    ⟨ha, hA.2.map_equivariant ρ σ f E hE⟩ le_rfl)
  apply h.trans
  rw [actionRatio, actionRatio, ← fixedCodim_map_equivariant ρ σ f E hE,
    rank_map_injective f hf]
end Representation.BinaryOffender
