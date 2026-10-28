module

public import CFSG.Quasithin.ChapterD.Section03.SourceConsequences
public import CFSG.Quasithin.ChapterD.Section03.ActorKernel

/-!
# The actual Sylow-span kernel in D.3.4

The kernel of X on the span of the T-conjugates of the seed is a proper
X T-invariant subgroup of X. The two source actor alternatives therefore
put that literal kernel in the Frattini subgroup of X.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma D.3.4(2), printed pp.193–194.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
  {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

/-- D.3.4(2) for the literal action kernel C_X(V_T). -/
theorem SourceHypotheses.sylowSpan_actorKernel_le_frattini
    (h : SourceHypotheses K ρ T X I) :
    subspaceKernel ρ (orbitSpan ρ (T : Subgroup G) I) X ≤
      (frattini X).map X.subtype := by
  let := h.normal
  let W := orbitSpan ρ (T : Subgroup G) I
  let N := subspaceKernel ρ W X
  have hW : X ⊔ (T : Subgroup G) ≤ subspaceStabilizer ρ W :=
    sup_le (orbitSpan_component_invariant ρ
      (by rw [normalizer_eq_top]; exact le_top) h.seed) (orbitSpan_invariant ρ _ _)
  apply h.cases.proper_normal_le_frattini (subspaceKernel_le ρ W X)
  · apply le_normalizer_iff.mpr
    intro g hg n hn
    refine ⟨h.normal.conj_mem n hn.1 g, ?_⟩
    intro w hw
    have hi : ρ g⁻¹ w ∈ W := (hW ((X ⊔ (T : Subgroup G)).inv_mem hg) w).2 hw
    have hh := congrArg (ρ g) (hn.2 _ hi)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, mul_assoc] using hh
  · intro he
    apply h.seed.not_le_fixedSpace ρ
    intro v hv x
    have hx : (x : G) ∈ N := by
      rw [show N = X from he]
      exact x.property
    exact hx.2 v (le_orbitSpan ρ (T : Subgroup G) I hv)

end CFSG.Quasithin.ChapterD.Section03
