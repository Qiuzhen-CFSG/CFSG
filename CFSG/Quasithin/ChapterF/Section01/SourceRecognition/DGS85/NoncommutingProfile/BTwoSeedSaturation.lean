module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntrinsic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedFieldSource

/-!
# Saturating the central seed

The subgroup called `V` in the proof of DGS (10.7) is first constructed from
the two radius-one/core factors.  The source then proves that this subgroup is
the whole `Q_alpha`; this is a genuine saturation step and must not be hidden
in the definition of the seed.  The intrinsic span theorem from
`BTwoSeedIntrinsic` reduces the step to the literal source inclusion
`Q_alpha <= span(V_x ∩ Q_alpha) ⊔ D_alpha`.

This file records that reduction and its original marked transport.  The
saturation premise is deliberately explicit: it is the remaining 10.8
source argument, while the equality and all quotient transports are proved
here.  No quotient model or field-parameter conclusion is assumed.

Source: DGS, *Groups and Graphs* (1985), proof of (10.7)--(10.8),
printed pp.158--161.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem centralSeed_eq_Q_of_span
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hsat : Q F v ≤
      (⨆ x : Vertex F, ⨆ (_ : (graph F).Adj v x), V F x 1 ⊓ Q F v) ⊔
        D F m t) :
    centralSeed F v m t = Q F v := by
  have hspan := c.seed_eq_neighbor_span h hS hb ht hne
  have hle : centralSeed F v m t ≤ Q F v := by
    obtain ⟨g, hg, hop⟩ := c.exists_opposite_lift h ht hne
    obtain ⟨d, hd, _⟩ := c.exists_oppositeGeometry h hS hb g hg hop
    rw [hspan]
    exact sup_le (iSup_le fun x => iSup_le fun hx =>
      inf_le_right) d.separated
  apply le_antisymm hle
  rw [hspan]
  exact hsat

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The original F1.11 transport of the saturation bridge.  The premise is
the literal reduced-source inclusion; the conclusion is the equality of the
actual seed image and the original alpha core. -/
theorem original_bTwo_seed_eq_core_of_span
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hsat : Q F₀ α ≤
      (⨆ x : Vertex F₀, ⨆ (_ : (graph F₀).Adj α x), V F₀ x 1 ⊓ Q F₀ α) ⊔
        D F₀ β t) :
    (centralSeed F₀ α β t).map (G₀ L S).subtype = (parabolic L S 0).pCoreIn 2 := by
  have heq := centralSeed_eq_Q_of_span (reduced_triple h)
    (reduced_kernel_sylow h) hb c ht hne hsat
  have heq' : centralSeed F₀ α β t = Q F₀ α := by
    simpa only [reducedFamily] using heq
  calc
    (centralSeed F₀ α β t).map (G₀ L S).subtype =
        (Q F₀ α).map (G₀ L S).subtype := congrArg (map (G₀ L S).subtype) heq'
    _ = (parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
