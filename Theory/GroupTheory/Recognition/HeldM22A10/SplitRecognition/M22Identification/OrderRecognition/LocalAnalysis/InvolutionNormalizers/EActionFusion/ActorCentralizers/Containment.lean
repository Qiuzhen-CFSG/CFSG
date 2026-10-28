module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers.OddCore
public import Theory.GroupTheory.ZStar.CoreFree

/-!
# The full ambient centralizer of the actor

Under contrary actor nonfusion, the local group C(a) ∩ C(z) is Sylow in
C(a), z is central and weakly closed in it, and the odd core of C(a) is
trivial. Glauberman's core-free theorem therefore makes z central in C(a).
Consequently C(a) equals the explicitly computed local group of order 32.
All hypotheses concern the actual subgroup C(a); simplicity of C(a) is
neither asserted nor needed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, C(a) analysis on p.6 and Lemma 7 on p.7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)
namespace CaseII
/-- The ambient actor centralizer equals its order-32 local subgroup. -/
public theorem actorCentralizer_eq_local (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    centralizer ({into D k a} : Set G) = actorLocalCentralizer D k := by
  let H := centralizer ({into D k a} : Set G)
  let zH : H := ⟨D.z, (actorLocalCentralizer_z_mem D k).1⟩
  obtain ⟨S, hS⟩ := actorLocalCentralizer_sylow D k hE hn
  have hzS : zH ∈ (S : Subgroup H) := by rw [hS]; exact actorLocalCentralizer_z_mem D k
  have hzC : zH ∈ center H := by
    refine Glauberman.ZStar.glauberman_zstar_corefree (actorCentralizer_oddCore D k hE hn)
      S zH ⟨fun h => D.z_ne_one (congrArg Subtype.val h), ?_⟩ hzS ?_ ?_
    · apply Subtype.ext
      change D.z ^ 2 = 1
      simpa only [D.z_order] using pow_orderOf_eq_one D.z
    · intro s hs
      rw [hS] at hs
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hs.2)
    · refine ⟨hzS, ?_⟩
      intro g hg
      rw [hS] at hg
      apply Subtype.ext
      exact actorLocalCentralizer_weakly_closed D k hE hn g g.property hg
  apply le_antisymm _ inf_le_left
  intro x hx
  exact ⟨hx, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_center_iff.mp hzC ⟨x, hx⟩))⟩
end CaseII

end Theory.GroupTheory.HeldM22A10.M22Identification
