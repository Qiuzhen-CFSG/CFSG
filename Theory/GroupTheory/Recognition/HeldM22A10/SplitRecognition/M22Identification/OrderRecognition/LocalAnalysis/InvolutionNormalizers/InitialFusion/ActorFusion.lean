module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.ActorFusion.Transport
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.ActorFusion.FiniteAction

/-!
# Janko's Lemma 3: fusion from a to d

Assume the distinguished central involution z is conjugate to the actor a.
Relative normality of the elementary sixteen F and Sylow conjugacy carry
this fusion into N_G(F). The normalizer's actual action on F has stabilizer
of z equal to the local Sylow action. A kernel-checked finite action argument
then supplies a normalizer element conjugating z to d.

No extra fusion, quotient-recognition, splitting, or normalizer-action
hypothesis is used. The argument works for finite ambient groups without
using simplicity, hence applies to the simple-group recognition problem.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 3 and preceding paragraph, printed p.5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy CaseII CaseII.ActorFusion
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Janko's Lemma 3, with the actual marked Case II coordinates. -/
public theorem actor_fusion_of_a (h : IsConj D.z (into D k a)) : IsConj D.z (into D k d) := by
  have ha : ∃ f ∈ actorImage D k, f zF = aF := by
    obtain ⟨n, hn⟩ := normalizer_fuses_a D k h
    refine ⟨normalizerAction D k n, ⟨n, rfl⟩, ?_⟩
    apply Subtype.ext
    apply into_injective D k
    rw [normalizerAction_apply]
    simpa only [zF, aF, into_z_zero D k] using hn
  obtain ⟨f, hf, hfd⟩ := finite_actor_fusion (actorImage D k)
    (localActor_le_actorImage D k) (actorImage_stabilizer D k) ha
  obtain ⟨n, rfl⟩ := hf
  refine isConj_iff.mpr ⟨(n : G), ?_⟩
  have hh := congrArg (fun x : modelF => into D k x) hfd
  rw [normalizerAction_apply] at hh
  simpa only [zF, dF, into_z_zero D k] using hh

end Theory.GroupTheory.HeldM22A10.M22Identification
