module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.Interface
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion.ActorFusion

/-!
# Held's quotient fusion data from the earlier ambient actors

The explicit local words identify C_Q(p) with C2 × C2 × D8, where
Q = C_G(mu)/<mu>. Nonfusion makes this centralizer a Sylow two-subgroup.
The Section 2.13 actor yields p conjugate to zm, and the initial Section 4.1
actor yields p conjugate to lt. Lifting conjugacy to C_G(mu), together with
central fusion control and the two actors, leaves exactly the seven candidate
words required by the transfer argument on printed p.233.

The two actors may use different xi markings. A seed fixes either xi or
pi*xi, and the two choices give the same pairs of candidate conjugates.
Consequently this construction does not need the stronger compatibility
with alpha's xi, nor the crossing-fusion theorem used to prove it.

This module completes the implication from the earlier ambient actors.
Their existence from D, e, and nonfusion remains to be supplied before the
unconditional source theorem can be asserted. No QuotientCore, centralizer
order 2880, A6 section, or global recognition is assumed.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.13 and 4.1, proof of 4.2, p.233.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
open FaithfulExclusion
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Complete quotient fusion data from alpha and an initial nu. The unconditional
source assembly must construct both actors from the original hypotheses. -/
public theorem nonempty_transferFusion_of_sourceActors
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    {b d : Bit} (a : AlphaRelations D e d) (n : NuSeedRelations D e b) :
    Nonempty (TransferFusion (Q D e) (p D e)) := by
  obtain ⟨T, hT⟩ := exists_quotient_sylow_eq_centralizer D e hfusion
  let c : TransferModel.Model ≃* T :=
    (SourceFusion.centralizerCoordinates D e hfusion).trans (MulEquiv.subgroupCongr hT.symm)
  have hc (x : TransferModel.Model) : (c x : Q D e) = SourceFusion.into D e x :=
    SourceFusion.centralizerCoordinates_apply D e hfusion x
  obtain ⟨d', ⟨n'⟩⟩ := SourceFusion.exists_nuRelations_of_seed n
  refine ⟨{
    sylow := T
    coordinates := c
    mark_p := ?_
    centralizer_eq := hT.symm
    conj_lt := ?_
    conj_zm := ?_
    class_bound := ?_ }⟩
  · rw [hc, SourceFusion.into_p]
  · rw [hc]
    exact SourceFusion.conj_lt_of_nu D e n'
  · rw [hc]
    exact SourceFusion.conj_zm_of_alpha D e a
  · intro x hx
    rw [hc] at hx
    exact SourceFusion.class_bound_of_nonfusion D e hfusion
      (SourceFusion.not_conj_t_of_seed D e hfusion n)
      (SourceFusion.not_conj_zlt_of_nu D e hfusion n') x hx

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
