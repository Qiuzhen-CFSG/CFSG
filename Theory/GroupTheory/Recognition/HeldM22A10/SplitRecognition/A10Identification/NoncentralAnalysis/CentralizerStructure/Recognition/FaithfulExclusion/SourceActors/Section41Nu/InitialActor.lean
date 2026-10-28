module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.InitialActor.MarkedAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion.SNormalizerFusion.OrbitReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation

/-!
# Constructing Held's initial actor from the earlier tau fusion

Given pi~tau, the order-64 tau-centralizer overgroup makes N_G(S) non-two.
The earlier orbit calculation gives |N_G(S)|=1152 and the three normalized
S-fusions. Counting orbits in the relative centralizer C_{N_G(S)}(mu)
gives its order 192, hence an element of order three. Its binary action
has one of two possible orientations; inversion chooses the desired one,
and conjugation by 1 or tau makes mu-prime invert it.

Thus every initial seed relation is proved from the earlier tau fusion.
The unconditional construction still requires that fusion from Held 2.9--2.11;
no alpha producer, A6 section, full mu-centralizer order, or xi compatibility
is used here. The supplied alpha may remain fixed in the eventual assembly.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.10--2.11 and the first part of 4.1.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Fusion Fusion.LambdaSeparation

universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Construct the initial Section 4.1 actor from the earlier tau fusion.
The only extra premise is this source fusion, whose producer belongs to
Sections 2.9--2.11. All normalizer and action premises are discharged here. -/
public theorem exists_nuSeedRelations_of_tau_fusion
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (ht : IsConj D.z (D.a10ModelEmbedding e Coordinates.tau)) :
    ∃ b : Bit, Nonempty (NuSeedRelations D e b) := by
  have hsep := lambda_separation D e
  obtain ⟨P, hP, _, hPC, hPN⟩ := exists_tau_overgroup_in_normalizer D e ht
  have hn := sCase_overgroup_normalizer_not_isPGroup D e 0 P hP hPC hPN
  have h9 : (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 9 := by
    rcases sNormalizer_pi_orbit_eq_one_or_nine D e hf hsep with h | h
    · exfalso
      apply hn
      apply IsPGroup.of_card (n := 7)
      rw [normalizer_card, h]
      decide
    · exact h
  have hcard : Nat.card (sNormalizer D e) = 1152 := by rw [normalizer_card, h9]
  obtain ⟨b, _, hml, hpl⟩ := exists_s_fusion_of_orbit_nine D e hf hsep h9
  obtain ⟨v, hvN, hv3, hvm⟩ := exists_initialNu_three_of_normalizer_card D e hf hcard
  obtain ⟨a⟩ := nonempty_nuAction_of_initial_three D e b hf ht hml hpl v hvN hv3 hvm
  exact ⟨b, a.nonempty_seed⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
