module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.TauOrder.Action

/-!
# The S-normalizer order in Held's tau case

If pi is conjugate to mu and tau, but not to lambda, the normalizer of
S=<pi,mu,tau,lambda> has order 384. Pi-lambda nonfusion identifies the
seven-element pi-class in S with U\{1}, where U=<pi,mu,tau>.
The faithful N_G(S)/S action on U embeds in PSL3(2). Its pi orbit has
at most seven points, so the image is proper; the Sylow parabolic theorem
restricts its order to 8 or 24. The order-64 tau-centralizer overgroup
excludes the two-group case, leaving |N_G(S)|=16*24.

This is an intermediate consequence of the contradictory tau alternative
in Held, Illinois J. Math. 13 (1969), Lemma 2.6, printed p.228. The separate
Sylow-fusion contradiction is not used here. No simplicity assumption or
additional local-centralizer premise is needed.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The normalizer of S has order 384 in the mu-and-tau fusion alternative. -/
public theorem normalizer_card_of_mu_tau
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : IsConj D.z (D.a10ModelEmbedding e tau)) :
    Nat.card (normalizer (ambientElementary D e 1 : Set G)) = 384 := by
  have h := normalizer_S_le_normalizer_tauFusionSpace D e hmu hlam htau
  have horbit := normalizer_pi_orbit_card_le_seven D e hmu hlam htau
  have hdvd := tauNormalizerAction_card_dvd D e h horbit
  have haction := tauNormalizerAction_card D e h
  have hnormalizer := LambdaSeparation.normalizer_card D e
  have h8 : 8 ∣ Nat.card (tauNormalizerAction D e h).range := by
    rw [haction]
    exact dvd_mul_right _ _
  have hcases : Nat.card (tauNormalizerAction D e h).range = 8 ∨
      Nat.card (tauNormalizerAction D e h).range = 24 := by
    have hm := Nat.mem_divisors.mpr ⟨hdvd, by decide⟩
    have hc : (24 : ℕ).divisors = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
    rw [hc] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  rcases hcases with hsmall | hlarge
  · have hcN : Nat.card (LambdaSeparation.sNormalizer D e) = 128 := by omega
    have htwo : IsPGroup 2 (LambdaSeparation.sNormalizer D e) :=
      IsPGroup.of_card (n := 7) (by simpa using hcN)
    obtain ⟨P, hP, _, hPC, hPN⟩ := exists_tau_overgroup_in_normalizer D e htau
    exact (sCase_overgroup_normalizer_not_isPGroup D e 0 P hP hPC hPN htwo).elim
  · change Nat.card (LambdaSeparation.sNormalizer D e) = 384
    omega

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
