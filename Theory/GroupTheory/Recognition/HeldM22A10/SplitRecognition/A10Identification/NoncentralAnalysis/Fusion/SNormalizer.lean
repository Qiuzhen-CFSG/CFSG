module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.Overgroups
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.PiLambda
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.TauOrder
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.TauSylow

/-!
# The S-normalizer part of Held's pi--mu nonfusion argument

The two local order-32 centralizers, their order-64 ambient overgroups, and
the tau overgroup's normalization of S are established in `Overgroups`.
The pi-lambda alternative is excluded in `PiLambda` by the action of its
order-64 overgroup on the center and squares of the local centralizer.
With pi-lambda excluded, tau fusion makes the seven nonidentity elements of
U=<pi,mu,tau> exactly the pi-class in S. The faithful action of N_G(S)/S on U
then forces |N_G(S)|=384, as proved in `TauOrder`. The order-64 tau-centralizer
overgroup contradicts this order by Sylow conjugacy and the local centralizer
catalogue, as proved in `TauSylow`.

Thus pi~mu and pi not~lambda imply that neither tau nor pi*lambda is conjugate
to pi. This completes the S-normalizer part of Lemma 2.6; the remaining parts
of pi--mu nonfusion belong to its assembly owner. This argument works for
finite G without simplicity and discharges every overgroup and order premise.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.228.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Under pi--mu fusion and lambda nonfusion, both S-normalizer alternatives
in Held's Lemma 2.6 are impossible. -/
public theorem tau_piLambda_nonfusion_of_mu
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e Coordinates.lam)) :
    (¬ IsConj D.z (D.a10ModelEmbedding e Coordinates.tau)) ∧
      ¬ IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * Coordinates.lam)) := by
  refine ⟨?_, piLambda_nonfusion_of_mu D e hmu hlam⟩
  intro htau
  obtain ⟨P, hc, hQP, hPC, hPN⟩ := exists_tau_overgroup_in_normalizer D e htau
  exact tau_overgroup_normalizer_card_ne_384 D e P hc hQP hPC hPN
    (normalizer_card_of_mu_tau D e hmu hlam htau)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
