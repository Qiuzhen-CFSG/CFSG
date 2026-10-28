module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.ThreeElement
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.Order72Exclusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Normalization

/-!
# Held's lambda separation

The involutions pi, lambda and pi*lambda cannot all be conjugate in the
ambient group. The proposed fusions give an element of order three in N_G(S)
centralizing pi*mu, where S is the displayed elementary subgroup of order
sixteen. Orbit counting forces the actual quotient N_G(S)/S to have order
72. The elementary-subgroup catalogue then gives fusion control in S, whose
nine pi-conjugates have product pi. This product is fixed by the normalizer,
contradicting the order-128 stabilizer of pi.

This assembles the order-three construction and the alternative exclusion
of both printed order-72 cases, discharging all their additional premises.
The resulting change of coordinates makes lambda nonconjugate to pi while
preserving the originally specified mu. No ambient pi--mu nonfusion,
centralizer order for mu, or global recognition result is used.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, pp.226--227.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Held's Lemma 2.4: pi, lambda and pi*lambda do not share an ambient conjugacy class. -/
public theorem lambda_separation :
    ¬ (IsConj D.z (D.a10ModelEmbedding e Coordinates.lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * Coordinates.lam))) := by
  intro h
  obtain ⟨x, hx, hc⟩ := LambdaSeparation.lambda_three_element D e h
  exact LambdaSeparation.lambda_order72_false D e h x hx hc
    (LambdaSeparation.quotient_card_of_three_centralizer D e x hx hc)

/-- Choose Held's normalized lambda without changing the specified noncentral involution. -/
public theorem exists_normalized_equiv_of_simple :
    ∃ e' : D.centralizer ≃* CentralizerModels.a10Centralizer,
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e ∧
      ¬ IsConj D.z (D.a10ModelEmbedding e' Coordinates.lam) :=
  exists_normalized_equiv D e (lambda_separation D e)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
