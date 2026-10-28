module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.ThreeElement.NonTwo
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.ThreeElement.OddOrder
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.ThreeElement.Normalization

/-!
# Held's order-three element for lambda separation

Write S=⟨pi,mu,tau,lambda⟩ and W=S⟨mu′xi⟩. Its center is the elementary
eight-group E=⟨pi,mu,lambda⟩, and C_G(E)=W. The unique nonidentity square
pi*mu is fixed by every W-normalizer. An order-64 extension of W in
C_G(lambda), together with xi's action on E, proves that N_G(W) is not
a two-group. Its action kernel is W and |Aut(E)|=168, so its only possible
odd primes are three and seven. Seven is excluded by orbit counting on E
with the two fixed points 1 and pi*mu.

An element of order three in N_G(W) preserves S because W has only two
elementary subgroups of order sixteen. It therefore lies in N_G(S) and
centralizes pi*mu, precisely the witness needed by NormalizerAction.
The proof in fact only needs the proposed fusion of pi with lambda; the
export below retains the requested simple-group and two-fusion interface.
This is the conditional construction in the first part of Held's Lemma 2.4,
not the unconditional lambda-separation theorem.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, printed p.226. The action on E replaces
the printed Sylow-subgroup comparison, and the two-subgroup catalogue gives
exactly the normalization needed for the odd-order witness. Conjugators here
use g*x*g⁻¹, opposite to the source's convention.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The order-three witness in the first part of Held's Lemma 2.4. -/
public theorem lambda_three_element [IsSimpleGroup G]
    (h : IsConj D.z (D.a10ModelEmbedding e Coordinates.lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * Coordinates.lam))) :
    ∃ x : sNormalizer D e, orderOf x = 3 ∧
      Commute (x : G) (D.a10ModelEmbedding e (Coordinates.pi * Coordinates.mu)) :=
  lambda_three_element_of_core_three D e
    (lambdaCore_three_of_not_two D e (lambdaCore_normalizer_not_two D e h.1))

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
