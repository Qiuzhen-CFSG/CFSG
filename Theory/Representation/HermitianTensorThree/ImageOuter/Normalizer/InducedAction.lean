module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Contracts
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.InducedAction.Factors
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.InducedAction.Semilinearity
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.InducedAction.Graph
/-!
# Automorphisms induced by the binary Hermitian normalizer

The actual image is PSL₃ in odd half-degree and SL₃ in even half-degree.
Standard automorphism coverage on those carriers leaves a possible graph
factor after the full GL₃ and coefficient factors are removed. The
scalar-centralizer premise makes every binary normalizer semilinear over
the actual fixed field. The descended trace obstruction then excludes
inverse transpose, completing induced-action coverage in both parity cases.

The scalar-centralizer theorem is an explicit input, independently produced
for the unconditional normalizer assembly. This theorem assumes neither
normalizer coverage nor graph exclusion, and retains all inner-diagonal
matrices. Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.4.2 setup and H.4.4(7), printed pp.380–381; the retained PGL₃(4) extension
also occurs in H.4.6(3), printed p.382.
-/

public section
noncomputable section
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions.SixCommutators
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

private theorem remove_conj {G : Type*} [Group G] (e s a b : G)
    (h : e * a * e⁻¹ = s * b * s⁻¹) :
    (s⁻¹ * e) * a * (s⁻¹ * e)⁻¹ = b := by
  calc
    _ = s⁻¹ * (e * a * e⁻¹) * s := by group
    _ = s⁻¹ * (s * b * s⁻¹) * s := by rw [h]
    _ = b := by group

/-- Every induced automorphism is realized by a full GL₃ congruence followed by
an automorphism of the extension field, assuming only scalar-centralizer coverage. -/
theorem inducedActionCoverage_of_scalarCentralizer
    (hcentral : ScalarCentralizerCoverage n) : InducedActionCoverage n := by
  have hgraph (e : Space n ≃ₗ[ZMod 2] Space n) (he : e ∈ binaryNormalizer n)
      (h : ∀ a : Cover n, e * binaryActionHom n a * e⁻¹ =
        binaryActionHom n (graphSL (E n) a)) : False := by
    obtain ⟨τ, hτ⟩ := normalizer_semilinear_of_scalarCentralizer n hcentral e he
    exact graph_not_implemented_semilinear n e τ hτ h
  intro e he
  obtain ⟨g, τ, ε, h⟩ := normalizer_standard_factors n e he
  cases ε with
  | false =>
    exact ⟨g, τ, fun a => (h a).trans (semilinearCongruence_conj n g τ a).symm⟩
  | true =>
    let s := semilinearCongruence n g τ
    let t := binaryCongruence n (reversalGL (E n))
    have hs : s ∈ binaryNormalizer n := semilinearCongruence_mem_normalizer n g τ
    have ht : t ∈ binaryNormalizer n := binaryCongruence_mem_normalizer n _
    have hfirst (a : Cover n) :
        (s⁻¹ * e) * binaryActionHom n a * (s⁻¹ * e)⁻¹ =
          binaryActionHom n (oppositionGraphSL (E n) a) := by
      apply remove_conj
      change e * binaryActionHom n a * e⁻¹ =
        semilinearCongruence n g τ * binaryActionHom n (oppositionGraphSL (E n) a) *
          (semilinearCongruence n g τ)⁻¹
      rw [semilinearCongruence_conj, h]
      rfl
    exfalso
    apply hgraph (t⁻¹ * (s⁻¹ * e))
      ((binaryNormalizer n).mul_mem ((binaryNormalizer n).inv_mem ht)
        ((binaryNormalizer n).mul_mem ((binaryNormalizer n).inv_mem hs) he))
    intro a
    apply remove_conj
    rw [hfirst]
    exact (binaryCongruence_conj n (reversalGL (E n)) (graphSL (E n) a)).symm

end Representation.HermitianTensorThree.ImageOuter
