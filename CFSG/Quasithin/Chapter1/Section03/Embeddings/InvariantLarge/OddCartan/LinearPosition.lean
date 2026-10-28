module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.SL2Subgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.ProjectiveSylow
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.SylowCenter

/-!
# Assembly of the linear Cartan position

The projective involution-centralizer residual and its transport to the
ambient group are proved in `InvolutionModel`. The supplied SL₂ subgroup
is identified with the residual at its central involution in `SL2Subgroups`.
Perfectness identifies the canonical residual once the whole Sylow center
centralizes an involution residual, by `ResidualGeometry`.

`FactorPosition` places the cyclic factors at an involution in the ambient
Sylow center. `SylowCenter` proves that the whole Sylow center centralizes
its residual, using the rigidity of prime-field SL₂ automorphisms fixing
a Sylow two-subgroup pointwise. The final `CaseThree.linearPosition`
assembles these results from the original `AmbientInput` and `CaseThree`
hypotheses, giving both the canonical cyclic decomposition and its actual
SL₂(q) isomorphism.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, and the proof of
1.3.4, printed pp.510–511 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J] [Finite J]

/-- Conditional position assembly. The full Sylow-center identity and the
cyclic-factor position remain explicit premises; the SL₂ model is proved. -/
theorem CaseThree.linearPosition_of_involution
    {D B S K : Subgroup J} {q : ℕ} [Fact q.Prime]
    (h : CaseThree D B S K q .linear .linear) (hlarge : 3 < q)
    {z : J} (hzD : z ∈ D) (hz : orderOf z = 2)
    (hR : canonicalResidual D S = involutionResidual D z)
    (hB : CyclicDecomposition B (involutionResidual D z)) :
    CyclicDecomposition B (canonicalResidual D S) ∧
      Nonempty (canonicalResidual D S ≃* SL(2, ZMod q)) := by
  rw [hR]
  exact ⟨hB, involutionResidual_equiv h.odd_characteristic hlarge h.model hzD hz⟩

/-- Assemble the two independent geometric inputs, as supplied from the
source hypotheses by `CaseThree.linearPosition` below. -/
theorem CaseThree.linearPosition_of_involution_inputs
    {D B S K : Subgroup J} {q : ℕ} [Fact q.Prime]
    (h : CaseThree D B S K q .linear .linear) (hlarge : 3 < q)
    (hposition : ∃ z ∈ D ⊓ centerImage S, orderOf z = 2 ∧
      CyclicDecomposition B (involutionResidual D z))
    (hcenter : ∀ z ∈ D ⊓ centerImage S, orderOf z = 2 →
      involutionResidual D z ≤ centralizer (centerImage S : Set J)) :
    CyclicDecomposition B (canonicalResidual D S) ∧
      Nonempty (canonicalResidual D S ≃* SL(2, ZMod q)) := by
  obtain ⟨z, hz, ho, hB⟩ := hposition
  exact h.linearPosition_of_involution hlarge hz.1 ho
    (canonicalResidual_eq_involutionResidual D S hz.2 (hcenter z hz ho)) hB

/-- The linear Cartan factors are positioned at the canonical residual
`C_D(Z(S))^∞`, and this residual is isomorphic to SL₂(q). -/
theorem CaseThree.linearPosition
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .linear .linear)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q) :
    CyclicDecomposition B (canonicalResidual D (S : Subgroup J)) ∧
      Nonempty (canonicalResidual D (S : Subgroup J) ≃* SL(2, ZMod q)) := by
  exact hC.linearPosition_of_involution_inputs hlarge
    (hC.linear_factorPosition hA hn hlarge)
    (fun _ hz hz2 =>
      hC.linear_involutionResidual_le_centralizer_centerImage hA hn hlarge hz hz2)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
