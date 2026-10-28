module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.SL2Subgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.FactorPosition
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.SylowCenter

/-!
# Assembly of the unitary Cartan position

The projective model and form transport identify each involution-centralizer
solvable residual in D ≅ PSU₃(q), for an odd prime q > 3, with SL₂(q).
The supplied SL₂ subgroup is itself one such residual, based at an involution
centralizing B.

`FactorPosition` places the cyclic factors at an involution in the ambient
Sylow center. `SylowCenter` proves that the entire center centralizes its
residual, using rigidity of prime-field SL₂ automorphisms fixing a Sylow
two-subgroup pointwise. Perfectness then identifies this involution residual
with the canonical residual of C_D(Z(S)). The final `CaseThree.unitaryPosition`
assembles both results from the original `AmbientInput` and `CaseThree`
hypotheses, giving the canonical cyclic decomposition and its actual SL₂(q)
isomorphism.

All unitary parameters retain fixed-field order q, matrix-field order q²,
Frobenius conjugation, and actual projective Hermitian-form isomorphisms.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, and the proof of 1.3.4,
printed pp.510–511. The requested SL₂ parameter is q, consistent with
A.3.15's SL₂ over the defining prime field.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {G : Type*} [Group G] [Finite G]

namespace UnitaryPosition

/-- Identify the canonical residual once full-center centralization and the cyclic position are proved. -/
theorem canonical_position_of_involution
    {D B S : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q) (hmodel : ClassicalGroup.IsPSU D 3 q)
    (z : D) (hz : orderOf z = 2) (hzS : (z : G) ∈ centerImage S)
    (hcentral : involutionResidual D z ≤ centralizer (centerImage S : Set G))
    (hposition : CyclicDecomposition B (involutionResidual D z)) :
    CyclicDecomposition B (canonicalResidual D S) ∧
      Nonempty (canonicalResidual D S ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  rw [canonicalResidual_eq_involutionResidual D S z hzS hcentral]
  exact ⟨hposition, involutionResidual_equiv D q hq hlarge hmodel z hz⟩

/-- A proved normalizer conjugacy supplies the cyclic-position premise. -/
theorem canonical_position_of_conjugate
    {D B S K : Subgroup G} {q : ℕ} [Fact q.Prime] {ε : Sign}
    (h : CaseThree D B S K q .unitary ε) (hlarge : 3 < q)
    (z : D) (hz : orderOf z = 2) (hzS : (z : G) ∈ centerImage S)
    (hcentral : involutionResidual D z ≤ centralizer (centerImage S : Set G))
    (hconj : ∃ g ∈ normalizer B,
      K.map (MulAut.conj g).toMonoidHom = involutionResidual D z) :
    CyclicDecomposition B (canonicalResidual D S) ∧
      Nonempty (canonicalResidual D S ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  obtain ⟨g, hg, hK⟩ := hconj
  exact canonical_position_of_involution h.odd_characteristic hlarge h.model z hz hzS
    hcentral (h.toCyclicDecomposition.of_conjugate hg hK)

/-- Assemble the unitary case from the two independent geometric inputs,
discharged from the source hypotheses by `CaseThree.unitaryPosition` below. -/
theorem caseThree_position_of_involution_inputs
    {D B S K : Subgroup G} {q : ℕ} [Fact q.Prime] {ε : Sign}
    (h : CaseThree D B S K q .unitary ε) (hlarge : 3 < q)
    (hcentral : ∀ z : D, orderOf z = 2 → (z : G) ∈ centerImage S →
      involutionResidual D z ≤ centralizer (centerImage S : Set G))
    (hposition : ∃ z : D, orderOf z = 2 ∧ (z : G) ∈ centerImage S ∧
      CyclicDecomposition B (involutionResidual D z)) :
    CyclicDecomposition B (canonicalResidual D S) ∧
      Nonempty (canonicalResidual D S ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  obtain ⟨z, hz, hzS, hB⟩ := hposition
  exact canonical_position_of_involution h.odd_characteristic hlarge h.model z hz hzS
    (hcentral z hz hzS) hB

end UnitaryPosition

/-- The unitary Cartan factors are positioned at the canonical residual
`C_D(Z(S))^∞`, and this residual is isomorphic to SL₂(q). -/
theorem CaseThree.unitaryPosition
    {κ : GroupClass} {D B K : Subgroup G} {S : Sylow 2 G} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup G) K q .unitary .unitary)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q) :
    CyclicDecomposition B (canonicalResidual D (S : Subgroup G)) ∧
      Nonempty (canonicalResidual D (S : Subgroup G) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  exact UnitaryPosition.caseThree_position_of_involution_inputs hC hlarge
    (UnitaryPosition.caseThree_involutionResidual_le_centralizer_centerImage hA hC hn hlarge)
    (UnitaryPosition.caseThree_factor_position hA hC hn hlarge)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
