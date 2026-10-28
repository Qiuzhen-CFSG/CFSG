module
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.BinarySylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# The PSU₃(3) endpoint of 1.1.5

The proved exceptional comparison carries every allowed field-nine Hermitian
model to the genuine octonion commutator group G₂(2)′. Full automorphism
coverage and its Sylow calculation show that the transported action is inner.
The common perfect-central-quotient argument lifts innerness to the original
automorphism and identifies the center with the two-core.

With the separate cover exclusion, this gives canonical row (a), using the
actual derived-group equivalence. Triviality of the center is retained as an
explicit premise until the unitary universal-cover result supplies it.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503; I.1.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure
open Atlas.G2.LieAutomorphismExtensions
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
variable {α : MulAut L} {P : Sylow 2 L}

/-- The genuine PSU₃(3)--G₂(2)′ comparison and binary automorphism theorem
force innerness of the original marked action upstairs. -/
theorem MarkedInvolution.unitary_three_three_inner_and_center
    (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 3 3) :
    α ∈ (MulAut.conj (G := L)).range ∧ center L = pCore 2 L := by
  obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := h
  let f := e.trans (J.projectiveEquivBinaryG2Derived hc hconj)
  obtain ⟨_, _, Q, hQ⟩ := d.centralQuotient_model_inputs f
  obtain ⟨g, _, hg⟩ := Atlas.G2.EvenInvolutionGeometry.binary_fixing_sylow_inner
    binaryConjugation_bijective Q (MulAut.centralQuotientAction f α) hQ
  exact d.inner_and_center_of_quotient_inner f ⟨g, hg.symm⟩

/-- The PSU₃(3) branch gives the derived G₂(2) alternative of canonical
row (a), once the independent cover exclusion has been discharged. -/
theorem MarkedInvolution.unitary_three_three_of_center_eq_bot
    (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 3 3) (hz : center L = ⊥) :
    ModelAction115 L α := by
  have hi := (d.unitary_three_three_inner_and_center h).1
  let f : L ≃* L ⧸ center L := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hs : IsSimpleGroup L := f.isSimpleGroup
  obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := h
  exact .lie hs (Or.inr (Or.inl (.g2_derived
    ⟨f.trans (e.trans (J.projectiveEquivBinaryG2Derived hc hconj))⟩))) hi

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
