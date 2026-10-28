module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.ModelInvolutions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section

/-!
# Reduction of Held's noncentral involution analysis to its A6 section

A normal A6 subgroup of C_G(mu) with dihedral quotient of order eight gives
|C_G(mu)| = 2880. Since |C_G(z)| = 384 and conjugate elements have isomorphic
centralizers, it also gives ambient nonconjugacy of z and mu. The proof is
valid for arbitrary universes and uses the exact element from SourceChecks.

This is a conditional reduction. The remaining source arguments are the
nonfusion theorem in Section 2.6 and the construction of the A6 section in
Section 4.2. The latter may use nonfusion as an explicit input; both must be
proved before this module can supply unconditional local analysis.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.6, 2.11 and 4.2.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10
universe u v
namespace A10Identification.NoncentralAnalysis

private theorem centralizer_card_equiv {G : Type u} {K : Type v} [Group G] [Group K]
    (f : G ≃* K) (x : G) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({f x} : Set K)) := by
  apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
  intro a
  change a ∈ centralizer ({x} : Set G) ↔ f a ∈ centralizer ({f x} : Set K)
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro ha
    simpa only [map_mul] using congrArg f ha
  · intro ha
    apply f.injective
    simpa only [map_mul] using ha

private theorem centralizer_card_conj {G : Type u} [Group G] {x y : G}
    (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he : (MulAut.conj g) x = y := hg
  simpa only [he] using centralizer_card_equiv (MulAut.conj g) x

end A10Identification.NoncentralAnalysis
namespace LocalData
open A10Identification.NoncentralAnalysis
variable {G : Type u} [Group G] (D : LocalData G)

/-- Conditional assembly from the genuine section of the ambient centralizer.
The construction of this section, including the nonfusion needed by its source
proof, remains an obligation of the unconditional local analysis. -/
public theorem a10NoncentralAnalysis_of_section
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
    (s : AlternatingSixSection (Subgroup.centralizer ({D.a10NoncentralInvolution e} : Set G))) :
    ¬ IsConj D.z (D.a10NoncentralInvolution e) ∧
      Nat.card (Subgroup.centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880 := by
  have hc := s.card
  refine ⟨?_, hc⟩
  intro h
  have he := centralizer_card_conj h
  have hz := D.centralizer_card
  change Nat.card (Subgroup.centralizer ({D.z} : Set G)) = 384 at hz
  rw [hz, hc] at he
  contradiction

end LocalData
end Theory.GroupTheory.HeldM22A10
