module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.ScalarExtension

/-!
# Assembly of the eight larger absolute M₂₄ models

Four individual binary models and two inequivalent pairs give eight simple
modules after scalar extension. Unequal degrees separate all but the two
specified pairs. The coordinate scalar-extension comparison supplies actual
representations of the native M₂₄ on `Fin d → F` for every closed field F of
characteristic two, as required by `LargeModelsExist`.

This file proves the assembly from finite construction certificates. It does
not yet assert `largeModelsExist`: the binary models and the two pair
certificates remain unproved inputs. In particular, the ATLAS labels are
not used as irreducibility or carrier-identification proofs.

Sources: James, *The modular characters of the Mathieu groups*, J. Algebra
27 (1973), 57–111; Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 5.1, manuscript p.17; candidate degrees and matrices at
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
universe v

/-- Degrees of the eight binary candidates, with the repeated degrees adjacent. -/
def candidateDegree : Fin 8 → ℕ := ![120, 252, 220, 220, 320, 320, 1242, 1792]

/-- Every candidate lies outside the degree window under consideration. -/
theorem candidateDegree_gt (i : Fin 8) : 48 < candidateDegree i := by
  revert i
  decide +kernel

private theorem equal_degree_cases {i j : Fin 8} (hij : i ≠ j)
    (h : candidateDegree i = candidateDegree j) :
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
  revert i j
  decide +kernel

/-- Assemble four single models and two equal-degree pairs into the candidate
family. No model is constructed merely by assigning it a degree. -/
def binaryCandidate (a120 : BinaryModel 120) (a252 : BinaryModel 252)
    (a220 : BinaryPair 220) (a320 : BinaryPair 320)
    (a1242 : BinaryModel 1242) (a1792 : BinaryModel 1792) :
    ∀ i, BinaryModel (candidateDegree i) := by
  refine Fin.cases a120 ?_
  refine Fin.cases a252 ?_
  refine Fin.cases a220.first ?_
  refine Fin.cases a220.second ?_
  refine Fin.cases a320.first ?_
  refine Fin.cases a320.second ?_
  refine Fin.cases a1242 ?_
  exact Fin.cases a1792 (fun i => Fin.elim0 i)

/-- Distinct dimensions and the two pair certificates separate all eight
actual binary representations. -/
theorem binaryCandidate_pairwise (a120 : BinaryModel 120) (a252 : BinaryModel 252)
    (a220 : BinaryPair 220) (a320 : BinaryPair 320)
    (a1242 : BinaryModel 1242) (a1792 : BinaryModel 1792) :
    Pairwise fun i j => IsEmpty
      ((binaryCandidate a120 a252 a220 a320 a1242 a1792 i).representation.Equiv
        (binaryCandidate a120 a252 a220 a320 a1242 a1792 j).representation) := by
  intro i j hij
  constructor
  intro e
  have hdim : candidateDegree i = candidateDegree j := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      e.toLinearEquiv.finrank_eq
  rcases equal_degree_cases hij hdim with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact a220.inequivalent.false e
  · exact a220.inequivalent.false e.symm
  · exact a320.inequivalent.false e
  · exact a320.inequivalent.false e.symm

/-- The finite binary construction certificates discharge the larger-model
premise of `absoluteSmallSpectrum_of_models` over every coefficient universe. -/
theorem largeModelsExist_of_candidates
    (a120 : BinaryModel 120) (a252 : BinaryModel 252)
    (a220 : BinaryPair 220) (a320 : BinaryPair 320)
    (a1242 : BinaryModel 1242) (a1792 : BinaryModel 1792) : LargeModelsExist.{v} := by
  exact largeModelsExist_of_binaryFamily candidateDegree
    (fun i => (binaryCandidate a120 a252 a220 a320 a1242 a1792 i).representation)
    (fun i => (binaryCandidate a120 a252 a220 a320 a1242 a1792 i).absolute)
    (binaryCandidate_pairwise a120 a252 a220 a320 a1242 a1792) candidateDegree_gt

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
