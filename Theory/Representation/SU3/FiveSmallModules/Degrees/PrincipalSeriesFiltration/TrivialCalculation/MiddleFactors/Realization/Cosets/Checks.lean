module
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Cosets.Data

/-!
# Kernel certificates for the fixed coset representatives and transitions

The representative checks certify determinant one and preservation of the
antidiagonal Hermitian form. Each transition supplies a valid root coordinate
and a nonzero full-torus coordinate, and its matrix product is checked against
the fixed `MiddleFactors.image`. A recovery table certifies distinct normalized
bottom rows. `Cosets` uses these facts to construct literal Borel cosets.

The disjoint batches of 21 bound the kernel reduction cache. The unbatched
representative check used 5.6 GiB; a batch of 21 used 2.8 GiB, including imports.
All finite decisions run in the kernel.

Source: `MiddleFactors/source/standard_flag_data.txt`, lines 133–276;
Guralnick–Malle Proposition 4.3, p.10; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
open BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
open Matrix
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization.CosetCertificate

-- The unbatched representative certificate peaked at 5.6 GiB.
-- Disjoint batches keep kernel reduction caches bounded; sequential elaboration
-- avoids simultaneous cache allocation by these independent finite certificates.
set_option Elab.async false

def RepresentativeValid (i : Fin 126) : Prop :=
  (representativeMatrix i).det = 1 ∧
    form.conjTranspose (representativeMatrix i) * form.form * representativeMatrix i = form.form

private theorem representatives_0 : ∀ i : Fin 126,
    0 ≤ i.val → i.val < 21 → RepresentativeValid i := by
  simp only [RepresentativeValid, Matrix.det_fin_three]
  decide +kernel

private theorem representatives_1 : ∀ i : Fin 126,
    21 ≤ i.val → i.val < 42 → RepresentativeValid i := by
  simp only [RepresentativeValid, Matrix.det_fin_three]
  decide +kernel

private theorem representatives_2 : ∀ i : Fin 126,
    42 ≤ i.val → i.val < 63 → RepresentativeValid i := by
  simp only [RepresentativeValid, Matrix.det_fin_three]
  decide +kernel

private theorem representatives_3 : ∀ i : Fin 126,
    63 ≤ i.val → i.val < 84 → RepresentativeValid i := by
  simp only [RepresentativeValid, Matrix.det_fin_three]
  decide +kernel

private theorem representatives_4 : ∀ i : Fin 126,
    84 ≤ i.val → i.val < 105 → RepresentativeValid i := by
  simp only [RepresentativeValid, Matrix.det_fin_three]
  decide +kernel

private theorem representatives_5 : ∀ i : Fin 126,
    105 ≤ i.val → i.val < 126 → RepresentativeValid i := by
  simp only [RepresentativeValid, Matrix.det_fin_three]
  decide +kernel

/-- Every displayed representative satisfies the determinant and Hermitian equations. -/
theorem representative_valid (i : Fin 126) :
    (representativeMatrix i).det = 1 ∧
      form.conjTranspose (representativeMatrix i) * form.form * representativeMatrix i = form.form := by
  by_cases h0 : i.val < 21
  · exact representatives_0 i (by omega) h0
  by_cases h1 : i.val < 42
  · exact representatives_1 i (by omega) h1
  by_cases h2 : i.val < 63
  · exact representatives_2 i (by omega) h2
  by_cases h3 : i.val < 84
  · exact representatives_3 i (by omega) h3
  by_cases h4 : i.val < 105
  · exact representatives_4 i (by omega) h4
  exact representatives_5 i (by omega) i.isLt

def transition (j : Fin 2) (i : Fin 126) : F25 × F25 × F25 :=
  let t := (transitionExponents j)[i.val]!
  (entry t.1, entry t.2.1, entry t.2.2)

theorem transition_valid : ∀ j i,
    (transition j i).2.1 + form.conj (transition j i).2.1 +
      (transition j i).1 * form.conj (transition j i).1 = 0 ∧
    (transition j i).2.2 ≠ 0 := by
  decide +kernel

def transitionRoot (j : Fin 2) (i : Fin 126) : hermitianUnipotentCoord form :=
  ⟨((transition j i).1, (transition j i).2.1), (transition_valid j i).1⟩

def transitionTorus (j : Fin 2) (i : Fin 126) : F25ˣ :=
  Units.mk0 (transition j i).2.2 (transition_valid j i).2

def TransitionMatrixValid (j : Fin 2) (i : Fin 126) : Prop :=
  representativeMatrix i * tableActorMatrix j =
    (hermitianUnipotentMatrix form (transitionRoot j i) *
      hermitianTorusMatrix form (transitionTorus j i)) * representativeMatrix (image j i)

private theorem transitions_0_0 : ∀ i : Fin 126,
    0 ≤ i.val → i.val < 21 → TransitionMatrixValid 0 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_0_1 : ∀ i : Fin 126,
    21 ≤ i.val → i.val < 42 → TransitionMatrixValid 0 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_0_2 : ∀ i : Fin 126,
    42 ≤ i.val → i.val < 63 → TransitionMatrixValid 0 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_0_3 : ∀ i : Fin 126,
    63 ≤ i.val → i.val < 84 → TransitionMatrixValid 0 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_0_4 : ∀ i : Fin 126,
    84 ≤ i.val → i.val < 105 → TransitionMatrixValid 0 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_0_5 : ∀ i : Fin 126,
    105 ≤ i.val → i.val < 126 → TransitionMatrixValid 0 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_1_0 : ∀ i : Fin 126,
    0 ≤ i.val → i.val < 21 → TransitionMatrixValid 1 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_1_1 : ∀ i : Fin 126,
    21 ≤ i.val → i.val < 42 → TransitionMatrixValid 1 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_1_2 : ∀ i : Fin 126,
    42 ≤ i.val → i.val < 63 → TransitionMatrixValid 1 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_1_3 : ∀ i : Fin 126,
    63 ≤ i.val → i.val < 84 → TransitionMatrixValid 1 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_1_4 : ∀ i : Fin 126,
    84 ≤ i.val → i.val < 105 → TransitionMatrixValid 1 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

private theorem transitions_1_5 : ∀ i : Fin 126,
    105 ≤ i.val → i.val < 126 → TransitionMatrixValid 1 i := by
  simp only [TransitionMatrixValid]
  decide +kernel

theorem transition_matrix (j : Fin 2) (i : Fin 126) :
    representativeMatrix i * tableActorMatrix j =
      (hermitianUnipotentMatrix form (transitionRoot j i) *
        hermitianTorusMatrix form (transitionTorus j i)) * representativeMatrix (image j i) := by
  fin_cases j
  · by_cases h0 : i.val < 21
    · exact transitions_0_0 i (by omega) h0
    by_cases h1 : i.val < 42
    · exact transitions_0_1 i (by omega) h1
    by_cases h2 : i.val < 63
    · exact transitions_0_2 i (by omega) h2
    by_cases h3 : i.val < 84
    · exact transitions_0_3 i (by omega) h3
    by_cases h4 : i.val < 105
    · exact transitions_0_4 i (by omega) h4
    exact transitions_0_5 i (by omega) i.isLt
  · by_cases h0 : i.val < 21
    · exact transitions_1_0 i (by omega) h0
    by_cases h1 : i.val < 42
    · exact transitions_1_1 i (by omega) h1
    by_cases h2 : i.val < 63
    · exact transitions_1_2 i (by omega) h2
    by_cases h3 : i.val < 84
    · exact transitions_1_3 i (by omega) h3
    by_cases h4 : i.val < 105
    · exact transitions_1_4 i (by omega) h4
    exact transitions_1_5 i (by omega) i.isLt

def rowKey (v : Fin 3 → F25) : Bool × F25 × F25 :=
  (decide (v 0 = 0), v 1 / v 0, v 2 / v 0)

def rowCode (k : Bool × F25 × F25) : ℕ :=
  if k.1 then 625 else
    k.2.1.re.val + 5 * k.2.1.im.val + 25 * (k.2.2.re.val + 5 * k.2.2.im.val)

theorem key_recovers_index : ∀ i,
    keyIndex[rowCode (rowKey (representativeMatrix i 2))]! = i.val := by
  decide +kernel

theorem rowKey_injective : Function.Injective (fun i => rowKey (representativeMatrix i 2)) := by
  intro i j h
  apply Fin.ext
  exact (key_recovers_index i).symm.trans
    ((congrArg (fun k => keyIndex[rowCode k]!) h).trans (key_recovers_index j))

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization.CosetCertificate
