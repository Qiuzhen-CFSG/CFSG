module
public import Stellmacher.Recognition.LyonsU3Four.TableIColumnReflection
public import Stellmacher.Recognition.LyonsU3Four.TableISignedDegreeTransport
public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorDegrees

/-!
# Pulling a degree-twelve witness back from Table I

A signed row equivalence preserves the absolute degrees and the weighted
centralizer sum. The column reflection fixes the distinguished column and the
row indices. Thus either numerical normalization returns the same unique
absolute-degree-twelve row to the original character data.

These adapters are the final numerical step before applying rationality to the
original ambient irreducible character; no character section identity is
transported through the reflection.
Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), §3, Lemma 4(c).
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

variable {I J : Type*} [Fintype I] [Fintype J]
variable {d : GeneralizedDecompositionData I} {d' : GeneralizedDecompositionData J}
variable {r : I → ℤ} {r' : J → ℤ}

def DegreeTwelveWitness.signedTransport (w : DegreeTwelveWitness d r)
    (h : SignedDegreeEquiv d d' r r') : DegreeTwelveWitness d' r' where
  row := h.equiv w.row
  abs_degree := (h.natAbs_eq w.row).trans w.abs_degree
  unique j hj := by
    obtain ⟨i, rfl⟩ := h.equiv.surjective j
    apply congrArg h.equiv
    exact w.unique i ((h.natAbs_eq i).symm.trans hj)
  weight_identity := by
    rw [h.weightedColumn_eq (fun j => h.z_eq j 0)]
    exact w.weight_identity

def DegreeTwelveWitness.reflectColumns (w : DegreeTwelveWitness d r) :
    DegreeTwelveWitness d.reflectColumns r where
  row := w.row
  abs_degree := w.abs_degree
  unique := w.unique
  weight_identity := by
    simpa only [reflectColumns_weightedColumn, reflectColumns_iDz,
      columnReflection_zero] using w.weight_identity

def DegreeTwelveWitness.of_reflectColumns
    (w : DegreeTwelveWitness d.reflectColumns r) : DegreeTwelveWitness d r where
  row := w.row
  abs_degree := w.abs_degree
  unique := w.unique
  weight_identity := by
    simpa only [reflectColumns_weightedColumn, reflectColumns_iDz,
      columnReflection_zero] using w.weight_identity

end Stellmacher.Recognition.LyonsU3Four
