module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules

/-!
# The source weight-two family in the M22 cocode

A pair of coordinate vectors lies in the even core. Its image under both
literal quotient maps defines the source vector; the distinguished pair maps
to zero. The family called O₂ in H.15 consists of the images of pairs joining
coordinate 0 to a native moving coordinate. Its nonzero, orbit and stabilizer
properties are separate obligations, not part of this definition.

Source: Aschbacher--Smith, H.13.1 and H.15.1, printed pp.395,398;
the orbit is described again before 8.1.1 on printed p.712.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace MathieuCode

theorem m22EvenPair_mem_core (i j : Fin 24) :
    (Pi.single i 1 + Pi.single j 1 : Full) ∈ Core := by
  rw [BinaryPermutation.mem_core]
  simp [Pi.single_apply, Finset.sum_add_distrib]

/-- The sum of two coordinate vectors in the actual even core. -/
def m22EvenPair (i j : Fin 24) : Core :=
  ⟨Pi.single i 1 + Pi.single j 1, m22EvenPair_mem_core i j⟩

/-- The image of a coordinate pair in the literal ten-dimensional quotient. -/
def m22CocodePair (i j : Fin 24) : M22Cocode :=
  m22PairLine.mkQ (codeInCore.mkQ (m22EvenPair i j))

/-- The source O₂ family, with the actual native moving coordinates retained. -/
def m22WeightTwoFamily : Set M22Cocode :=
  Set.range (fun i : Fin 22 => m22CocodePair 0 (m22Coordinates i))

theorem m22CocodePair_distinguished : m22CocodePair 0 9 = 0 := by
  apply (Submodule.Quotient.mk_eq_zero m22PairLine).mpr
  change m22PairClass ∈ m22PairLine
  exact Submodule.subset_span (Set.mem_singleton _)

end MathieuCode
