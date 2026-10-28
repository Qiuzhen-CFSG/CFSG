module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Reduction
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120.Norm
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

/-!
# Full matrix algebras for the degree-120 and degree-252 M24 candidates

For each pair of published binary matrices, the initial polynomial norm lies
in every subalgebra containing the two generators. Checked contractions produce
a rank-one operator, and checked spanning row and column orbits then produce
every matrix unit. Thus both pairs generate their full matrix algebras without
an irreducibility, degree-spectrum or native-realization hypothesis.

Applying density to an actual native realization proves absolute irreducibility
of its representation. The realization remains an explicit input; its independent
construction is retained by the degree-120/252 model assembly. The conditional
norm reductions remain publicly available through `MatrixDensity.Reduction`.

Sources: the unchanged ATLAS matrices M24G1-f2r120B0 and M24G1-f2r252B0 and
`source/density-120.json`, `source/density-252.json`; James, J. Algebra 27 (1973),
57–111. All certificate identities are proved in Lean; see
`MatrixDensity/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252

/-- The two degree-120 matrices generate the full binary matrix algebra. -/
theorem matrix120_full
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : Q = ⊤ :=
  matrix120_full_of_norm Q hA (MatrixDensity.Degree120.norm_mem Q hA)

/-- The two degree-252 matrices generate the full binary matrix algebra. -/
theorem matrix252_full
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 252) (Fin 252) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix252 j ∈ Q) : Q = ⊤ :=
  matrix252_full_of_norm Q hA (MatrixDensity.Degree252.norm_mem Q hA)

/-- Every actual native realization of the degree-120 matrices is absolutely irreducible. -/
theorem NativeRealization.absolute120 (r : NativeRealization 120 matrix120) :
    r.representation.IsAbsolutelyIrreducible :=
  r.absolute matrix120_full

/-- Every actual native realization of the degree-252 matrices is absolutely irreducible. -/
theorem NativeRealization.absolute252 (r : NativeRealization 252 matrix252) :
    r.representation.IsAbsolutelyIrreducible :=
  r.absolute matrix252_full

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
