module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.Kernel
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.Pair

/-!
# Certified binary G₂ cycle matrices

The saved 64 cycle vectors form a basis of the numerical incidence kernel.
Their adapted basis gives a 32-dimensional half and coordinates on its literal
quotient. The two saved flag actors have exactly the four published factor
matrices. The eight ambient actors permute a complementary pair consisting of
this half and its root-F image.

All finite arithmetic is checked by Lean's kernel. The separate coset
certificate identifies these numerical spaces and actors with the actual
G₂ incidence representation; the source-theorem owner retains that assembly.
Source application: Aschbacher–Smith G.7.2(3), printed p.348/PDF p.359.
-/
