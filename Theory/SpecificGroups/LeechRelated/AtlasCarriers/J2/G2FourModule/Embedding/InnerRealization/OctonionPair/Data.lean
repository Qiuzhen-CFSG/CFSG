module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Theory.AtlasPort.Algebra.SplitOctonion.BasisChecks

/-!
# Explicit octonion matrices over a computable field of four elements

The matrices act on columns in the literal split-octonion coordinate order.
Entries are encoded by `0, 1, z, z+1`, where `z² = z+1`. They are the witnesses
in `../source/candidate.json`. Subsequent modules independently certify their
invertibility, preservation of multiplication, and five presentation relators.
The quadratic-algebra construction parallels ATLAS GoldenModuloTwo and
GoldenFourFinite, but avoids importing the unrelated icosian lattice.

Source: Aschbacher--Smith, K.4.5, printed p.460/PDF p.471; ATLAS J2G1-P2.
Matrix provenance and ATLAS Research and Attribution License 1.0 are recorded
in `../source/README.md`, `LICENSES/ATLAS.txt`, and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair

abbrev Coeff := QuadraticAlgebra (ZMod 2) 1 1
instance coeff_irreducible : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide⟩
instance coeff_fintype : Fintype Coeff :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm
def z : Coeff := ⟨0,1⟩
abbrev Mat := Matrix (Fin 8) (Fin 8) Coeff
def aMatrix : Mat :=
  ![![1,0,0,1,1,0,0,1],
    ![0,1,0,0,0,1,0,0],
    ![0,0,1,0,0,0,1,0],
    ![0,0,0,1,0,0,0,1],
    ![0,0,0,0,1,0,0,1],
    ![0,0,0,0,0,1,0,0],
    ![0,0,0,0,0,0,1,0],
    ![0,0,0,0,0,0,0,1]]
def bMatrix : Mat :=
  ![![z,z,1,1,1,0,z,1],
    ![z,0,0,1,1,1,1,(z+1)],
    ![1,1,z,z,z,1,1,0],
    ![0,1,z,0,1,(z+1),1,1],
    ![0,1,z,1,0,(z+1),1,1],
    ![1,0,1,(z+1),(z+1),(z+1),0,1],
    ![z,1,0,1,1,1,0,(z+1)],
    ![1,(z+1),1,0,0,1,(z+1),(z+1)]]
def bInvMatrix : Mat :=
  ![![(z+1),(z+1),1,1,1,0,(z+1),1],
    ![(z+1),0,0,1,1,1,1,z],
    ![1,1,(z+1),(z+1),(z+1),1,1,0],
    ![0,1,(z+1),0,1,z,1,1],
    ![0,1,(z+1),1,0,z,1,1],
    ![1,0,1,z,z,z,0,1],
    ![(z+1),1,0,1,1,1,0,z],
    ![1,z,1,0,0,1,z,z]]


/-- The binary coefficient pair is a bijective four-element coordinate system. -/
theorem coeff_card : Fintype.card Coeff = 4 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd 1 1), Fintype.card_prod]
  decide

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
