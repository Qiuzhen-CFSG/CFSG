module

public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.WreathedSylow
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvolutionCentralizer
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Stellmacher.Recognition.FongWreathed

/-!
# The exceptional isomorphism PSU₃(3) ≃ G₂(2)′

The actual commutator subgroup of the split-octonion automorphism group is
simple, has a height-two wreathed Sylow subgroup, and has a solvable
involution centralizer. Fong's recognition theorem therefore identifies it
with the projective special unitary matrix group over GF(9).

Orthonormal Hermitian bases and entrywise field transport then give the
comparison for any coefficient field of order nine and any nondegenerate
Hermitian form with cube Frobenius conjugation. The projective side is the
actual image of the determinant-one isometry group in PGL.

Sources: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), pp.69–76; Aschbacher–Smith,
*The Classification of Quasithin Groups*, G.7.2(3) and G.7.3(1), printed
p.348 (combined 1 March 2004 manuscript). The octonion construction and
root calculations are inherited from the licensed ATLAS port through the
imports; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section

namespace Atlas.G2
open BinaryParabolicPair

/-- Fong recognition applied to the actual binary octonion commutator group. -/
theorem nonempty_commutator_binary_equiv_psu3 :
    Nonempty (commutator (Model (ZMod 2)) ≃* ABG.PSU3 3 1 (by decide)) := by
  let : IsSimpleGroup (commutator (Model (ZMod 2))) := isSimple_commutator_binary
  let : Group.IsSolvable
      (Subgroup.centralizer ({derivedInvolution} : Set DerivedModel)) :=
    isSolvable_centralizer_derivedInvolution
  exact Stellmacher.Recognition.FongWreathed.nonempty_equiv_psu3
    derivedSylow derivedSylow_isWreathedOfHeight derivedInvolution derivedInvolution_order

end Atlas.G2

namespace BenderSuzuki.MatrixGroups.HermitianForm

/-- The exceptional comparison for every field-nine ternary Hermitian model
with cube conjugation, retaining its actual projective matrix image. -/
noncomputable def projectiveEquivBinaryG2Derived
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = 3 ^ 2) (hconj : ∀ x, J.conj x = x ^ 3) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (Classical.choice
    (Matrix.SU3.InnerThreeRank.exists_projective_equiv_standard 3 F J hcard hconj)).trans
    (Classical.choice Atlas.G2.nonempty_commutator_binary_equiv_psu3).symm

end BenderSuzuki.MatrixGroups.HermitianForm
