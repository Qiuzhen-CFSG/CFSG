module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Numerics

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.aB2

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.aC

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.aF

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.aG

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.aJ

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.bD

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.bF


/-!
# The two complementary matrices belong to the literal generated algebras

The first complement is A(B²A+B+1)+(BA+1)B²+1; the second is
(B+1)AB+A+B+1. The product and addition certificates identify these algebra
expressions with the stored complement rows, so membership uses only closure
under multiplication, addition, and one. No group action is assumed.
Source matrices: `Degree320Pair/source/README.md`.
-/
public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneChecks

open Thompson.BinaryMatrix

private theorem aA_mem : decode 320 Data.aA.toArray ∈ generated false := by
  change matrixA false ∈ generated false
  exact Algebra.subset_adjoin (by simp)

private theorem aB_mem : decode 320 Data.aB.toArray ∈ generated false := by
  change matrixB false ∈ generated false
  exact Algebra.subset_adjoin (by simp)

private theorem bA_mem : decode 320 Data.bA.toArray ∈ generated true := by
  change matrixA true ∈ generated true
  exact Algebra.subset_adjoin (by simp)

private theorem bB_mem : decode 320 Data.bB.toArray ∈ generated true := by
  change matrixB true ∈ generated true
  exact Algebra.subset_adjoin (by simp)

private theorem ident_mem (variant : Bool) : decode 320 Data.ident.toArray ∈ generated variant := by
  rw [ident_matrix]
  exact (generated variant).one_mem

theorem a_membership : decode 320 Data.aS.toArray ∈ generated false := by

  have aB2_mem : decode 320 Data.aB2.toArray ∈ generated false := by
    rw [← Products.aB2.matrix]
    exact (generated false).mul_mem aB_mem aB_mem

  have aC_mem : decode 320 Data.aC.toArray ∈ generated false := by
    rw [← Products.aC.matrix]
    exact (generated false).mul_mem aB2_mem aA_mem

  have aD0_mem : decode 320 Data.aD0.toArray ∈ generated false := by
    rw [← aD0_add]
    exact (generated false).add_mem aC_mem aB_mem

  have aD_mem : decode 320 Data.aD.toArray ∈ generated false := by
    rw [← aD_add]
    exact (generated false).add_mem aD0_mem (ident_mem false)

  have aF_mem : decode 320 Data.aF.toArray ∈ generated false := by
    rw [← Products.aF.matrix]
    exact (generated false).mul_mem aA_mem aD_mem

  have aG_mem : decode 320 Data.aG.toArray ∈ generated false := by
    rw [← Products.aG.matrix]
    exact (generated false).mul_mem aB_mem aA_mem

  have aH_mem : decode 320 Data.aH.toArray ∈ generated false := by
    rw [← aH_add]
    exact (generated false).add_mem aG_mem (ident_mem false)

  have aJ_mem : decode 320 Data.aJ.toArray ∈ generated false := by
    rw [← Products.aJ.matrix]
    exact (generated false).mul_mem aH_mem aB2_mem

  have aS0_mem : decode 320 Data.aS0.toArray ∈ generated false := by
    rw [← aS0_add]
    exact (generated false).add_mem aF_mem aJ_mem

  have aS_mem : decode 320 Data.aS.toArray ∈ generated false := by
    rw [← aS_add]
    exact (generated false).add_mem aS0_mem (ident_mem false)

  exact aS_mem

theorem b_membership : decode 320 Data.bS.toArray ∈ generated true := by

  have bC_mem : decode 320 Data.bC.toArray ∈ generated true := by
    rw [← bC_add]
    exact (generated true).add_mem bB_mem (ident_mem true)

  have bD_mem : decode 320 Data.bD.toArray ∈ generated true := by
    rw [← Products.bD.matrix]
    exact (generated true).mul_mem bC_mem bA_mem

  have bF_mem : decode 320 Data.bF.toArray ∈ generated true := by
    rw [← Products.bF.matrix]
    exact (generated true).mul_mem bD_mem bB_mem

  have bS0_mem : decode 320 Data.bS0.toArray ∈ generated true := by
    rw [← bS0_add]
    exact (generated true).add_mem bF_mem bA_mem

  have bS1_mem : decode 320 Data.bS1.toArray ∈ generated true := by
    rw [← bS1_add]
    exact (generated true).add_mem bS0_mem bB_mem

  have bS_mem : decode 320 Data.bS.toArray ∈ generated true := by
    rw [← bS_add]
    exact (generated true).add_mem bS1_mem (ident_mem true)

  exact bS_mem

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneChecks
