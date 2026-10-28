module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear00
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear06
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear12
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear18
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear24
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear30
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear36
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear42
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear48
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear54
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear60
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear66
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Linear72
/-!
# Affine consequences of the normalized polynomial equations

The normalization products and both Gaussian stages are checked by kernel
reduction. The first stage gives 78 linear relations, and the second expresses
each eliminated variable affinely in the 47 free variables. This module proves
that the corresponding affine relations vanish, then proves soundness of an
ideal certificate with affine multipliers.

The witnesses are regenerated from `../source/witnesses.json`. The Gaussian checks are partitioned into bounded pieces; their evaluation
soundness is proved in `Pieces.lean`.
-/

@[expose] public section
set_option maxRecDepth 10000
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.Elimination
open Janko4.GeneratorCertificates

private theorem normalization_checked : affineRow normalizationAffine = normalizationRow := by
  decide +kernel

private theorem normalizationProducts_checked : ∀ i : Fin 125,
    productRow normalizationAffine [some i] = normalizationProducts.get i := by
  decide +kernel

private theorem values_checked : ∀ i : Fin 78,
    xorList ((valueWitnesses.get i).map linearRows.get) = affineRow (valueAffines.get i) := by
  decide +kernel

private theorem zeros_append {n m : ℕ} (a : Vector ℕ n) (b : Vector ℕ m)
    (x : Coefficients) (ha : ∀ i, eval (a.get i) x = 0)
    (hb : ∀ i, eval (b.get i) x = 0) :
    ∀ i, eval ((a ++ b).get i) x = 0 := by
  intro i
  change eval ((a ++ b)[i.val]) x = 0
  rw [Vector.getElem_append]
  split
  · exact ha _
  · exact hb _

theorem inputRows_zero (x : Coefficients)
    (heq : ∀ e : Fin 987, eval (equationRows.get e) x = 0)
    (hnorm : eval normalizationRow x = 0) :
    ∀ e : Fin 1113, eval (inputRows.get e) x = 0 := by
  have hnp (i : Fin 125) : eval (normalizationProducts.get i) x = 0 := by
    rw [← normalizationProducts_checked i, eval_product, normalization_checked, hnorm,
      zero_mul]
  unfold inputRows
  apply zeros_append (equationRows ++ (⟨#[normalizationRow], rfl⟩ : Vector ℕ 1))
    normalizationProducts x
  · apply zeros_append equationRows (⟨#[normalizationRow], rfl⟩ : Vector ℕ 1) x heq
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hnorm
  · exact hnp

theorem valueAffines_zero (x : Coefficients)
    (hinputs : ∀ e : Fin 1113, eval (inputRows.get e) x = 0) :
    ∀ i : Fin 78, eval (affineRow (valueAffines.get i)) x = 0 := by
  have hl (i : Fin 78) : eval (linearRows.get i) x = 0 := by
    fin_cases i
    · exact linear0_zero x hinputs
    · exact linear1_zero x hinputs
    · exact linear2_zero x hinputs
    · exact linear3_zero x hinputs
    · exact linear4_zero x hinputs
    · exact linear5_zero x hinputs
    · exact linear6_zero x hinputs
    · exact linear7_zero x hinputs
    · exact linear8_zero x hinputs
    · exact linear9_zero x hinputs
    · exact linear10_zero x hinputs
    · exact linear11_zero x hinputs
    · exact linear12_zero x hinputs
    · exact linear13_zero x hinputs
    · exact linear14_zero x hinputs
    · exact linear15_zero x hinputs
    · exact linear16_zero x hinputs
    · exact linear17_zero x hinputs
    · exact linear18_zero x hinputs
    · exact linear19_zero x hinputs
    · exact linear20_zero x hinputs
    · exact linear21_zero x hinputs
    · exact linear22_zero x hinputs
    · exact linear23_zero x hinputs
    · exact linear24_zero x hinputs
    · exact linear25_zero x hinputs
    · exact linear26_zero x hinputs
    · exact linear27_zero x hinputs
    · exact linear28_zero x hinputs
    · exact linear29_zero x hinputs
    · exact linear30_zero x hinputs
    · exact linear31_zero x hinputs
    · exact linear32_zero x hinputs
    · exact linear33_zero x hinputs
    · exact linear34_zero x hinputs
    · exact linear35_zero x hinputs
    · exact linear36_zero x hinputs
    · exact linear37_zero x hinputs
    · exact linear38_zero x hinputs
    · exact linear39_zero x hinputs
    · exact linear40_zero x hinputs
    · exact linear41_zero x hinputs
    · exact linear42_zero x hinputs
    · exact linear43_zero x hinputs
    · exact linear44_zero x hinputs
    · exact linear45_zero x hinputs
    · exact linear46_zero x hinputs
    · exact linear47_zero x hinputs
    · exact linear48_zero x hinputs
    · exact linear49_zero x hinputs
    · exact linear50_zero x hinputs
    · exact linear51_zero x hinputs
    · exact linear52_zero x hinputs
    · exact linear53_zero x hinputs
    · exact linear54_zero x hinputs
    · exact linear55_zero x hinputs
    · exact linear56_zero x hinputs
    · exact linear57_zero x hinputs
    · exact linear58_zero x hinputs
    · exact linear59_zero x hinputs
    · exact linear60_zero x hinputs
    · exact linear61_zero x hinputs
    · exact linear62_zero x hinputs
    · exact linear63_zero x hinputs
    · exact linear64_zero x hinputs
    · exact linear65_zero x hinputs
    · exact linear66_zero x hinputs
    · exact linear67_zero x hinputs
    · exact linear68_zero x hinputs
    · exact linear69_zero x hinputs
    · exact linear70_zero x hinputs
    · exact linear71_zero x hinputs
    · exact linear72_zero x hinputs
    · exact linear73_zero x hinputs
    · exact linear74_zero x hinputs
    · exact linear75_zero x hinputs
    · exact linear76_zero x hinputs
    · exact linear77_zero x hinputs
  intro i
  exact eval_zero_of_xor linearRows (valueWitnesses.get i) _ (values_checked i) x hl

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.Elimination
