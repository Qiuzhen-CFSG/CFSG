module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0000
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0045
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0090
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0135
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0180
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0225
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0270
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0315
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0360
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0405
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0450
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0495
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0540
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0585
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0630
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0675
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0720
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0765
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0810
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0855
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0900
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0945
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products.Checks0990

/-!
# All quadratic matrix products

Assembly of kernel-checked finite certificates for the calculation described in
KernelBound/source/README.md.
-/

@[expose] public section
open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate.ExteriorAnnihilators PolynomialCertificate.PullbackCoefficients ExteriorInvariance

theorem productWords_spec (p : Fin 1035) :
    decodeHalf (productWords.get p) = (squareBasis (productPairs.get p).1)ᵀ * testForm *
      squareBasis (productPairs.get p).2 := by
  by_cases h0 : p.val < 45
  · exact products_0 p.val (by omega) h0 p.isLt
  by_cases h45 : p.val < 90
  · exact products_45 p.val (by omega) h45 p.isLt
  by_cases h90 : p.val < 135
  · exact products_90 p.val (by omega) h90 p.isLt
  by_cases h135 : p.val < 180
  · exact products_135 p.val (by omega) h135 p.isLt
  by_cases h180 : p.val < 225
  · exact products_180 p.val (by omega) h180 p.isLt
  by_cases h225 : p.val < 270
  · exact products_225 p.val (by omega) h225 p.isLt
  by_cases h270 : p.val < 315
  · exact products_270 p.val (by omega) h270 p.isLt
  by_cases h315 : p.val < 360
  · exact products_315 p.val (by omega) h315 p.isLt
  by_cases h360 : p.val < 405
  · exact products_360 p.val (by omega) h360 p.isLt
  by_cases h405 : p.val < 450
  · exact products_405 p.val (by omega) h405 p.isLt
  by_cases h450 : p.val < 495
  · exact products_450 p.val (by omega) h450 p.isLt
  by_cases h495 : p.val < 540
  · exact products_495 p.val (by omega) h495 p.isLt
  by_cases h540 : p.val < 585
  · exact products_540 p.val (by omega) h540 p.isLt
  by_cases h585 : p.val < 630
  · exact products_585 p.val (by omega) h585 p.isLt
  by_cases h630 : p.val < 675
  · exact products_630 p.val (by omega) h630 p.isLt
  by_cases h675 : p.val < 720
  · exact products_675 p.val (by omega) h675 p.isLt
  by_cases h720 : p.val < 765
  · exact products_720 p.val (by omega) h720 p.isLt
  by_cases h765 : p.val < 810
  · exact products_765 p.val (by omega) h765 p.isLt
  by_cases h810 : p.val < 855
  · exact products_810 p.val (by omega) h810 p.isLt
  by_cases h855 : p.val < 900
  · exact products_855 p.val (by omega) h855 p.isLt
  by_cases h900 : p.val < 945
  · exact products_900 p.val (by omega) h900 p.isLt
  by_cases h945 : p.val < 990
  · exact products_945 p.val (by omega) h945 p.isLt
  exact products_990 p.val (by omega) p.isLt p.isLt

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
