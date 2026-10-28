module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointExtension.Words

/-!
# Necessary extension equations for the literal Mathieu point restriction

The full-group involution B conjugates two elements S,T of the two-point
stabilizer to elements of the point stabilizer. Their actual images under
`pointStabilizerEquiv` are the four displayed special linear matrices.
Transporting any full-group representation into catalogue coordinates gives
an involution satisfying the corresponding intertwining equations and
commuting with the marked central scalar. No irreducibility of a restriction
is assumed. Excluding the competing entries is a separate finite calculation.

Source: James (1973), Lemma 8.3, used in Aschbacher–Smith H.12.1(1),
printed pp.393–394. Matrix data comes from the ATLAS-derived matrices in
`PointExtension.Words` and `PointModel.Coordinates`; their attribution is
retained in the J₄ `LinearModel/source/` directory.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion

open Matrix
open PointModel PointExtension
open Representation.SL3FourLocalCatalogue
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- S,T and their conjugates by the actual involution B, in the literal subgroup. -/
def localWord : Fin 4 → pointStabilizer :=
  ![⟨wordS, wordS_mem⟩, ⟨wordT, wordT_mem⟩,
    ⟨coreGeneratorB * wordS * coreGeneratorB, conjugate_wordS_mem⟩,
    ⟨coreGeneratorB * wordT * coreGeneratorB, conjugate_wordT_mem⟩]

/-- Matrices in the geometric natural coordinates, with omega fixed by the center. -/
def classicalMatrix : Fin 4 → Matrix (Fin 3) (Fin 3) Reference.F :=
  let w := (QuadraticAlgebra.omega : Reference.F)
  ![![![0, 1+w, w], ![1+w, 1+w, 1], ![w, 1+w, 1+w]],
    ![![w, w, 1], ![0, 0, w], ![1+w, 1, 0]],
    ![![1, 1+w, w], ![0, 1+w, 1], ![1+w, 1, w]],
    ![![1+w, 1, 1+w], ![w, w, 1+w], ![1, 1, 0]]]

private lemma classicalMatrix_det (j : Fin 4) : (classicalMatrix j).det = 1 := by
  revert j
  decide +kernel

/-- Concrete SL₃(4) values of the four words. -/
def classicalWord (j : Fin 4) : Reference.SL :=
  ⟨classicalMatrix j, by exact classicalMatrix_det j⟩

private def binaryWord : Fin 4 → Matrix12 :=
  ![matrixS, matrixT,
    fromRows ![148, 1513, 1412, 256, 509, 1681, 3095, 1717, 2666, 3623, 2372, 64],
    fromRows ![2956, 2392, 2936, 3531, 596, 1620, 1109, 2741, 1261, 2717, 1214, 3737]]

private lemma binaryWord_spec (j : Fin 4) :
    (((localWord j).val : Matrix12ˣ) : Matrix12) = binaryWord j := by
  fin_cases j
  · exact coe_wordS
  · exact coe_wordT
  · change (↑(coreGeneratorB : Matrix12ˣ) : Matrix12) * ↑(wordS : Matrix12ˣ) *
        ↑(coreGeneratorB : Matrix12ˣ) = _
    rw [show (↑(coreGeneratorB : Matrix12ˣ) : Matrix12) = matrixB from coe_coreB, coe_wordS]
    decide +kernel
  · change (↑(coreGeneratorB : Matrix12ˣ) : Matrix12) * ↑(wordT : Matrix12ˣ) *
        ↑(coreGeneratorB : Matrix12ˣ) = _
    rw [show (↑(coreGeneratorB : Matrix12ˣ) : Matrix12) = matrixB from coe_coreB, coe_wordT]
    decide +kernel

set_option maxRecDepth 4000 in
private lemma natural_basis : ∀ (j : Fin 4) (k : Fin 6),
    binaryWord j *ᵥ naturalInclusion (flatten.symm (Pi.single k 1)) =
      naturalInclusion ((classicalWord j).val *ᵥ flatten.symm (Pi.single k 1)) := by
  decide +kernel

private lemma natural_action (j : Fin 4) (v : Reference.W) :
    pointRepresentation (localWord j) (naturalInclusion v) =
      naturalInclusion ((classicalWord j).val *ᵥ v) := by
  have h : (binaryWord j).mulVecLin.comp (naturalInclusion.comp flatten.symm.toLinearMap) =
      naturalInclusion.comp (((classicalWord j).val.mulVecLin.restrictScalars (ZMod 2)).comp
        flatten.symm.toLinearMap) := by
    apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
    intro k
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.restrictScalars_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply]
      using natural_basis j k
  have hv := LinearMap.congr_fun h (flatten v)
  change binaryWord j *ᵥ naturalInclusion (flatten.symm (flatten v)) =
    naturalInclusion ((classicalWord j).val *ᵥ flatten.symm (flatten v)) at hv
  rw [flatten.symm_apply_apply] at hv
  change (((localWord j).val : Matrix12ˣ) : Matrix12) *ᵥ naturalInclusion v = _
  rw [binaryWord_spec]
  exact hv

/-- The displayed matrices are images under the actual subgroup equivalence. -/
theorem pointStabilizerEquiv_localWord (j : Fin 4) :
    pointStabilizerEquiv (localWord j) = classicalWord j := by
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  apply naturalInclusion_injective
  rw [← pointStabilizerEquiv_natural_action, natural_action]

/-- The catalogue operator in interleaved binary matrix coordinates. -/
def catalogueMatrix (i : CatalogueEntry) : Reference.SL →* Matrix12 :=
  Matrix.toLinAlgEquiv'.symm.toMonoidHom.comp
    ((LinearEquiv.conjAlgEquiv (ZMod 2) flattenPair).toMonoidHom.comp (catalogueRepresentation i))

/-- These equations are necessary for extending the catalogue action across B. -/
def ExtensionEquations (i : CatalogueEntry) (X : Matrix12) : Prop :=
  X * X = 1 ∧
  X * catalogueMatrix i (classicalWord 0) = catalogueMatrix i (classicalWord 2) * X ∧
  X * catalogueMatrix i (classicalWord 1) = catalogueMatrix i (classicalWord 3) * X ∧
  Commute X (catalogueMatrix i Representation.SL3FourNaturalDual.centralScalar)

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) M22TripleCover U)

/-- Restriction along the literal subgroup and the inverse of its actual comparison. -/
def transportedRestriction : Representation (ZMod 2) Reference.SL U :=
  (ρ.comp pointStabilizer.subtype).comp pointStabilizerEquiv.symm.toMonoidHom

/-- Transported full-group matrices in any specified catalogue equivalence. -/
def fullMatrix (i : CatalogueEntry)
    (e : (transportedRestriction ρ).Equiv (catalogueRepresentation i)) :
    M22TripleCover →* Matrix12 :=
  Matrix.toLinAlgEquiv'.symm.toMonoidHom.comp
    ((LinearEquiv.conjAlgEquiv (ZMod 2) (e.toLinearEquiv.trans flattenPair)).toMonoidHom.comp ρ)

theorem fullMatrix_on_pointStabilizer (i : CatalogueEntry)
    (e : (transportedRestriction ρ).Equiv (catalogueRepresentation i))
    (g : pointStabilizer) :
    fullMatrix ρ i e g = catalogueMatrix i (pointStabilizerEquiv g) := by
  change Matrix.toLinAlgEquiv'.symm ((e.toLinearEquiv.trans flattenPair).conj (ρ g)) =
    Matrix.toLinAlgEquiv'.symm (flattenPair.conj
      (catalogueRepresentation i (pointStabilizerEquiv g)))
  congr 1
  apply LinearMap.ext
  intro v
  change e.toLinearEquiv.trans flattenPair
      (ρ g ((e.toLinearEquiv.trans flattenPair).symm v)) =
    flattenPair (catalogueRepresentation i (pointStabilizerEquiv g) (flattenPair.symm v))
  have he := LinearMap.congr_fun (e.isIntertwining' (pointStabilizerEquiv g))
    (e.symm (flattenPair.symm v))
  change e (ρ ((pointStabilizerEquiv.symm (pointStabilizerEquiv g) : pointStabilizer) :
      M22TripleCover) (e.symm (flattenPair.symm v))) =
    catalogueRepresentation i (pointStabilizerEquiv g) (e (e.symm (flattenPair.symm v))) at he
  rw [pointStabilizerEquiv.symm_apply_apply, e.apply_symm_apply] at he
  exact congrArg flattenPair he

private lemma involution_intertwines {G R : Type*} [Group G] [Monoid R]
    (f : G →* R) (b k : G) (hb : b * b = 1) :
    f b * f k = f (b * k * b) * f b := by
  rw [← map_mul, ← map_mul]
  congr 1
  rw [mul_assoc, mul_assoc, hb, mul_one]

/-- Every actual extension supplies the small finite system. No restriction
irreducibility, semisimplicity, or choice of a constituent is used. -/
theorem fullMatrix_extensionEquations (i : CatalogueEntry)
    (e : (transportedRestriction ρ).Equiv (catalogueRepresentation i)) :
    ExtensionEquations i (fullMatrix ρ i e coreGeneratorB) := by
  let f := fullMatrix ρ i e
  have hw (j : Fin 4) : f (localWord j) = catalogueMatrix i (classicalWord j) := by
    rw [fullMatrix_on_pointStabilizer, pointStabilizerEquiv_localWord]
  change ExtensionEquations i (f coreGeneratorB)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul, generatorB_sq, map_one]
  · rw [← hw 0, ← hw 2]
    change f coreGeneratorB * f wordS = f (coreGeneratorB * wordS * coreGeneratorB) * f coreGeneratorB
    exact involution_intertwines f _ _ generatorB_sq
  · rw [← hw 1, ← hw 3]
    change f coreGeneratorB * f wordT = f (coreGeneratorB * wordT * coreGeneratorB) * f coreGeneratorB
    exact involution_intertwines f _ _ generatorB_sq
  · have hz : f scalar = catalogueMatrix i Representation.SL3FourNaturalDual.centralScalar := by
      exact (fullMatrix_on_pointStabilizer ρ i e pointScalar).trans
        (congrArg (catalogueMatrix i) pointStabilizerEquiv_pointScalar)
    rw [← hz]
    exact (show Commute coreGeneratorB scalar from
      Subgroup.mem_center_iff.mp scalar_mem_center coreGeneratorB).map f

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion
