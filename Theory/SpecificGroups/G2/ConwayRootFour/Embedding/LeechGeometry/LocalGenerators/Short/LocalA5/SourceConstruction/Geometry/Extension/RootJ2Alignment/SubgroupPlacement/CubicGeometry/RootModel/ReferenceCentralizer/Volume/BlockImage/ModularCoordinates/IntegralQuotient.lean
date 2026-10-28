module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.Coordinates

/-!
# Integral-basis coordinates on the actual binary Leech quotient

The displayed glued quaternion basis gives an integral linear equivalence
with the retained Leech lattice. Reducing these integral coefficients, with
kernel exactly twice the lattice, constructs the binary equivalence. A
rational basis identity then descends to the literal binary action. Applying
this to the two checked inverse-adjoint generator matrices gives the actions
used in the reference eigenspace coordinate comparison.

No rational coefficient is reduced modulo two. The scalar eigenspace and its
three-dimensional coordinates remain separate obligations.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284.
The basis and generators are the John Bray ATLAS 6L34G1-Ar6aB0 construction;
the retained Leech comparison is the Gerald Höhn ATLAS port, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. See LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff for the retained attribution and license.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates
open Long.Block Long.Block.Realization

theorem basisMap_injective : Function.Injective basisMap := by
  intro x y h
  have hi := congrArg (fun v => basisInverse.map (Int.castRingHom ℚ) *ᵥ v) h
  rw [basisMap_apply, basisMap_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    inverse_mul_basis, Matrix.one_mulVec, Matrix.one_mulVec] at hi
  funext i
  have hh : (x i : ℚ) = (y i : ℚ) := congrFun hi i
  exact_mod_cast hh

def integralBasis : (Index → ℤ) ≃ₗ[ℤ] lattice :=
  LinearEquiv.ofBijective basisMap.rangeRestrict
    ⟨fun _ _ h => basisMap_injective (congrArg Subtype.val h),
      fun x => by obtain ⟨z, hz⟩ := x.property; exact ⟨z, Subtype.ext hz⟩⟩

def latticeComparison : lattice ≃ₗ[ℤ] rationalLeech where
  toFun x := ⟨matrixComparison x, (matrixComparison_lattice x).mp x.property⟩
  invFun x := ⟨matrixComparison.symm x, (matrixComparison_lattice _).mpr (by
    simpa only [matrixComparison.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext (matrixComparison.symm_apply_apply x)
  right_inv x := Subtype.ext (matrixComparison.apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add matrixComparison x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (matrixComparison.restrictScalars ℤ) r x.val)

def integralEquiv : (Index → ℤ) ≃ₗ[ℤ] leech :=
  integralBasis.trans (latticeComparison.trans latticeEmbeddingEquiv.symm)

theorem integralEquiv_agrees (z : Index → ℤ) :
    rationalEmbedding (integralEquiv z).val = matrixComparison (basisMap z) := by
  exact congrArg Subtype.val
    (latticeEmbeddingEquiv.apply_symm_apply (latticeComparison (integralBasis z)))

def binaryReduction : leech →+ (Index → Bit) where
  toFun x i := (integralEquiv.symm x i : Bit)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

theorem binaryReduction_surjective : Function.Surjective binaryReduction := by
  intro v
  refine ⟨integralEquiv (fun i => (v i).val), ?_⟩
  ext i
  change ((integralEquiv.symm (integralEquiv _) i : ℤ) : Bit) = v i
  rw [integralEquiv.symm_apply_apply]
  simp

theorem binaryReduction_kernel : twiceLeech = binaryReduction.ker := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change binaryReduction ((2 : ℕ) • z) = 0
    rw [map_nsmul]
    ext i
    simp
  · intro hx
    have hd (i : Index) : (2 : ℤ) ∣ integralEquiv.symm x i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
      exact congrFun hx i
    choose z hz using hd
    refine ⟨integralEquiv z, ?_⟩
    apply integralEquiv.symm.injective
    change integralEquiv.symm ((2 : ℕ) • integralEquiv z) = integralEquiv.symm x
    rw [map_nsmul, integralEquiv.symm_apply_apply]
    funext i
    exact (hz i).symm

def binaryCoordinates : LeechModTwo ≃ₗ[Bit] (Index → Bit) :=
  let e := (QuotientAddGroup.quotientAddEquivOfEq binaryReduction_kernel).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective binaryReduction binaryReduction_surjective)
  { e with map_smul' := ZMod.map_smul e }

def binaryEquiv : (Index → Bit) ≃ₗ[Bit] LeechModTwo := binaryCoordinates.symm

theorem binaryCoordinates_reduce (x : leech) :
    binaryCoordinates (leechReduction x) = binaryReduction x := rfl

theorem binaryEquiv_cast (z : Index → ℤ) :
    binaryEquiv (fun i => (z i : Bit)) = leechReduction (integralEquiv z) := by
  apply binaryCoordinates.injective
  rw [binaryEquiv, LinearEquiv.apply_symm_apply, binaryCoordinates_reduce]
  ext i
  change (z i : Bit) = (integralEquiv.symm (integralEquiv z) i : Bit)
  rw [integralEquiv.symm_apply_apply]

theorem integralEquiv_action (g : LeechIsometryGroup) (M : RealMatrix)
    (N : Matrix Index Index ℤ)
    (hM : M * basisMatrix = basisMatrix * N.map (Int.castRingHom ℚ))
    (hg : ∀ x : Space, (fullIsometryEquiv g).val (matrixComparison x) =
      matrixComparison (M *ᵥ x)) (z : Index → ℤ) :
    g.val (integralEquiv z) = integralEquiv (N *ᵥ z) := by
  apply Subtype.ext
  apply rationalEmbedding_injective
  rw [← rationalExtension_agrees, integralEquiv_agrees]
  change (fullIsometryEquiv g).val (matrixComparison (basisMap z)) = _
  rw [hg, integralEquiv_agrees, basisMap_apply, basisMap_apply,
    integerEmbedding_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

theorem binaryEquiv_action (g : LeechIsometryGroup) (M : RealMatrix)
    (N : Matrix Index Index ℤ)
    (hM : M * basisMatrix = basisMatrix * N.map (Int.castRingHom ℚ))
    (hg : ∀ x : Space, (fullIsometryEquiv g).val (matrixComparison x) =
      matrixComparison (M *ᵥ x)) (v : Index → Bit) :
    leechModTwoRepresentation g (binaryEquiv v) =
      binaryEquiv (N.map (Int.castRingHom Bit) *ᵥ v) := by
  let z : Index → ℤ := fun i => (v i).val
  have hz : (fun i => (z i : Bit)) = v := by ext i; simp [z]
  rw [← hz, binaryEquiv_cast, leechModTwoRepresentation_reduce,
    integralEquiv_action g M N hM hg]
  have hc : (fun i => ((N *ᵥ z) i : Bit)) =
      N.map (Int.castRingHom Bit) *ᵥ (fun i => (z i : Bit)) := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [← hc, binaryEquiv_cast]

def transportedBinary (d : Alignment) : (Index → Bit) ≃ₗ[Bit] LeechModTwo :=
  binaryEquiv.trans (leechModTwoRepresentation d.conjugator)

theorem transportedBinary_action (d : Alignment) (g : matrixGroup)
    (N : Matrix Index Index ℤ)
    (hN : realification g.val.inv.conjTranspose * basisMatrix =
      basisMatrix * N.map (Int.castRingHom ℚ)) (v : Index → Bit) :
    leechModTwoRepresentation (integralHom d g) (transportedBinary d v) =
      transportedBinary d (N.map (Int.castRingHom Bit) *ᵥ v) := by
  change leechModTwoRepresentation (d.conjugator * matrixToLeech g * d.conjugator⁻¹)
    (leechModTwoRepresentation d.conjugator (binaryEquiv v)) = _
  rw [map_mul, map_mul, map_inv]
  change leechModTwoRepresentation d.conjugator
    (leechModTwoRepresentation (matrixToLeech g)
      ((leechModTwoRepresentation d.conjugator).symm
        (leechModTwoRepresentation d.conjugator (binaryEquiv v)))) = _
  rw [LinearEquiv.symm_apply_apply,
    binaryEquiv_action (matrixToLeech g) _ N hN (matrixToLeech_intertwines g)]
  rfl

theorem transportedBinary_generatorA (d : Alignment) (v : Index → Bit) :
    leechModTwoRepresentation (integralHom d matrixGeneratorA) (transportedBinary d v) =
      transportedBinary d (generatorACoordinates.map (Int.castRingHom Bit) *ᵥ v) :=
  transportedBinary_action d matrixGeneratorA generatorACoordinates generatorA_basis v

theorem transportedBinary_generatorB (d : Alignment) (v : Index → Bit) :
    leechModTwoRepresentation (integralHom d matrixGeneratorB) (transportedBinary d v) =
      transportedBinary d (generatorBCoordinates.map (Int.castRingHom Bit) *ᵥ v) :=
  transportedBinary_action d matrixGeneratorB generatorBCoordinates generatorB_basis v

end ReferenceBlock.ModularCoordinates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel

