module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Model
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Golden.Linear
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Cubic

/-!
# Four finite golden constituent certificates

The six column masks use integral-basis bit 4*i.1+i.2. Their order is
re(v₀), im(v₀), re(v₁), im(v₁), re(v₂), im(v₂). Explicit sparse left inverses
certify independence. Kernel-checked identities on those six columns certify
the three quaternion axes, both cubic orientations, and both literal
generators. No rational numerator is evaluated in these certificates.

The discovery data are recorded in Golden/source/four-cases.json; they are
not trusted certificates. Each identity below is checked by Lean.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284,
the natural and dual SL₃(4) constituents. The displayed matrices and integral
comparison retain John Bray and Gerald Höhn's ATLAS attribution and Research
and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation
namespace Golden
open Long.Block Long.Block.Realization

def sixNumber (j : Six) : Fin 6 := ⟨2 * j.1.val + j.2.val, by omega⟩

def masks (inverse opposite : Bool) : Fin 6 → Nat :=
  match inverse, opposite with
  | false, false => ![10485760,6291456,10487296,6294528,6948352,12979200]
  | false, true => ![2031887,12061448,15732720,8390784,2093056,12091392]
  | true, false => ![2031887,10947079,15732720,7341936,2093056,10973184]
  | true, true => ![10485760,12582912,10487296,12585472,6948352,11274752]

def columns (inverse opposite : Bool) : Matrix Index Six Bit :=
  fun i j => if (masks inverse opposite (sixNumber j)).testBit (indexNumber i).val then 1 else 0

def retraction (inverse opposite : Bool) : Matrix Six Index Bit :=
  fun j i => (match inverse, opposite with
    | false, false =>
      ![![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,1,0],![0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,1,0],![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0]]
    | false, true =>
      ![![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0]]
    | true, false =>
      ![![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0]]
    | true, true =>
      ![![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1,0,0],![0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,1,0],![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0]]
    : Matrix (Fin 6) (Fin 24) Bit) (sixNumber j) (indexNumber i)

def twist (inverse opposite : Bool) : SL(3,GoldenFour) ≃* SL(3,GoldenFour) :=
  match inverse, opposite with
  | false, false => MulEquiv.refl _
  | false, true => dualTwist.trans fieldTwist
  | true, false => dualTwist
  | true, true => fieldTwist

theorem left_inverse (inverse opposite : Bool) : retraction inverse opposite * columns inverse opposite = 1 := by
  cases inverse <;> cases opposite <;> decide +kernel

theorem fixed_certificate (inverse opposite : Bool) : ∀ k j, (rightAxisTable k).map (Int.castRingHom Bit) *ᵥ
    embedding (columns inverse opposite) (unitVector j) =
      embedding (columns inverse opposite) (unitVector j) := by
  simp only [embedding_unitVector]
  cases inverse <;> cases opposite <;> decide +kernel

theorem scalar_certificate (inverse opposite : Bool) : ∀ j, embedding (columns inverse opposite) (goldenFourTau • unitVector j) =
    orientationAction opposite (embedding (columns inverse opposite) (unitVector j)) := by
  simp only [embedding_unitVector]
  cases inverse <;> cases opposite <;> decide +kernel

theorem cubic_certificate (inverse opposite : Bool) : ∀ j, (cubicTable inverse).map (Int.castRingHom Bit) *ᵥ
    embedding (columns inverse opposite) (unitVector j) =
      orientationAction opposite (embedding (columns inverse opposite) (unitVector j)) := by
  simp only [embedding_unitVector]
  cases inverse <;> cases opposite <;> decide +kernel

theorem generatorA_certificate (inverse opposite : Bool) : ∀ j, generatorACoordinates.map (Int.castRingHom Bit) *ᵥ
    embedding (columns inverse opposite) (unitVector j) =
      embedding (columns inverse opposite) ((twist inverse opposite threeA).val *ᵥ unitVector j) := by
  simp only [embedding_unitVector]
  cases inverse <;> cases opposite <;> decide +kernel

theorem generatorB_certificate (inverse opposite : Bool) : ∀ j, generatorBCoordinates.map (Int.castRingHom Bit) *ᵥ
    embedding (columns inverse opposite) (unitVector j) =
      embedding (columns inverse opposite) ((twist inverse opposite threeB).val *ᵥ unitVector j) := by
  simp only [embedding_unitVector]
  cases inverse <;> cases opposite <;> decide +kernel

end Golden
end ReferenceBlock.ModularCoordinates.FiniteCalculation
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
