module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Maximality
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Separation

/-!
# The opposite Borel big cell on the concrete F4 carrier

The original standard positive roots generate the unipotent radical of the
positive Borel, and their negatives generate that of the opposite Borel.
`Maximality` proves that the literal torus/root candidates are maximal connected
solvable subgroups. `Separation` proves that their intersection is the fixed
split torus, and `ProductDensity` proves that their product is dense and open.
Here these results discharge every premise of the existing big-cell assembly.

The witnesses use exactly `RootModel.Corrected.rootSystemModel`, its torus and
its positive system. Thus they can be supplied directly to highest-weight and
Steinberg geometry. No root labels, representation weights or coroot parameters
are changed: the raw cocharacters retain the inverse-parameter convention.

Sources: the prescribed-positive-system and opposite-pair cases of GLS3,
Theorems 1.11.2 and 1.11.4 (`refs/KGroup/GLS3/Chapter1.tex`), and the Borel
and open-product conclusions of Steinberg (6.2)
(`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped Pointwise

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels

open RootModel.Corrected
universe u
variable (F : Type u) [Field F] [IsAlgClosed F] [CharP F 2]

/-- The opposite big cell for the literal F4 torus and corrected root datum,
with all maximality, radical, separation and density obligations discharged. -/
def bigCell :
    OppositeBorelBigCell (rootSystemModel (F := F)).torus
      (rootSystemModel (F := F)).rootData (rootSystemModel (F := F)).rootData.positive :=
  bigCellOfMaximalityAndSeparation F (positiveCandidate_isBorel F)
    (negativeCandidate_isBorel F) (opposite_disjoint F)

/-- Compatible Borels for the same torus and the original standard positive system. -/
def borelOppositeData :
    RealizedRootBorelOppositeData (rootSystemModel (F := F)).torus
      (rootSystemModel (F := F)).rootData (positiveRoots F) :=
  (bigCell F).data

/-- The positive Borel/root witness, including its actual unipotent radical. -/
def positiveBorelWitness :
    IsBorelOfPositiveSystem (rootSystemModel (F := F)).rootData
      (positiveRoots F) (positiveCandidate F) :=
  (bigCell F).data.positive_witness

/-- The opposite Borel/root witness for the negatives of the same labelled roots. -/
def negativeBorelWitness :
    IsBorelOfPositiveSystem (rootSystemModel (F := F)).rootData
      (negativeRoots F) (negativeCandidate F) :=
  (bigCell F).data.opposite_witness

/-- The assembled positive Borel is the published literal candidate. -/
@[simp] theorem bigCell_positive : (bigCell F).data.B = positiveCandidate F := rfl

/-- The assembled opposite Borel is the published literal candidate. -/
@[simp] theorem bigCell_negative : (bigCell F).data.Bopp = negativeCandidate F := rfl

/-- The positive witness has exactly the literal positive root-generated radical. -/
@[simp] theorem positiveBorelWitness_unipotent :
    (positiveBorelWitness F).unipotent = positiveUnipotent F := rfl

/-- The opposite witness has exactly the literal negative root-generated radical. -/
@[simp] theorem negativeBorelWitness_unipotent :
    (negativeBorelWitness F).unipotent = negativeUnipotent F := rfl

/-- The positive Borel decomposes using the same torus and labelled positive roots. -/
theorem positive_decomposition (x : Variety.Point (F4Chevalley.Carrier (k := F))) :
    x ∈ (bigCell F).data.B ↔ ∃ t u,
      t ∈ F4Chevalley.splitTorus ∧
      u ∈ RootSubgroupGenerated (rootSystemModel (F := F)).rootData (positiveRoots F) ∧
      x = t * u :=
  (bigCell F).positive_decomposition x

/-- The opposite Borel decomposes using the negatives of the original positive roots. -/
theorem negative_decomposition (x : Variety.Point (F4Chevalley.Carrier (k := F))) :
    x ∈ (bigCell F).data.Bopp ↔ ∃ t u,
      t ∈ F4Chevalley.splitTorus ∧
      u ∈ RootSubgroupGenerated (rootSystemModel (F := F)).rootData (negativeRoots F) ∧
      x = t * u :=
  (bigCell F).negative_decomposition x

/-- The assembled big cell is open on the actual F4 carrier. -/
theorem bigCell_product_open :
    IsOpen (((bigCell F).data.B.toSubgroup : Set (Variety.Point (F4Chevalley.Carrier (k := F)))) *
      ((bigCell F).data.Bopp.toSubgroup : Set (Variety.Point (F4Chevalley.Carrier (k := F))))) :=
  candidates_product_open F

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
