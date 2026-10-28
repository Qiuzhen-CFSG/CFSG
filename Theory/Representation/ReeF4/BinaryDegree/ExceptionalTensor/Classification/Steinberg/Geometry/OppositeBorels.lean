module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Unipotence
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.ProductDensity
public import Theory.AlgebraicGroup.Borel.OppositeBigCell

/-!
# The conditional assembly boundary for the F4 opposite big cell

The literal signed candidates are closed, connected and solvable, with their
root-generated groups as unipotent radicals. Their product is dense and open.
The construction below connects these results to the exact `OppositeBorelBigCell`
consumed by highest-weight geometry, retaining the corrected model and its
original positive roots.

Two independent geometric steps are explicit in this reusable assembly:
maximal connected solvability of both candidates, and separation of the positive
unipotent group from the negative candidate. `OppositeBorels.Assembly` supplies
both proved certifications and exports the unconditional F4 big cell.

Sources: GLS3 1.11.2 and 1.11.4 (`refs/KGroup/GLS3/Chapter1.tex`), and
Steinberg (6.2)(c) (`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
open RootModel.Corrected
universe u
variable (F : Type u) [Field F] [IsAlgClosed F] [CharP F 2]

/-- Assemble the exact F4 big cell once maximality and opposite separation
are certified. All other geometric fields are proved by the imported modules. -/
def bigCellOfMaximalityAndSeparation
    (hpos : IsBorelSubgroup (positiveCandidate F))
    (hneg : IsBorelSubgroup (negativeCandidate F))
    (hsep : Disjoint (positiveUnipotent F).toSubgroup (negativeCandidate F).toSubgroup) :
    OppositeBorelBigCell (rootSystemModel (F := F)).torus
      (rootSystemModel (F := F)).rootData (rootSystemModel (F := F)).rootData.positive where
  data := {
    positive := rootSystemModel_isPositiveSystem
    B := positiveCandidate F
    Bopp := negativeCandidate F
    B_isBorel := hpos
    Bopp_isBorel := hneg
    positive_witness := {
      unipotent := positiveUnipotent F
      root_generated := rootGenerated_toSubgroup F (positiveRoots F)
      borel := hpos
      radical := positiveCandidate_unipotentRadical
      torus_unipotent_generate := torusRootGenerated_toSubgroup F (positiveRoots F) }
    opposite_witness := {
      unipotent := negativeUnipotent F
      root_generated := rootGenerated_toSubgroup F (negativeRoots F)
      borel := hneg
      radical := negativeCandidate_unipotentRadical
      torus_unipotent_generate := torusRootGenerated_toSubgroup F (negativeRoots F) } }
  intersection_eq_torus := intersection_eq_torus_of_disjoint F hsep
  product_dense := candidates_product_dense F

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
