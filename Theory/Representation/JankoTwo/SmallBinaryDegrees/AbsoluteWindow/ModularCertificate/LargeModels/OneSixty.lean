module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Polynomial
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Orbits
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary160Basis
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary160Application
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation

/-!
# The degree-160 characteristic-two Hall--Janko representation

The literal ATLAS J2G1-f2r160B0 generators satisfy the five presentation
relations. Their generated algebra contains a checked rank-one polynomial;
the recorded left and right translates are invertible bases. Thus this algebra
is the full matrix algebra, and the descended action is absolutely irreducible
over every characteristic-two field in every universe.

Descent is to the original degree-100 permutation carrier. The sole external
input is injectivity of the already constructed presentation-to-carrier map.
The shared checked left inverse is consumed unchanged through
`Binary160Basis.action_absolutelyIrreducible`. ATLAS attribution, certificate
conventions and performance measurements are in `OneSixty/source/README.md`.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
open Sporadic.LeechRelated.J2
open G2FourModule.Embedding.InnerRealization
universe v

variable (F : Type*) [Field F] [CharP F 2]

/-- The actual degree-160 action of the original Hall--Janko carrier. -/
def representation (hp : Function.Injective Presentation.toCarrier) :
    Representation F Carrier (Fin 160 → F) :=
  action hp (unitA F) (unitB F) (units_relations F)

/-- The first marked carrier generator acts by the literal ATLAS matrix. -/
theorem representation_a (hp : Function.Injective Presentation.toCarrier) :
    representation F hp GeneratorPair.a = Matrix.toLin' (matrixA F) :=
  action_a hp (unitA F) (unitB F) (units_relations F)

/-- The second marked carrier generator acts by the literal ATLAS matrix. -/
theorem representation_b (hp : Function.Injective Presentation.toCarrier) :
    representation F hp GeneratorPair.b = Matrix.toLin' (matrixB F) :=
  action_b hp (unitA F) (unitB F) (units_relations F)

theorem representation_absolutelyIrreducible (hp : Function.Injective Presentation.toCarrier) :
    IsAbsolutelyIrreducible (representation F hp) := by
  apply Binary160Basis.action_absolutelyIrreducible hp (unitA F) (unitB F) (units_relations F)
    (vector F 160 Data.column) (vector F 160 Data.covector)
    (Binary.eval F 160 Data.rightBasis) (Binary.eval F 160 Data.rightInverse)
    (rankOne_mem F)
  · intro i
    refine ⟨wordValue (matrixA F) (matrixB F) Data.leftWords[i.val]!.reverse, ?_,
      left_orbit_identity F i⟩
    apply wordValue_mem
    · exact Algebra.subset_adjoin (by simp [unitA])
    · exact Algebra.subset_adjoin (by simp [unitB])
  · intro i
    refine ⟨wordValue (matrixA F) (matrixB F) Data.rightWords[i.val]!, ?_,
      right_orbit_identity F i⟩
    apply wordValue_mem
    · exact Algebra.subset_adjoin (by simp [unitA])
    · exact Algebra.subset_adjoin (by simp [unitB])
  · exact right_inverse_mul_basis F

/-- The degree-160 family required for modular saturation, with all numerical
and irreducibility obligations discharged. -/
theorem modelsExist (hp : Function.Injective Presentation.toCarrier) :
    ModelsExist.{v} (fun _ : Fin 1 => 160) := by
  intro K _ _ _
  refine ⟨fun _ => representation K hp, ?_, ?_⟩
  · intro i
    let : IsAbsolutelyIrreducible (representation K hp) :=
      representation_absolutelyIrreducible K hp
    exact IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
