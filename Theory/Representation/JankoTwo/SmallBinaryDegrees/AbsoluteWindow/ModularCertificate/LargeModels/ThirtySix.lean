module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Descent
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.ThirtySix.Certificate

/-!
# The degree-36 characteristic-two Hall--Janko representation

The two ATLAS `J2G1-f2r36B0` matrices satisfy all five relators of J2G1-P2.
The checked rank-one polynomial and its two invertible orbit bases prove full
matrix-algebra density over every characteristic-two field. Descent through the
exact presentation then constructs an absolutely irreducible representation
of the literal degree-100 permutation carrier, in every universe.

The sole group-theoretic input is injectivity of `Presentation.toCarrier`.
No irreducibility or completeness assertion from ATLAS is a proof premise.
Original matrices, attribution and untrusted discovery records are preserved
in `LargeModels/source/`; see also `ModularCertificate/Source.md`.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.ThirtySix
open Sporadic.LeechRelated.J2
open G2FourModule.Embedding.InnerRealization
universe v

variable (hp : Function.Injective Presentation.toCarrier)
variable (F : Type*) [Field F] [CharP F 2]

/-- The actual degree-36 action of the degree-100 Hall--Janko carrier. -/
def representation : Representation F Carrier (Fin 36 → F) :=
  action hp (unitA F) (unitB F) (relations F)

/-- The rank-one and orbit identities give absolute irreducibility. -/
theorem absolutelyIrreducible : IsAbsolutelyIrreducible (representation hp F) :=
  action_absolutelyIrreducible_of_rankOne hp (unitA F) (unitB F) (relations F)
    (column F) (row F) (Binary.eval F 36 pData) (Binary.eval F 36 piData)
    (Binary.eval F 36 qData) (Binary.eval F 36 qiData)
    (rankOne_mem F) (left_basis F) (right_basis F) (left_inverse F) (right_inverse F)

/-- The first generator is the literal ATLAS binary matrix. -/
theorem representation_a : representation hp F GeneratorPair.a =
    Matrix.toLin' (generatorA F) := action_a hp (unitA F) (unitB F) (relations F)

/-- The second generator is the literal ATLAS binary matrix. -/
theorem representation_b : representation hp F GeneratorPair.b =
    Matrix.toLin' (generatorB F) := action_b hp (unitA F) (unitB F) (relations F)

/-- The degree-36 member of the modular saturation family, in every universe. -/
theorem modelsExist (hp : Function.Injective Presentation.toCarrier) : ModelsExist.{v} (fun _ : Fin 1 => 36) := by
  intro K _ _ _
  refine ⟨fun _ => representation hp K, ?_, ?_⟩
  · intro i
    let := absolutelyIrreducible hp K
    exact IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.ThirtySix
