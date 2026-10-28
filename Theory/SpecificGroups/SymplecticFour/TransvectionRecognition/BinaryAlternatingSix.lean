module

public import Theory.Representation.BinaryAlternatingSixModels.ScalarFour
public import Theory.SpecificGroups.SymplecticFour.Flag

/-!
# The literal A₆ four-space in a symplectic subgroup

The abstract actor identification is pulled back along the actual inclusion
of the subgroup in the ambient symplectic four-space. The arbitrary-field
A₆ catalogue then returns a linear equivalence to the coefficient extension
of a binary natural model, intertwining the same subgroup elements and the
specified identification. The two alternatives retain the exceptional
S₆ diagram twist. The simple carrier is A₆; adjoining a normalizer and the
symplectic change of form remain with the recognition assembly.
Source: Aschbacher–Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
open Representation
open scoped TensorProduct
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- An irreducible actual A₆ subgroup has binary natural coordinates over F,
with its literal subgroup inclusion and given actor identification. -/
theorem exists_alternatingSix_intertwiner (N : Subgroup (Sp F))
    (e : N ≃* alternatingGroup (Fin 6))
    (hi : IsIrreducible ((symplecticNatural 2).comp N.subtype)) :
    ∃ A : Vector F ≃ₗ[F] F ⊗[ZMod 2] Theory.SpecificGroups.SymmetricSix.NaturalModule,
      (∀ n : N, ∀ v, A ((n : Sp F) • v) =
        extendScalars F BinaryAlternatingSix.firstAlternating (e n) (A v)) ∨
      (∀ n : N, ∀ v, A ((n : Sp F) • v) =
        extendScalars F BinaryAlternatingSix.secondAlternating (e n) (A v)) := by
  let ρ : Representation F N (Vector F) := (symplecticNatural 2).comp N.subtype
  let : ρ.IsIrreducible := hi
  exact BinaryAlternatingSix.ScalarFour.exists_intertwiner ρ e (by
    simp [Vector])

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
