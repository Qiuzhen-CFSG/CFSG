module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.E7Block.Exponentiation

/-!
# The concrete E7 block carrying the checked E6 cubic

The 27 displayed roots define an injective linear inclusion into the literal E7
Chevalley representation. Both signs of each of the first six simple generators
act by the transvections of `CubicModel`, and every evaluated word intertwines
this inclusion. The residue diagonal acts on the block by the inverse scalar.

Root membership, distinctness, the complete root-step columns and the central
exponents are proved in the descendants of this module. Higher divided powers
vanish by cancellation over ℤ before specialization, so every result includes
characteristic three. This discharges the concrete block premises of
`e7Six_residue_cube_of_block` and `e8Six_residue_cube_of_e7_block`; the parent
cubic module owns their application to the unconditional residue constraints.

Sources: GLS3 §§1.12.5–6 and §2.6.2 (the common Chevalley lattice), used for the
exceptional inclusions in Aschbacher–Smith A.2.17, printed p.39.
-/

public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _

/-- The actual block, with both literal identities and no representation hypothesis. -/
theorem exists_block (F : Type*) [Field F] :
    ∃ J₀ : (Fin 27 → F) →ₗ[F] ((typeE7RootPairing_base.support ⊕ typeE7Roots) → F),
      Function.Injective J₀ ∧
      (∀ (s : Bool) (i : Fin 6) (t : F) (x : Fin 27 → F),
        (e7Simple F s (i.castLE (by decide)) t).val.val *ᵥ J₀ x =
          J₀ (CubicModel.curve s i t x)) ∧
      (∀ (u : Fˣ) (x : Fin 27 → F),
        (residueDiagonal F e7Node u).val *ᵥ J₀ x = J₀ ((u⁻¹ : Fˣ).val • x)) :=
  ⟨J F, J_injective F, simple_J F, residueDiagonal_J F⟩

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
