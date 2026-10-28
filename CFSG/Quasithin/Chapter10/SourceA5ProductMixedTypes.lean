module
public import CFSG.Quasithin.Chapter10.SourceA5ProductTypeAlternatives
public import Theory.Representation.AlternatingFiveMovedPair.MixedTypes
/-!
# Fixed mixed markings in the moved A₅ product alternatives

The mixed cases of the original D.3.5 constituent classification use an
arbitrary SL₂(4) identification. The two S₅ extensions absorb that choice,
so both mixed alternatives use one specified baseline for the two factors.
The targets are the exact summands of the moved mixed-pair displacement model.
No constituent exchange is assumed here.

Source: Aschbacher–Smith D.3.5, printed pp.195–196.
-/
public section
open Representation Representation.QuadraticFourGroup.TensorClassification
open BinaryPermutation.FiveTensorSquare
namespace CFSG.Quasithin.Chapter10
open Representation.AlternatingFiveMovedPair

/-- Both mixed orientations have literal model markings under one selected
baseline. Cubic freeness and the deleted-square alternative are retained. -/
theorem source_a5_product_module_alternatives_fixed_mixed_marking
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (Alt × Alt) U) [ρ.IsIrreducible]
    (hleft : ∃ g, ρ (g,1) ≠ 1) (hright : ∃ g, ρ (1,g) ≠ 1)
    (base : Alt ≃* SL2FourNatural.SL) :
    CubicFreeOnFactors ρ ∨
    Nonempty (Representation.Equiv ρ
      (MixedTypes.secondSL.comp (base.prodCongr base).toMonoidHom)) ∨
    Nonempty (Representation.Equiv ρ
      (MixedTypes.firstSL.comp (base.prodCongr base).toMonoidHom)) ∨
    Nonempty (ρ.Equiv deletedAction) := by
  rcases source_a5_product_module_alternatives_without_exchange ρ hleft hright with
    hfree | hdn | hnd | hdd
  · exact Or.inl hfree
  · obtain ⟨f,⟨e⟩⟩ := hdn
    obtain ⟨b⟩ := MixedTypes.deleted_natural_marked_model f base
    exact Or.inr (Or.inl ⟨e.trans b⟩)
  · obtain ⟨f,⟨e⟩⟩ := hnd
    obtain ⟨b⟩ := MixedTypes.natural_deleted_marked_model f base
    exact Or.inr (Or.inr (Or.inl ⟨e.trans b⟩))
  · exact Or.inr (Or.inr (Or.inr hdd))
end CFSG.Quasithin.Chapter10
