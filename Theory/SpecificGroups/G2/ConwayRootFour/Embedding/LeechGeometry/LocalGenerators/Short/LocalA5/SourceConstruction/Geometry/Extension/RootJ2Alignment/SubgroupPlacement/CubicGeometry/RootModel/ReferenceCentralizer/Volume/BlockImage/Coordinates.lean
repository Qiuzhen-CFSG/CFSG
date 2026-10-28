module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient

/-!
# Two-generator coordinates for the transported block

A coordinate comparison gives a linear equivalence from F₄³ to the actual
reference eigenspace and identifies the two explicit Eisenstein generators.
An automorphism of SL₃(4) permits the field and contragredient conventions.
Subgroup generation extends these two equations to every block element and
the equivalence establishes dimension three without using trivial padding.

The coordinate comparison remains an explicit input; this module does not
assert its existence. The assembly in BlockImage applies the resulting
equivariance to the already proved matrixQuotient surjectivity.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284.
The explicit generators and quotient are the attributed John Bray ATLAS block.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long


namespace ReferenceBlock

/-- The two literal block generators generate the actual subgroup carrier. -/
theorem generators_generate :
    Subgroup.closure {Long.Block.matrixGeneratorA, Long.Block.matrixGeneratorB} = ⊤ := by
  have hs : ({Long.Block.matrixGeneratorA, Long.Block.matrixGeneratorB} :
      Set Long.Block.matrixGroup) = Long.Block.matrixGroup.subtype ⁻¹'
        {Long.Block.generatorA, Long.Block.generatorB} := by
    ext g
    change (g = Long.Block.matrixGeneratorA ∨ g = Long.Block.matrixGeneratorB) ↔
      (g.val = Long.Block.generatorA ∨ g.val = Long.Block.generatorB)
    exact ⟨fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val),
      fun h => h.imp Subtype.ext Subtype.ext⟩
  rw [hs]
  exact Subgroup.closure_preimage_eq_top _

/-- Coordinate evidence consists of actual vectors and the actions of the two
integral generators. The automorphism permits the dual and field conventions. -/
structure Coordinates (d : Alignment) where
  equiv : (Fin 3 → F) ≃ₗ[F] ReferenceNatural
  twist : SL(3,F) ≃* SL(3,F)
  generatorA : ∀ v,
    referenceEigenAction referenceScalar (toReference d Long.Block.matrixGeneratorA) (equiv v) =
      equiv ((twist (Long.Block.matrixQuotient Long.Block.matrixGeneratorA)).val *ᵥ v)
  generatorB : ∀ v,
    referenceEigenAction referenceScalar (toReference d Long.Block.matrixGeneratorB) (equiv v) =
      equiv ((twist (Long.Block.matrixQuotient Long.Block.matrixGeneratorB)).val *ᵥ v)

/-- The two generator equations determine the action of every integral block element. -/
theorem Coordinates.intertwines {d : Alignment} (c : Coordinates d)
    (g : Long.Block.matrixGroup) (v : Fin 3 → F) :
    referenceEigenAction referenceScalar (toReference d g) (c.equiv v) =
      c.equiv ((c.twist (Long.Block.matrixQuotient g)).val *ᵥ v) := by
  let lhs : Long.Block.matrixGroup →* (ReferenceNatural ≃ₗ[F] ReferenceNatural) :=
    (referenceEigenAction referenceScalar).comp (toReference d)
  let rhs : Long.Block.matrixGroup →* (ReferenceNatural ≃ₗ[F] ReferenceNatural) :=
    (Atlas.LinearAlgebra.linearAutomorphismCongr c.equiv).toMonoidHom.comp
      (SpecialLinearGroup.toLin'.comp (c.twist.toMonoidHom.comp Long.Block.matrixQuotient))
  have hg : lhs = rhs := by
    apply MonoidHom.eq_of_eqOn_dense generators_generate
    rintro _ (rfl | rfl)
    · apply LinearEquiv.ext
      intro w
      obtain ⟨v, rfl⟩ := c.equiv.surjective w
      simpa only [lhs, rhs, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        Atlas.LinearAlgebra.linearAutomorphismCongr_apply,
        LinearEquiv.symm_apply_apply, SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply] using c.generatorA v
    · apply LinearEquiv.ext
      intro w
      obtain ⟨v, rfl⟩ := c.equiv.surjective w
      simpa only [lhs, rhs, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        Atlas.LinearAlgebra.linearAutomorphismCongr_apply,
        LinearEquiv.symm_apply_apply, SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply] using c.generatorB v
  have hh := DFunLike.congr_fun (DFunLike.congr_fun hg g) (c.equiv v)
  simpa only [lhs, rhs, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Atlas.LinearAlgebra.linearAutomorphismCongr_apply,
    LinearEquiv.symm_apply_apply, SpecialLinearGroup.toLin'_apply,
    Matrix.toLin'_apply] using hh

/-- The coordinate comparison identifies the actual eigenspace dimension. -/
theorem Coordinates.finrank {d : Alignment} (c : Coordinates d) :
    Module.finrank F ReferenceNatural = 3 := by
  rw [← c.equiv.finrank_eq]
  simp


end ReferenceBlock
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
