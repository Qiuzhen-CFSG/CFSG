module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.BlockData
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.ClassicalModel.Generation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.ClassicalModel.Canonical

/-!
# The literal Suz 27-pair image is PΩ⁻₆(2)

The pair labels are all the nonzero singular vectors of a six-dimensional
binary quadratic space. The exact block permutations lift to two quadratic
isometries, and this action is faithful because the labelled points include
a basis. A certified stabilizer chain and four word relations identify their
generated subgroup with the full orthogonal group's commutator subgroup.
An explicit Witt basis then transports this group to the canonical minus
model; over the binary field the scalar quotient is trivial.

`blockEquivPOmegaMinus` is an unconditional multiplicative equivalence of the
literal `BlockGroup`. The centralizer-section assembly can supply it directly
to `CFSG.Quasithin.ChapterA.SuzCentralizerSection.quotientDataOfEquiv`.
No ambient Suz simplicity, recognition, order or generation premise is used.

Source: Aschbacher--Smith A.2.19, printed pp.40--41; GLS3 Table 5.3o and
section 2.7. This is the commutator/scalar quotient, not the full isometry group.
See `ClassicalModel/source/README.md` for coordinate and word provenance.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection

/-- The concrete action on the 27 pairs is the canonical minus projective
orthogonal group, with no additional hypothesis. -/
noncomputable def blockEquivPOmegaMinus :
    BlockGroup ≃* ClassicalGroup.POmegaMinus 3 (ZMod 2) :=
  ClassicalModel.generatedBlockEquiv.symm.trans
    ((MulEquiv.subgroupCongr ClassicalModel.generated_eq_commutator).trans
      ClassicalModel.omegaProjectiveEquiv)

end Sporadic.LeechRelated.Suz.CentralizerSection
