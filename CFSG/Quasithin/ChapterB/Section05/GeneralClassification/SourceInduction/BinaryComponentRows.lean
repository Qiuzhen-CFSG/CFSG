module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.SL2.NoLinearThreeEmbedding
/-!
# Native B.5 rows selected by a binary rank-one component

A normal source factor containing a component modeled by binary SL₂ cannot
be an SL₃ factor: its quasisimplicity would identify the component with the
factor, contradicting the concrete two-subgroup exponent calculation.
This excludes the natural, repeated and exceptional SL₃ rows while retaining
the literal moved-space equality and quotient-image intertwiner. The same
argument excludes the hyperplane row when all actual components are binary
rank one. No minimal-parabolic hypothesis is introduced.

Source: Aschbacher–Smith B.5.6(3),(5), printed p.105, applied in 13.6.14,
printed p.929. Factor placement is an explicit group-theoretic input here.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V E : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [Field E] [Finite E] [CharP E 2]
  {ρ : Representation (ZMod 2) D V} {A C : Subgroup D} {U : Subrepresentation ρ}

private theorem component_in_linearThree_not_binaryTwo [A.Normal]
    (hC : IsComponent D C) (hCA : C ≤ A)
    (eC : C ≃* SL(2,E)) (F : BinaryField) (eA : A ≃* SL(3,F.Carrier)) : False := by
  let : IsQuasisimple SL(3,F.Carrier) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  have hA : IsComponent D A :=
    ⟨(inferInstance : A.Normal).isSubnormal, IsQuasisimple.of_mulEquiv eA.symm⟩
  have he := hC.eq_of_le hA hCA
  let e := eA.symm.trans ((MulEquiv.subgroupCongr he).symm.trans eC)
  exact Matrix.SpecialLinearGroup.not_injective_linearThree_to_binaryLinearTwo
    e.toMonoidHom e.injective

/-- The same specified quotient summand is a natural SL₂ or symmetric-five module. -/
theorem SourceFactorCase.rankOne_of_binary_component [A.Normal]
    (h : SourceFactorCase ρ A U) (hC : IsComponent D C) (hCA : C ≤ A)
    (eC : C ≃* SL(2,E)) :
    U.toSubmodule = moved ρ A ∧
      ((∃ F : BinaryField, IsLinearNatural
        (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) F 2) ∨
       IsSymmetricNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) 5) := by
  have hexcl := component_in_linearThree_not_binaryTwo hC hCA eC
  cases h with
  | natural hm hn =>
    cases hn with
    | linearTwo F he => exact ⟨hm,Or.inl ⟨F,he⟩⟩
    | symmetricFive he => exact ⟨hm,Or.inr he⟩
    | linearThree F _ he => obtain ⟨e⟩ := he; exact (hexcl F e.groupEquiv).elim
  | doubleNatural F _ _ he => obtain ⟨e⟩ := he; exact (hexcl F e.groupEquiv).elim
  | exceptional _ c => exact (hexcl BinaryField.two c.natural.groupEquiv).elim

/-- Binary rank-one components exclude the actual SL₃ factor in the hyperplane row. -/
theorem HyperplaneCase.not_of_binary_components (c : HyperplaneCase ρ)
    (hmodels : ∀ C : Subgroup D, IsComponent D C →
      ∃ F : BinaryField, Nonempty (C ≃* SL(2,F.Carrier))) : False := by
  let : c.first.Normal := c.product.swap.second_normal
  let : IsQuasisimple SL(3,ZMod 2) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  have hC : IsComponent D c.first :=
    ⟨(inferInstance : c.first.Normal).isSubnormal,IsQuasisimple.of_mulEquiv c.firstEquiv.symm⟩
  obtain ⟨F,⟨e⟩⟩ := hmodels c.first hC
  exact Matrix.SpecialLinearGroup.not_injective_linearThree_to_binaryLinearTwo
    (e.toMonoidHom.comp c.firstEquiv.symm.toMonoidHom) (e.injective.comp c.firstEquiv.symm.injective)

end CFSG.Quasithin.ChapterB.SourceInduction
