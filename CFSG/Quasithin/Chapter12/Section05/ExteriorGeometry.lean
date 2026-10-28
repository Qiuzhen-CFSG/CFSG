module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry

/-!
# Intrinsic exterior-module steps in 12.5.7 and 12.5.10

The lower-layer geometry proves Lemmas 12.5.2 and 12.5.5 for the actual
SL₅(2) exterior square. Here its fixed-space calculations are applied to the
literal source radical R₆ = O₂(L₆T). An elementary A₃ subgroup of the standard
flag group is R₆, has fixed and commutator space V₆, and its subgroups of
quotient rank at most three have fixed spaces spanning V. For A₂, excluding
the two commutator-line alternatives puts A in R₆ and makes it fix V₆.

In the book, E.3.10 supplies A₃/A₂ membership, and 12.5.9(4) excludes the
commutator-line alternatives in 12.5.10. Those ambient premises remain explicit
here. The §12.5 owner must identify its source representation with an exterior
model, provide those inputs, and complete the fusion/elimination argument.
These theorems establish the intrinsic module steps, not the full 12.5.7/10.

Reference: Aschbacher–Smith, printed pp.820–821/PDF pp.837–838. The strict
inequality in E.3.8 differs from the bound ≤ 3 in fixed-space generation.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section05.ExteriorGeometry
open Representation Representation.SL5TenDimensional Representation.SL5ExteriorSquare

/-- The complete module calculation used after E.3.10 in 12.5.7. -/
theorem smallIndex_three_module_geometry (A : Subgroup Group)
    [IsElementaryAbelian 2 A] (hflag : A ≤ flagGroup) (hne : A ≠ ⊥)
    (hsmall : HasSmallIndexFixedSpaceProperty 3 A) :
    A = parabolicResidualTwoCore 4 ∧
      BinaryOffender.fixedSpace (exteriorAction 2) A = V₆ ∧
      BinaryOffender.subspaceCommutator (exteriorAction 2) ⊤ A = V₆ ∧
      (⨆ (B : Subgroup Group) (_ : B ≤ A) (_ : Nat.log 2 (B.relIndex A) ≤ 3),
        BinaryOffender.fixedSpace (exteriorAction 2) B) = ⊤ := by
  have he := (flag_elementaryTwo_smallIndex_three_iff_radicalSix hflag).mp
    ⟨⟨hne, inferInstance⟩, hsmall⟩
  refine ⟨he, ?_, ?_, iSup_fixedSpace_subgroups_of_flag_smallIndex_three hflag hne hsmall⟩
  · rw [he]
    exact radicalSix_fixedSpace_and_commutator.1
  · rw [he]
    exact radicalSix_fixedSpace_and_commutator.2

/-- The module calculation in 12.5.10 after its two 12.5.9(4) exclusions. -/
theorem smallIndex_two_module_containment (A : Subgroup Group)
    [IsElementaryAbelian 2 A] (hflag : A ≤ flagGroup)
    (hsmall : HasSmallIndexFixedSpaceProperty 2 A)
    (h₃ : ¬ V₁ ≤ BinaryOffender.subspaceCommutator (exteriorAction 2) V₃ A)
    (h₃' : ¬ V₁ ≤ BinaryOffender.subspaceCommutator (exteriorAction 2) V₃' A) :
    A ≤ parabolicResidualTwoCore 4 ∧
      V₆ ≤ BinaryOffender.fixedSpace (exteriorAction 2) A := by
  have hle : A ≤ parabolicResidualTwoCore 4 := by
    rcases le_radicalSix_or_commutator_of_flag_smallIndex_two hflag hsmall with h | h | h
    · exact h
    · exact (h₃ h).elim
    · exact (h₃' h).elim
  refine ⟨hle, ?_⟩
  rw [← radicalSix_fixedSpace_and_commutator.1]
  intro v hv a
  exact hv ⟨a.val, hle a.property⟩

end CFSG.Quasithin.Chapter12.Section05.ExteriorGeometry
