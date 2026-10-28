module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Source
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient

/-!
# Strong-offender exclusion on the actual paired symmetric-five source

Strong replacement gives a best offender in the genuine offender layer.
Its literal subgroup-of action has the same fixed codimension on the marked
natural pair, where the product estimate excludes strong offending.
Thus no additional whole-ambient action comparison is needed.

Source: Aschbacher--Smith B.2.18(c), B.6.9--10 and E.2.3(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.SourceInduction.SourceTwoFactorCase.MarkedProduct
open BinaryPermutation
variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem symmetric_not_strong
    (α : Representation (ZMod 2) H V)
    (d : SourceTwoFactorCase (α.comp (offenderSubgroup α).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5))) : ¬ IsStrongFFModule α := by
  rintro ⟨A,hA⟩
  obtain ⟨B,_,hB,hBs⟩ := hA.exists_bestOffender α
  have hBY : B ≤ offenderSubgroup α := hB.le_offenderSubgroup α
  let C := B.subgroupOf (offenderSubgroup α)
  have hs : IsOffender (α.comp (offenderSubgroup α).subtype) C :=
    (show IsOffender α B from ⟨hBs.1,hBs.2.le⟩).subgroupOf α hBY
  let : IsElementaryAbelian 2 C := hs.1.2
  apply ChapterC.SymmetricFive.Paired.not_strong ⟨C.map c.action.groupEquiv.toMonoidHom,?_,?_⟩
  · exact ⟨fun hz => hs.1.1 ((map_eq_bot_iff_of_injective C c.action.groupEquiv.injective).mp hz),
      IsElementaryAbelian.map _⟩
  · rw [rank_map_injective _ c.action.groupEquiv.injective,←c.symmetric_fixedCodim,
      fixedCodim_subgroupOf α hBY,rank_subgroupOf hBY]
    exact hBs.2
end CFSG.Quasithin.ChapterB.SourceInduction.SourceTwoFactorCase.MarkedProduct
