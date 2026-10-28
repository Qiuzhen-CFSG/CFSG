module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.ModelSeparation
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# PSL₃(4) is not PSL₄(2)

The existing A₈--PSL₃(4) separation compares centers of actual Sylow
2-subgroups. Transport the binary field and use the proved A₈--PSL₄(2)
equivalence to obtain the model-predicate version needed by A.3.12(5),(17).
No conclusion is inferred from equal group orders.

Source: Aschbacher--Smith, A.3.12, printed pp.47--48, used on p.1136.
The underlying ATLAS adaptation and its license are recorded in the
imported ModelSeparation module.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization

/-- These two model predicates are incompatible over any coefficient fields. -/
theorem no_binary_four {X : Type*} [Group X]
    (hX : ClassicalGroup.IsPSL X 3 4) : ¬ ClassicalGroup.IsPSL X 4 2 := by
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hX
  rintro ⟨E, _, _, hE, ⟨eE⟩⟩
  let := Fintype.ofFinite E
  let e : E ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hE]
    simp)
  let b := eE.trans (Atlas.fieldEquivPSL 4 e)
  exact CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.ModelSeparation.alt8_not_equiv_psl3Card4
    hF ⟨Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans (b.symm.trans eF)⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
