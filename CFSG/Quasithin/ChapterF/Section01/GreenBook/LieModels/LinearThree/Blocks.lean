module

public import Theory.SpecificGroups.PSL3.LinearThreeLocalStructure
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2Affine

/-!
# Natural blocks in the degree-three projective local groups

For |F| = 2ⁿ with n > 1, the actual `pointLocal F` and `lineLocal F`
are L₂(2ⁿ)-blocks in the intrinsic convention of C.1.7. Their affine
coordinates give the root-plane commutator layers, trivial fixed layers,
and irreducible natural conjugation modules. The quotient identifications
are the same marked maps as in `LinearThreeLocalCores`.

The affine structure theorems discharge perfectness and F*(L) = O₂(L),
so the final constructors have only the finite-field cardinality hypotheses.
Characteristic two is recovered from that cardinality, and the trivial
center of SL₂ in characteristic two supplies the projective quotient model.
No normality in the ambient PSL₃ is asserted.

Source: Aschbacher–Smith, C.1.7 and C.1.12, printed pp.123–124, and the
nonbinary local-block clause of F.1.12(I)(1), printed pp.262–264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree

open Matrix.PSL3.LinearThree ChapterC

section CharacteristicTwo
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The source U(L) is precisely the point root plane. -/
theorem pointLocal_blockU_eq : blockU (pointLocal F) = pointRadical F := by
  rw [SL2Affine.blockU_eq_core (pointLocalEquivAffine F), pointLocal_twoCore_eq]

/-- The source U(L) is precisely the line root plane. -/
theorem lineLocal_blockU_eq : blockU (lineLocal F) = lineRadical F := by
  rw [SL2Affine.blockU_eq_core (lineLocalEquivAffine F), lineLocal_twoCore_eq]

theorem pointLocal_blockFixed_eq_bot : blockFixed (pointLocal F) = ⊥ :=
  SL2Affine.fixed_eq_bot (pointLocalEquivAffine F)

theorem lineLocal_blockFixed_eq_bot : blockFixed (lineLocal F) = ⊥ :=
  SL2Affine.fixed_eq_bot (lineLocalEquivAffine F)

/-- The actual point-local conjugation quotient is the natural plane. -/
noncomputable def pointLocalBlockModuleModel :
    BlockModuleModel (pointLocal F) (Matrix.SL2.naturalAction F) :=
  SL2Affine.blockModuleModel (pointLocalEquivAffine F)

/-- The actual line-local conjugation quotient is the natural plane. -/
noncomputable def lineLocalBlockModuleModel :
    BlockModuleModel (lineLocal F) (Matrix.SL2.naturalAction F) :=
  SL2Affine.blockModuleModel (lineLocalEquivAffine F)

/-- The module uses exactly the previously specified point-local quotient map. -/
theorem pointLocalBlockModuleModel_quotientIso :
    (pointLocalBlockModuleModel F).quotientIso = pointLocalCoreQuotientEquiv F := rfl

/-- The module uses exactly the previously specified line-local quotient map. -/
theorem lineLocalBlockModuleModel_quotientIso :
    (lineLocalBlockModuleModel F).quotientIso = lineLocalCoreQuotientEquiv F := rfl

theorem pointLocal_block_irreducible : BlockModuleIrreducible (pointLocal F) :=
  SL2Affine.block_irreducible (pointLocalEquivAffine F)

theorem lineLocal_block_irreducible : BlockModuleIrreducible (lineLocal F) :=
  SL2Affine.block_irreducible (lineLocalEquivAffine F)

/-- All five source short-group clauses for the point local. -/
theorem pointLocal_isShort (hcard : 4 ≤ Nat.card F) : IsShort (pointLocal F) :=
  SL2Affine.isShort (pointLocalEquivAffine F) hcard
    (pointLocal_isPerfect F hcard) (pointLocal_generalizedFitting_eq_twoCore F)

/-- All five source short-group clauses for the line local. -/
theorem lineLocal_isShort (hcard : 4 ≤ Nat.card F) : IsShort (lineLocal F) :=
  SL2Affine.isShort (lineLocalEquivAffine F) hcard
    (lineLocal_isPerfect F hcard) (lineLocal_generalizedFitting_eq_twoCore F)

end CharacteristicTwo

variable (F : Type) [Field F] [Finite F]

private theorem charTwo_of_card {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    CharP F 2 := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, show n ≠ 0 by omega])
  exact ringChar.of_eq hc

/-- The concrete point local is an L₂(2ⁿ)-block, with all structural premises proved. -/
theorem pointLocal_isL2EvenBlock {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsL2EvenBlock (pointLocal F) n := by
  let := charTwo_of_card F hF hn
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn)
  exact isL2EvenBlock_of_affine hn hF (pointLocalEquivAffine F)
    (pointLocal_isPerfect F hcard) (pointLocal_generalizedFitting_eq_twoCore F)

/-- The concrete line local is an L₂(2ⁿ)-block, with all structural premises proved. -/
theorem lineLocal_isL2EvenBlock {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsL2EvenBlock (lineLocal F) n := by
  let := charTwo_of_card F hF hn
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn)
  exact isL2EvenBlock_of_affine hn hF (lineLocalEquivAffine F)
    (lineLocal_isPerfect F hcard) (lineLocal_generalizedFitting_eq_twoCore F)

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree
