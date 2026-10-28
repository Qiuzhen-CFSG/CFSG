module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.CheckedPoint

/-!
# The literal cubic action and checked point used by the Borel argument

The residual permutation image in the A₅ marking has order three. Its
nonidentity elements move z, so its kernel is exactly the kernel of
conjugation on V. The first isomorphism theorem transfers the cardinality
to that literal conjugation image. The flag's central checked point is
then compared with the checked subgroup-image convention used by the
Borel construction. `Assembly.source_geometry` consumes both comparisons.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the marking before 13.6.5, printed p.926, and 13.6.18, p.931.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
open ComponentSelection A5Module BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- The order-three residual permutation action is exactly conjugation on V. -/
theorem marked_residual_conjugation_kernel (m : Marking L V)
    (hLV : Lv L (markedV m) ≤ normalizer (V : Set G)) :
    (conjugationAction V (Lv L (markedV m)) hLV).ker = (residualAction m).ker := by
  rw [conjugationAction_ker]
  ext l
  change ((l : G) ∈ centralizer (V : Set G)) ↔ residualAction m l = 1
  constructor
  · intro hl
    have he := m.equivariant (inclusion (residual_le_L m) l) z
    have hc : MulAut.conj (l : G) (markedZ m) = markedZ m :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hl _ (map_mem m _)).symm
    have hz : act (residualAction m l) z = z := by
      apply Multiplicative.ofAdd.injective
      apply m.injective
      exact he.symm.trans hc
    rcases ResidualCoordinates.cubic_cases _ (residualAction_mem_cubic m l) with
      h | h | h
    · exact h
    · rw [h] at hz
      exact (by decide +kernel : act cubic z ≠ z) hz |>.elim
    · rw [h] at hz
      exact (by decide +kernel : act (cubic ^ 2) z ≠ z) hz |>.elim
  · intro hl x hx
    obtain ⟨w, rfl⟩ := m.range_eq.ge hx
    have he := m.equivariant (inclusion (residual_le_L m) l) w.toAdd
    change MulAut.conj (l : G) (m.map w) =
      m.map (Multiplicative.ofAdd (act (residualAction m l) w.toAdd)) at he
    rw [hl] at he
    simp only [act, Subgroup.coe_one, map_one, Module.End.one_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

variable [Finite G]
/-- This supplies the cubic-cardinality premise of the degree bound directly
from the actual A₅ marking, without an additional action-image assumption. -/
theorem marked_residual_conjugation_card (m : Marking L V)
    (hLV : Lv L (markedV m) ≤ normalizer (V : Set G)) :
    Nat.card (conjugationAction V (Lv L (markedV m)) hLV).range = 3 := by
  let f := conjugationAction V (Lv L (markedV m)) hLV
  let g := residualAction m
  let e := (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (marked_residual_conjugation_kernel m hLV)).trans
      (QuotientGroup.quotientKerEquivRange g))
  rw [Nat.card_congr e.toEquiv, residualAction_range]
  exact ResidualCoordinates.cubicGroup_card

omit [Finite G] in
/-- The flag's checked central point is central in the same checked subgroup
image used by the Borel geometry, with the two literal quotient maps compared. -/
theorem marked_checked_central {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) :
    checkedQuotientMap (markedV d.module) (inclusion inf_le_right d.checkedPoint) ∈
      centralizer (checkedImage (markedV d.module)
        (Tv (T : Subgroup G) (markedV d.module)) : Set (Gcheck (markedV d.module))) := by
  rintro _ ⟨t, ht, rfl⟩
  have h := mem_center_iff.mp d.checkedPoint_central
    ((checkedSylowMap (T : Subgroup G) (markedV d.module)).rangeRestrict ⟨t, ht⟩)
  exact congrArg Subtype.val h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
