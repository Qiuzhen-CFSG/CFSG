module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Bounds
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedWitness.Duads
import all CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedWitness.Duads
/-!
# Separation of literal duad vectors

The bijective binary coordinates detect equality of pair labels. Native
M₂₄ two-transitivity moves a given duad to the marked pair, where a small
kernel-checked table certificate recovers its unordered endpoints.

The internal import of `SeedWitness.Duads` exposes the coordinate definition
only within this comparison proof. Its public interface and the actual
quotient action remain unchanged.

Source: the ATLAS pair-label certificates in `Image.StarData`; the local
E₂¹¹.M₂₄ action of GLS3 Table 5.3i, used in Aschbacher–Smith A.3.12(17).
-/

set_option maxRecDepth 10000
public section
open Subgroup
open Janko4 Janko4.Cardinality Janko4.Cardinality.QuotientCount.Image
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.OctadCenter
open AmbientGeometry.SeedDuads StarOrderCertificate
attribute [local irreducible] Janko4.modelGroup max1Subgroup


private theorem pairLabel_one_endpoints : ∀ k l : Fin 24,
    pairLabel k l = 1 → (k = 0 ∧ l = 1) ∨ (k = 1 ∧ l = 0) := by
  decide +kernel


private theorem duad_mask_eq {i j k l : Fin 24}
    (h : duad i j = duad k l) :
    pairLabel (relabel.symm i) (relabel.symm j) =
      pairLabel (relabel.symm k) (relabel.symm l) := by
  have hb := coordinates_injective matrixA_mul_self matrixB_pow_four
    (show coordinates matrixA_mul_self matrixB_pow_four
        (fun b => (pairLabel (relabel.symm i) (relabel.symm j)).testBit b.val) =
      coordinates matrixA_mul_self matrixB_pow_four
        (fun b => (pairLabel (relabel.symm k) (relabel.symm l)).testBit b.val) from
      Subtype.ext h)
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hlt : b < 11
  · exact congrFun hb ⟨b, hlt⟩
  · have hp : 2048 ≤ 2 ^ b := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 11 ≤ b)
    rw [Nat.testBit_lt_two_pow ((pairLabel_lt _ _).trans_le hp),
      Nat.testBit_lt_two_pow ((pairLabel_lt _ _).trans_le hp)]


/-- Equality of nonzero duad vectors remembers exactly the unordered endpoints. -/
theorem duad_endpoints {i j k l : Fin 24} (hij : i ≠ j)
    (h : duad i j = duad k l) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  let : MulAction.IsMultiplyPretransitive Sporadic.Mathieu.M24 (Fin 24) 5 :=
    Sporadic.Mathieu.m24_isFivePretransitive
  have ht : MulAction.IsMultiplyPretransitive Sporadic.Mathieu.M24 (Fin 24) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 5) (by decide) (by simp)
  obtain ⟨g, hi, hj⟩ := MulAction.is_two_pretransitive_iff.mp ht hij
    (relabel.injective.ne (by decide : (0 : Fin 24) ≠ 1))
  obtain ⟨x, hx⟩ := literalMathieuMap_surjective g
  have he := congrArg (fun z => x * z * x⁻¹) h
  rw [conjugate_duad, conjugate_duad, hx, hi, hj] at he
  have hl := duad_mask_eq he
  simp only [Equiv.symm_apply_apply] at hl
  rcases pairLabel_one_endpoints _ _ hl.symm with he | he
  · left
    constructor
    · apply MulAction.injective g
      apply relabel.symm.injective
      simpa only [hi, Equiv.symm_apply_apply] using he.1.symm
    · apply MulAction.injective g
      apply relabel.symm.injective
      simpa only [hj, Equiv.symm_apply_apply] using he.2.symm
  · right
    constructor
    · apply MulAction.injective g
      apply relabel.symm.injective
      simpa only [hi, Equiv.symm_apply_apply] using he.2.symm
    · apply MulAction.injective g
      apply relabel.symm.injective
      simpa only [hj, Equiv.symm_apply_apply] using he.1.symm

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.OctadCenter
