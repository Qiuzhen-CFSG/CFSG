module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeQuotientOrbitChecks

/-!
# A lower bound for the row-seven quotient conjugacy class

The certified conjugation tree realizes 1155 distinct conjugates of the
literal image `q (lift 3)` in the twelve-dimensional max2 quotient.
Sorted codes give the injection into its actual conjugacy class. Together
with the existing quotient upper bound this determines the class size.

Source: the native max2 census and Kleidman--Wilson (1988), Table 1, p.487.
No ambient matrix-group conjugacy or unproved centralizer generation is used.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeQuotientOrbit
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.QuotientCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData LowerBound
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
attribute [local irreducible] modelGroup matrixA matrixB

theorem realized (i : Fin 1155) :
    ∃ u : Q, IsConj (q (lift 3)) u ∧ u.val.val = decode (orbitCode i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rcases edges_checked i with rfl | ⟨hlt, hleft, hright⟩
    · refine ⟨q (lift 3), IsConj.refl _, ?_⟩
      rw [← element_marked 3, element_val, root_checked]
    · obtain ⟨u, hc, hu⟩ := ih (parent i) hlt
      let g : Q := basic (letter i)
      have he : u.val.val * g.val.val = g.val.val * decode (orbitCode i) := by
        rw [hu, show g.val.val = decode (generatorCode (letter i)) from generators_checked _]
        exact (mulCheck_sound hleft).trans (mulCheck_sound hright).symm
      refine ⟨g⁻¹ * u * g, hc.trans (isConj_iff.mpr ⟨g⁻¹, by simp only [inv_inv]⟩), ?_⟩
      change (g⁻¹).val.val * u.val.val * g.val.val = _
      rw [mul_assoc, he, ← mul_assoc]
      have hinv : (g⁻¹).val.val * g.val.val = 1 :=
        congrArg (fun x : Q => x.val.val) (inv_mul_cancel g)
      rw [hinv, one_mul]

def table (i : Fin 1155) : Q := (realized i).choose

theorem table_val (i : Fin 1155) : (table i).val.val = decode (orbitCode i) :=
  (realized i).choose_spec.2

theorem table_isConj (i : Fin 1155) : IsConj (q (lift 3)) (table i) :=
  (realized i).choose_spec.1

/-- The actual third quotient involution has at least 1155 conjugates. -/
theorem quotient_class_lower : 1155 ≤ Nat.card (quotientClass (q (lift 3))) := by
  have hi : Function.Injective (fun i => table (sorted i)) :=
    table_injective _ (fun i => orbitCode (sorted i)) (fun i => table_val _) sorted_checked
  let f : Fin 1155 → quotientClass (q (lift 3)) :=
    fun i => ⟨table (sorted i), table_isConj _⟩
  have hf : Function.Injective f := fun _ _ he => hi (congrArg Subtype.val he)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeQuotientOrbit
