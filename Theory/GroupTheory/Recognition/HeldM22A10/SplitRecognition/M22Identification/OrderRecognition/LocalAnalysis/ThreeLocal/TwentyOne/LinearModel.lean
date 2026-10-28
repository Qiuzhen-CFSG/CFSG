module

public import Theory.AtlasPort.ExceptionalIsomorphisms.SingerEightAction

/-!
# A nonabelian subgroup of order twenty-one in GL₃(2)

The normalizer of the explicit Singer subgroup has order twenty-one by the
existing Sylow-seven count for the simple group SL₃(2). The Frobenius matrix
conjugates its generator to its square, and the two matrices do not commute.
The inclusion SL₃(2) → GL₃(2) transports this actual subgroup injectively.

This supplies the odd model subgroup used after the normalizer enlargement
in Janko, *A characterization of the Mathieu simple groups, I*, J. Algebra 9
(1968), Section 4, p.8, Lemma 9. The Singer matrices and the order/simplicity
proofs come from the attributed ATLAS ports imported above; this module uses
their existing theorems without adding model certification assumptions.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open Atlas.Comparisons.Exceptional
open SingerEight

private def frobenius : G := ⟨!![1,0,0; 0,0,1; 0,1,1], by decide +kernel⟩

private theorem frobenius_relation : frobenius * U = U ^ 2 * frobenius := by
  decide +kernel

private theorem frobenius_noncomm : frobenius * U ≠ U * frobenius := by
  decide +kernel

private theorem frobenius_normalizes :
    frobenius ∈ normalizer (subgroup 7 : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (zpowers U).map (MulAut.conj frobenius).toMonoidHom = zpowers U
  rw [MonoidHom.map_zpowers]
  change zpowers (MulAut.conj frobenius U) = zpowers U
  have he : MulAut.conj frobenius U = U ^ 2 := by
    change frobenius * U * frobenius⁻¹ = U ^ 2
    rw [frobenius_relation, mul_inv_cancel_right]
  rw [he]
  apply le_antisymm
  · exact zpowers_le.mpr (npow_mem_zpowers _ _)
  · apply zpowers_le.mpr
    rw [mem_zpowers_pow_iff, U, singer_order]
    decide

/-- The binary linear group contains an actual nonabelian subgroup of order twenty-one. -/
public theorem linear_nonabelian_twenty_one :
    ∃ A : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)),
      Nat.card A = 21 ∧ ∃ x y : A, x * y ≠ y * x := by
  let N := normalizer (subgroup 7 : Set G)
  let := sl3Two_simple
  have hN : Nat.card N = 21 :=
    Atlas.GroupTheory.simple_order_168_sylow_seven_normalizer_card sl3Two_card (sylow 7)
  let f : G →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) := Matrix.SpecialLinearGroup.toGL
  let x : N := ⟨frobenius, frobenius_normalizes⟩
  let y : N := ⟨U, (subgroup 7).le_normalizer (mem_zpowers U)⟩
  refine ⟨N.map f, ?_, ⟨f x, mem_map_of_mem f x.property⟩,
    ⟨f y, mem_map_of_mem f y.property⟩, ?_⟩
  · rw [card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective, hN]
  · intro he
    apply frobenius_noncomm
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hh := congrArg Subtype.val he
    change f (frobenius * U) = f (U * frobenius)
    simpa only [Subgroup.coe_mul, map_mul] using hh

end Theory.GroupTheory.HeldM22A10.M22Identification
