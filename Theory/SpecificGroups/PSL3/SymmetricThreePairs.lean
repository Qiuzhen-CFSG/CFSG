module

public import Theory.SpecificGroups.PSL2.SymmetricThreePairs
public import Theory.SpecificGroups.PSL3Even.ResidualComparison
public import Theory.SpecificGroups.SL3.InvolutionBlock

/-!
# Conjugate involution pairs force the binary field in PSL₃

The determinant-one two-by-two block embeds injectively in the genuine
projective quotient: its fixed third coordinate kills any scalar kernel.
Every projective involution is conjugate to a root involution in this block.
Restricting the actual pair condition to the block invokes the rank-one
matrix obstruction, forcing the field to have at most two elements.

Source: Aschbacher–Smith, 13.5.21, printed p.924. No assumption on the
center of the covering SL₃, nor on root marking, enters this argument.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry
namespace Theory.PSL3
variable (F : Type*) [Field F]
private def rootBlock : SL(2,F) →* PSL(3,F) :=
  (Matrix.PSL3.projection F).comp ((SL3.blockEmbedding F).comp Matrix.SpecialLinearGroup.toGL)

private theorem rootBlock_injective : Function.Injective (rootBlock F) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro x hx
  have hc : ((SL3.blockEmbedding F).comp Matrix.SpecialLinearGroup.toGL) x ∈
      center SL(3,F) := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr1 : r = 1 := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 2 2) hr
    change (Matrix.scalar (Fin 3) r) 2 2 =
      (SL3.blockMatrix F (Matrix.SpecialLinearGroup.toGL x)) 2 2 at hh
    simpa [SL3.blockMatrix] using hh
  have hb : ((SL3.blockEmbedding F).comp Matrix.SpecialLinearGroup.toGL) x = 1 := by
    apply Subtype.ext
    simpa [hr1] using hr.symm
  exact ((SL3.blockEmbedding_injective F).comp Matrix.SpecialLinearGroup.toGL_injective)
    (hb.trans (map_one ((SL3.blockEmbedding F).comp Matrix.SpecialLinearGroup.toGL)).symm)

open Theory.GroupTheory BenderSuzuki.Converse

theorem field_card_le_two_of_involution_pairs [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (v : PSL(3,F)) (hv : orderOf v = 2) (h : SymmetricThreePairs v) :
    Nat.card F ≤ 2 := by
  let b := rootBlock F (uni 1)
  have hu : orderOf (uni (1 : F)) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]
    · intro he
      have hh := congrArg (fun a : SL2 F => a.val 0 1) he
      simp at hh
  have hb : orderOf b = 2 :=
    (orderOf_injective (rootBlock F) (rootBlock_injective F) _).trans hu
  have hconj : IsConj v b :=
    (Matrix.PSL3Even.ResidualComparison.involution_isConj_root_of_pos F hn hF v
      (orderOf_eq_prime_iff.mp hv).2 (orderOf_eq_prime_iff.mp hv).1).trans
    (Matrix.PSL3Even.ResidualComparison.involution_isConj_root_of_pos F hn hF b
      (orderOf_eq_prime_iff.mp hb).2 (orderOf_eq_prime_iff.mp hb).1).symm
  exact Theory.PSL2.field_card_le_two_of_root_pairs one_ne_zero
    ((h.of_isConj hconj).of_injective (rootBlock F) (rootBlock_injective F))

end Theory.PSL3
