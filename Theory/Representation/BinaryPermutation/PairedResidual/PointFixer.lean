module
public import Theory.Representation.BinaryPermutation.PairedResidual

/-!
# Fixed vectors of a relabeled paired A₄

Conjugating the paired residual transports its unique nonzero fixed vector
to the corresponding six-support vector. Its stabilizer is exactly the
permutations fixing the remaining letter. Both statements retain the
original relabeling permutation.

Source: Aschbacher--Smith §B.3, used in 15.1.25(5), printed p.1102.
-/

public section
open Subgroup
namespace AlternatingSeven.ThreeResidualLocals
open BinaryPermutation BinaryPermutation.SevenParabolic.Ordinary

theorem conjugate_pairedFour_fixed (c : Perm7) (v : core (Fin 7))
    (hv : ∀ g ∈ pairedFour.map (MulAut.conj c).toMonoidHom,
      coreRepresentation (Fin 7) g v = v) :
    v = 0 ∨ v = coreRepresentation (Fin 7) c firstSix := by
  let ρ := coreRepresentation (Fin 7)
  let w := ρ c⁻¹ v
  have hw : ∀ g ∈ pairedFour, ρ g w = w := by
    intro g hg
    have hcg := hv _ (mem_map_of_mem (MulAut.conj c).toMonoidHom hg)
    change ρ (c * g * c⁻¹) v = v at hcg
    calc
      ρ g w = ρ (g * c⁻¹) v := by rw [map_mul,Module.End.mul_apply]
      _ = ρ (c⁻¹ * (c*g*c⁻¹)) v := by congr 2; group
      _ = ρ c⁻¹ (ρ (c*g*c⁻¹) v) := by rw [map_mul,Module.End.mul_apply]
      _ = w := by rw [hcg]
  have hcw : ρ c w = v := by
    change ρ c (ρ c⁻¹ v) = v
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  rcases pairedFour_fixed w hw with he | he
  · exact Or.inl (hcw.symm.trans (by rw [he,map_zero]))
  · exact Or.inr (hcw.symm.trans (by rw [he]))

theorem conjugate_six_fixed_iff (c g : Perm7) :
    coreRepresentation (Fin 7) g (coreRepresentation (Fin 7) c firstSix) =
      coreRepresentation (Fin 7) c firstSix ↔ g (c 6) = c 6 := by
  let ρ := coreRepresentation (Fin 7)
  have he : ρ g (ρ c firstSix) = ρ c firstSix ↔
      ρ (c⁻¹*g*c) firstSix = firstSix := by
    rw [← ((ρ.apply_bijective c⁻¹).injective).eq_iff]
    simp only [←Module.End.mul_apply,←map_mul]
    rw [inv_mul_cancel,map_one,Module.End.one_apply,mul_assoc]
  rw [he]
  change SevenParabolic.action (c⁻¹*g*c) firstSix = firstSix ↔ _
  rw [action_firstSix]
  change c.symm (g (c 6)) = 6 ↔ _
  rw [Equiv.symm_apply_eq]

end AlternatingSeven.ThreeResidualLocals
