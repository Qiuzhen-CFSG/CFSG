module

public import Theory.GroupTheory.OrderNineAutomorphisms
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The affine branch in degree nine

A nontrivial abelian normal subgroup in a faithful primitive action is
transitive, hence regular. In degree nine it therefore has order nine.
The conjugation map has kernel contained in this subgroup, and its image
lies in the solvable automorphism group proved in `OrderNineAutomorphisms`.
Thus every such primitive group is solvable.

This closes the abelian-normal branch of the primitive A₉ calculation for
Aschbacher–Smith, Theorem 0.1.2(3), condition K, printed pp.4 and 482.
Existence and identification of a nonabelian simple normal subgroup in the
remaining branch are separate obligations; no primitive list is assumed.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

open MulAction
open scoped IsMulCommutative

variable {H : Type*} [Group H] [MulAction H (Fin 9)] [FaithfulSMul H (Fin 9)]

private theorem abelian_normal_card_nine [IsPreprimitive H (Fin 9)]
    (N : Subgroup H) [N.Normal] [IsMulCommutative N] (hN : N ≠ ⊥) :
    Nat.card N = 9 := by
  let : IsPretransitive N (Fin 9) := Atlas.GroupTheory.normal_pretransitive N hN
  have hi : Function.Injective (fun n : N => n • (0 : Fin 9)) := by
    intro n m he
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin 9)
    intro x
    obtain ⟨k, rfl⟩ := exists_smul_eq N (0 : Fin 9) x
    change n • (0 : Fin 9) = m • (0 : Fin 9) at he
    calc
      n • (k • (0 : Fin 9)) = k • (n • (0 : Fin 9)) := by
        rw [← mul_smul, mul_comm n k, mul_smul]
      _ = k • (m • (0 : Fin 9)) := by rw [he]
      _ = m • (k • (0 : Fin 9)) := by rw [← mul_smul, mul_comm k m, mul_smul]
  have hs : Function.Surjective (fun n : N => n • (0 : Fin 9)) :=
    fun x => exists_smul_eq N 0 x
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hi,hs⟩)).trans (Nat.card_fin 9)

private theorem conjNormal_ker_le_of_abelian_transitive
    (N : Subgroup H) [N.Normal] [IsMulCommutative N] [IsPretransitive N (Fin 9)] :
    (MulAut.conjNormal : H →* MulAut N).ker ≤ N := by
  intro g hg
  obtain ⟨n, hn⟩ := exists_smul_eq N (0 : Fin 9) (g • (0 : Fin 9))
  have he : g = (n : H) := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin 9)
    intro x
    obtain ⟨m, rfl⟩ := exists_smul_eq N (0 : Fin 9) x
    have hcomm : g * (m : H) = (m : H) * g := by
      have h := congrArg (fun a : MulAut N => ((a m : N) : H)) hg
      change g * (m : H) * g⁻¹ = (m : H) at h
      exact mul_inv_eq_iff_eq_mul.mp h
    calc
      g • (m • (0 : Fin 9)) = (g * (m : H)) • (0 : Fin 9) := (mul_smul _ _ _).symm
      _ = ((m : H) * g) • (0 : Fin 9) := by rw [hcomm]
      _ = m • (g • (0 : Fin 9)) := mul_smul _ _ _
      _ = m • (n • (0 : Fin 9)) := by rw [hn]
      _ = n • (m • (0 : Fin 9)) := by rw [← mul_smul, mul_comm m n, mul_smul]
  exact he ▸ n.property

/-- A faithful primitive group of degree nine with a nontrivial abelian normal subgroup is solvable. -/
public theorem solvable_of_abelian_normal
    (hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsMulCommutative N] (hN : N ≠ ⊥) :
    Group.IsSolvable H := by
  let := hp
  have hcard := abelian_normal_card_nine N hN
  let : Finite N := Nat.finite_of_card_ne_zero (by omega)
  let : IsPretransitive N (Fin 9) := Atlas.GroupTheory.normal_pretransitive N hN
  let : Group.IsSolvable (MulAut N) := MulAut.isSolvable_of_card_nine hcard
  exact Group.isSolvable_of_ker_le_range N.subtype MulAut.conjNormal
    (by simpa only [Subgroup.range_subtype] using conjNormal_ker_le_of_abelian_transitive N)

end CFSG.Quasithin.MainConverse.NineReduction
